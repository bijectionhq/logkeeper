use std::{collections::BTreeSet, time::Duration};

use journal_contract::JournalError;
use openraft::{ServerState, async_runtime::WatchReceiver};
use tokio::time::{Instant, timeout, timeout_at};
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

use super::{Engine, Group, NodeId, Outcome, Reply, Request, failure, invalid, leader_reply};
use crate::stream::consensus::{LogId, Stage, Vote, network::Frame, state::Command};

pub(super) const MANAGEMENT_TIMEOUT: Duration = Duration::from_secs(30);

impl Engine {
    pub(super) async fn replace(
        &self,
        group: &Group,
        expected: u64,
        voters: [Uuid; 3],
    ) -> std::io::Result<Reply> {
        let Ok(_guard) = group.membership.try_lock() else {
            return Ok(failure(JournalError::Unavailable));
        };
        let deadline = Instant::now() + MANAGEMENT_TIMEOUT;
        if let Err(reply) = group.barrier(deadline).await {
            return Ok(reply);
        }
        let (head, configuration, previous_revision, membership) = match group.state.placement() {
            Ok(placement) => placement,
            Err(error) => return Ok(failure(error)),
        };
        let joint = membership.membership().get_joint_config();
        let conflict = || failure(JournalError::Conflict { head });
        if !self.placement.roster(&voters) {
            return Ok(conflict());
        }
        if previous_revision == Some(expected) && configuration.voters == voters {
            return Ok(Reply::Decision(Outcome::Configuration(configuration)));
        }
        if configuration.revision != expected {
            return Ok(conflict());
        }
        let target = voters
            .into_iter()
            .map(|id| id.as_u128())
            .collect::<BTreeSet<_>>();
        let _write_fence = match joint.as_slice() {
            [current] if *current == target => {
                return Ok(Reply::Decision(Outcome::Configuration(configuration)));
            }
            [_] => {
                let vote = {
                    let metrics = group.raft.metrics();
                    let current = metrics.borrow_watched();
                    if current.state != ServerState::Leader {
                        return Ok(leader_reply(current.current_leader));
                    }
                    current.vote
                };
                let stage = Stage {
                    stream: group.genesis.stream,
                    source: expected,
                    old: configuration.voters,
                    target: voters,
                };
                if !group.state.staged(&stage) {
                    match self.catalog_request(Request::Stage(stage.clone())).await? {
                        Reply::Staged(receipt) if receipt == stage => (),
                        _ => return Ok(failure(JournalError::Unavailable)),
                    }
                }
                if !group.state.staged_intent(&stage) {
                    match group.write(Command::StageOwned(stage.clone())).await {
                        Reply::Decision(Outcome::Unit) => (),
                        reply => return Ok(reply),
                    }
                }
                let mut catch_up = *membership.log_id();
                let new_voters = self
                    .nodes(voters)
                    .into_iter()
                    .filter(|(id, _)| !joint[0].contains(id));
                let mut learners = Vec::new();
                let mut handles = Vec::new();
                for (id, node) in new_voters {
                    let keeper = Uuid::from_u128(id);
                    let Reply::Generation(generation) = self
                        .rpc
                        .call(
                            keeper,
                            Frame::Client(Request::StageReplica {
                                genesis: group.genesis.clone(),
                                stage: stage.clone(),
                            }),
                            deadline.saturating_duration_since(Instant::now()),
                        )
                        .await?
                    else {
                        return Ok(failure(JournalError::Unavailable));
                    };
                    handles.push((keeper, generation));
                    if membership.membership().get_node(&id).is_none() {
                        match timeout_at(deadline, group.raft.add_learner(id, node, false)).await {
                            Ok(Ok(response)) => catch_up = Some(response.log_id),
                            Ok(Err(error)) => {
                                return Ok(leader_reply(
                                    error
                                        .forward_to_leader()
                                        .and_then(|leader| leader.leader_id),
                                ));
                            }
                            Err(_) => return Ok(failure(JournalError::Unavailable)),
                        }
                    }
                    learners.push(id);
                }
                if let Some(catch_up) = catch_up {
                    group
                        .wait_for_learners(vote, &learners, catch_up, deadline)
                        .await?;
                }
                // Let application traffic continue during the initial copy.
                // Fence new proposals and drain old ones before sampling the
                // entire issued prefix that will precede the joint entry.
                let Ok(Ok(fence)) = timeout_at(
                    deadline,
                    group
                        .writes
                        .clone()
                        .acquire_many_owned(super::MAX_PENDING_WRITES as u32),
                )
                .await
                else {
                    return Ok(failure(JournalError::Unavailable));
                };
                let through = group
                    .state
                    .durable_tip()
                    .ok_or_else(|| invalid("leader lacks a durable log"))?;
                group
                    .wait_for_learners(vote, &learners, through, deadline)
                    .await?;
                for (keeper, generation) in handles {
                    let Reply::Decision(Outcome::Unit) = self
                        .rpc
                        .call(
                            keeper,
                            Frame::Client(Request::InstallReplica {
                                genesis: group.genesis.clone(),
                                stage: stage.clone(),
                                generation,
                                through,
                            }),
                            deadline.saturating_duration_since(Instant::now()),
                        )
                        .await?
                    else {
                        return Ok(failure(JournalError::Unavailable));
                    };
                }
                Some(fence)
            }
            [_, pending] if *pending == target => None,
            _ => return Ok(conflict()),
        };
        Ok(
            match timeout_at(deadline, group.raft.change_membership(target, false)).await {
                Ok(Ok(_)) => Reply::Decision(
                    group
                        .state
                        .placement()
                        .map(|(_, current, _, _)| Outcome::Configuration(current))
                        .into(),
                ),
                Ok(Err(error)) => leader_reply(
                    error
                        .forward_to_leader()
                        .and_then(|leader| leader.leader_id),
                ),
                Err(_) => failure(JournalError::Unavailable),
            },
        )
    }
}

impl Group {
    async fn wait_for_learners(
        &self,
        vote: Vote,
        learners: &[NodeId],
        through: LogId,
        deadline: Instant,
    ) -> std::io::Result<()> {
        let mut metrics = self.raft.metrics();
        // A replication match covers the learner's durable log or installed snapshot.
        // Matching a later log ID in this ballot also covers this exact prefix.
        let observed = timeout_at(deadline, async {
            loop {
                {
                    let metrics = metrics.borrow_and_update();
                    if metrics.vote != vote
                        || metrics.state != ServerState::Leader
                        || metrics.replication.as_ref().is_some_and(|matched| {
                            learners.iter().all(|id| {
                                matched.get(id).copied().flatten().is_some_and(|mark| {
                                    mark.index > through.index || mark == through
                                })
                            })
                        })
                    {
                        return Ok::<_, std::io::Error>(metrics.clone());
                    }
                }
                metrics.changed().await.map_err(std::io::Error::other)?;
            }
        })
        .await??;
        if observed.vote == vote && observed.state == ServerState::Leader {
            Ok(())
        } else {
            Err(invalid("leadership changed while staging learners"))
        }
    }

    pub(super) async fn configuration(&self) -> Reply {
        if let Err(reply) = self.barrier(Instant::now() + super::REQUEST_TIMEOUT).await {
            return reply;
        }
        Reply::Decision(
            self.state
                .placement()
                .map(|(_, current, _, _)| Outcome::Configuration(current))
                .into(),
        )
    }

    pub(super) async fn resume_membership(&self, id: NodeId, stop: CancellationToken) {
        let mut metrics = self.raft.server_metrics();
        let mut retry = tokio::time::interval(Duration::from_millis(500));
        retry.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                _ = stop.cancelled() => return,
                _ = retry.tick() => {
                    if self.state.healthy() && self.state.suffix_len() >= super::MAX_LOG_SUFFIX as usize {
                        self.request_covered_purge().await;
                    }
                },
                result = metrics.changed() => if result.is_err() { return; },
            }
            let is_leader = {
                let current = metrics.borrow_watched();
                current.state == ServerState::Leader && current.current_leader == Some(id)
            };
            if !is_leader {
                continue;
            }
            let Ok(_guard) = self.membership.try_lock() else {
                continue;
            };
            let membership = self.state.membership();
            if let [_, target] = membership.membership().get_joint_config().as_slice() {
                tokio::select! {
                    _ = stop.cancelled() => return,
                    _ = timeout(MANAGEMENT_TIMEOUT, self.raft.change_membership(target.clone(), false)) => (),
                }
            }
        }
    }
}
