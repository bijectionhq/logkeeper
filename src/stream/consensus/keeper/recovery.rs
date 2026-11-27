//! Operator recovery of a stream that lost two of its three voters.
//!
//! `logkeeper keeper recover-stream` runs on the stopped survivor's data
//! directory under its media lock. It replays the survivor's whole log,
//! asks every other keeper for its status, and refuses unless the operator
//! acknowledges the data loss, names the two lost voters, and neither of
//! them answers with a healthy replica. A lost voter that does not answer is
//! asked again for longer before it counts as lost: a slow keeper is not a
//! lost one. Naming the lost voters is the operator's statement that they
//! are down or fenced, which no probe can prove. It then stages an installed
//! empty copy on each of two replacements, stages the move in the catalog,
//! which fences the lost configuration, and writes one WAL round on the
//! survivor: a vote for itself in a term above every term it has seen, and
//! two entries in that term. The first,
//! `Command::Recover`, stages the move and fences the stream under the
//! recovery writer at an epoch above every applied epoch. The second is the
//! membership of the survivor and the two replacements. When the survivor
//! starts, its replacements elect it with their empty logs, and it
//! replicates its log, which commits the recovery.

use std::{collections::BTreeMap, io, time::Duration};

use journal_contract::{Epoch, Lsn, StreamId};
use openraft::{BasicNode, EntryPayload};
use tokio::time::{Instant, timeout};
use uuid::Uuid;

use super::{Config, Reply, Request, catalog_stream, failure};
use crate::stream::{
    consensus::{
        Entry, LogId, Stage, Vote, assignment,
        catalog::{self, Catalog},
        decisions, invalid,
        network::{Lane, Rpc},
        placement::Placement,
        state::{Command, Outcome},
        storage::{self, Disk, Record},
    },
    wire::KeeperId,
};

const STATUS_TIMEOUT: Duration = Duration::from_secs(2);
/// Further status requests to a lost voter that did not answer the first,
/// each given `LOST_STATUS_TIMEOUT`, with `LOST_STATUS_PAUSE` between them.
const LOST_STATUS_ROUNDS: u32 = 2;
const LOST_STATUS_TIMEOUT: Duration = Duration::from_secs(5);
const LOST_STATUS_PAUSE: Duration = Duration::from_secs(1);
const STAGING_TIMEOUT: Duration = Duration::from_secs(10);

/// What the operator asked of a recovery.
#[derive(Clone, Debug, Default)]
pub struct Recovery {
    /// The operator accepts that acknowledged records only the lost voters
    /// held are gone.
    pub acknowledge_data_loss: bool,
    /// The two voters the operator found down or fenced. They must be the
    /// survivor's configuration's other two voters.
    pub lost: Option<[Uuid; 2]>,
    /// The two replacement keepers. Without them the best-ranked live,
    /// accepting keepers in free failure domains are chosen.
    pub with: Option<[Uuid; 2]>,
    /// Fails the durable WAL round: 2 before its boundary, 3 after it.
    #[cfg(test)]
    pub(super) interrupt: Option<u8>,
}

/// What a recovery did, or found already done.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryReport {
    pub stream: StreamId,
    pub lost: [Uuid; 2],
    pub voters: [Uuid; 3],
    pub revision: u64,
    pub head: Lsn,
    pub epoch: Epoch,
    pub term: u64,
    /// False when an earlier run already wrote this recovery.
    pub written: bool,
}

impl std::fmt::Display for RecoveryReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "stream {:032x} {} from this keeper at head {}: voters {} {} {}, revision {}, \
             term {}, recovery fence at epoch {}. Lost voters {} and {} must retire their \
             copies before they rejoin. Start this keeper, then acknowledge the recovery \
             so writers can seal again.",
            self.stream.0,
            if self.written {
                "recovered"
            } else {
                "was already recovered"
            },
            self.head.0,
            self.voters[0],
            self.voters[1],
            self.voters[2],
            self.revision,
            self.term,
            self.epoch.0,
            self.lost[0],
            self.lost[1],
        )
    }
}

impl Config {
    /// Recovers `stream` on this stopped keeper from its local replica, as
    /// the module documentation describes.
    pub async fn recover_stream(
        &self,
        stream: StreamId,
        recovery: Recovery,
    ) -> io::Result<RecoveryReport> {
        let placement = self.validate()?;
        let keeper = KeeperId(self.keeper.as_u128());
        let rpc = Rpc::new(
            self.tls.peer_protocols(keeper, Lane::Application.alpns())?,
            self.keepers.clone(),
            Lane::Application,
        );
        if stream == catalog_stream::STREAM {
            return Err(invalid(
                "the replicated catalog cannot be recovered this way",
            ));
        }
        let enrollment = self.enrollment()?;
        let disk = tokio::task::spawn_blocking(move || Disk::open(enrollment)).await??;
        let result = self
            .recover_on(&disk, &rpc, &placement, stream, recovery)
            .await;
        let shutdown = disk.shutdown().await;
        match result {
            Ok(recovered) => shutdown.map(|()| recovered),
            Err(error) => Err(error),
        }
    }

    async fn recover_on(
        &self,
        disk: &Disk,
        rpc: &Rpc,
        placement: &Placement,
        stream: StreamId,
        recovery: Recovery,
    ) -> io::Result<RecoveryReport> {
        let genesis = disk
            .genesis(stream)
            .ok_or_else(|| invalid("stream is not installed on this keeper"))?;
        let generation = disk
            .ownership(stream)
            .filter(|book| book.installed())
            .and_then(|book| book.generation())
            .ok_or_else(|| invalid("this keeper holds no installed replica of the stream"))?;
        disk.check_placement(stream, placement)?;
        let replayed = storage::replay(disk, genesis.clone(), placement.clone()).await?;
        let head = replayed
            .head
            .map_err(|error| invalid(format!("the stream cannot be recovered: {error:?}")))?;
        let configuration = replayed
            .configuration
            .filter(|_| replayed.uniform)
            .ok_or_else(|| {
                invalid("the survivor's latest membership is not a finalized configuration")
            })?;
        let point = disk.recovery_point(stream);
        if let Some(done) = point.written {
            let report = RecoveryReport {
                stream,
                lost: lost(&done.old, self.keeper),
                voters: done.target,
                revision: configuration.revision,
                head,
                epoch: replayed.epoch,
                term: point.vote_term,
                written: false,
            };
            crate::stream::consensus::logging::audit_recovery(
                self.keeper,
                stream,
                &report.lost,
                &report.voters,
                report.revision,
                report.head,
                report.epoch,
                report.term,
                report.written,
                "already_written",
            );
            return Ok(report);
        }
        let survivor_votes = configuration.voters.contains(&self.keeper);
        if !survivor_votes {
            return Err(invalid(
                "this keeper is not a voter of the stream's latest configuration",
            ));
        }
        let old = configuration.voters;
        let others = lost(&old, self.keeper);

        let ask = |keeper: Uuid, limit: Duration| async move {
            let status = timeout(
                limit,
                rpc.call_application(keeper, Request::KeeperStatus(stream), limit),
            )
            .await;
            match status {
                Ok(Ok(Reply::Status(status))) if status.keeper == keeper => (keeper, Some(status)),
                _ => (keeper, None),
            }
        };
        let mut statuses = BTreeMap::new();
        // Draining retired keepers still hold replicas, so they are asked too.
        let asked = placement
            .all_domains()
            .keys()
            .copied()
            .filter(|keeper| *keeper != self.keeper)
            .map(|keeper| ask(keeper, STATUS_TIMEOUT));
        statuses.extend(futures::future::join_all(asked).await);
        // A lost voter that missed the first request may only be slow. It
        // counts as lost only after it also misses the longer ones.
        for _ in 0..LOST_STATUS_ROUNDS {
            let silent = others
                .into_iter()
                .filter(|voter| statuses.get(voter).cloned().flatten().is_none())
                .collect::<Vec<_>>();
            if silent.is_empty() {
                break;
            }
            tokio::time::sleep(LOST_STATUS_PAUSE).await;
            let asked = silent
                .into_iter()
                .map(|voter| ask(voter, LOST_STATUS_TIMEOUT));
            for (voter, status) in futures::future::join_all(asked).await {
                if status.is_some() {
                    statuses.insert(voter, status);
                }
            }
        }
        let healthy = others
            .iter()
            .filter(|voter| {
                statuses
                    .get(voter)
                    .and_then(|status| status.as_ref())
                    .is_some_and(|status| status.replica == Some(true))
            })
            .count() as u64;
        if healthy != 0 {
            return Err(invalid(format!(
                "refused: {healthy} other voter(s) of {old:?} answer with a healthy replica, \
                 so the stream still has a quorum; restart this keeper instead"
            )));
        }

        let health = statuses
            .iter()
            .map(|(keeper, status)| {
                (
                    *keeper,
                    assignment::Health {
                        live: status.is_some(),
                        accepting: status.as_ref().is_some_and(|status| status.accepting),
                        streams: status.as_ref().map_or(0, |status| status.streams),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let target = match recovery.with {
            Some(with) => {
                let mut target = [self.keeper, with[0], with[1]];
                target.sort_unstable();
                if with.iter().any(|keeper| {
                    old.contains(keeper)
                        || !statuses
                            .get(keeper)
                            .and_then(|status| status.as_ref())
                            .is_some_and(|status| status.accepting)
                }) || !placement.roster(&target)
                {
                    return Err(invalid(
                        "replacements must be two live, accepting keepers outside the lost \
                         configuration, in failure domains distinct from each other and from \
                         this keeper's",
                    ));
                }
                target
            }
            None => assignment::recovery_roster(
                stream,
                self.keeper,
                old,
                &assignment::View {
                    eligible: placement.domains(),
                    health: &health,
                },
            )
            .ok_or_else(|| {
                invalid("no two live, accepting keepers in free failure domains can replace the lost voters")
            })?,
        };
        let stage = Stage {
            stream,
            source: configuration.revision,
            old,
            target,
        };
        if point.snapshot_ahead {
            return Err(invalid(
                "the selected snapshot is ahead of the log; start and stop this keeper first",
            ));
        }
        let tip = point.tip;
        let term = decisions::recovery_term(point.vote_term, point.log_term)
            .ok_or_else(|| invalid("the stream's term is exhausted"))?;
        let epoch = decisions::recovery_epoch(replayed.epoch.0)
            .map(Epoch)
            .ok_or_else(|| invalid("the stream's epoch is exhausted"))?;
        let named = recovery.lost.is_some_and(|mut lost| {
            lost.sort_unstable();
            lost == others
        });
        if recovery.acknowledge_data_loss && !named {
            return Err(invalid(format!(
                "refused: confirm that {} and {} are down or fenced, then name them with \
                 --lost {},{}",
                others[0], others[1], others[0], others[1],
            )));
        }
        if !decisions::allows_recovery(
            recovery.acknowledge_data_loss && named,
            survivor_votes,
            healthy,
        ) {
            return Err(invalid(format!(
                "refused without --acknowledge-data-loss. This would make this keeper's copy of \
                 stream {:032x} (head {}) the only history: records only {} and {} held are \
                 lost. The voters would become {target:?} at revision {}, term {term}, with \
                 seals refused under a recovery fence at epoch {} until an administrator \
                 acknowledges the recovery. To proceed, confirm that {} and {} are down or \
                 fenced and add --acknowledge-data-loss --lost {},{}",
                stream.0,
                head.0,
                others[0],
                others[1],
                stage.source + 1,
                epoch.0,
                others[0],
                others[1],
                others[0],
                others[1],
            )));
        }

        for replacement in target.into_iter().filter(|id| !old.contains(id)) {
            match rpc
                .call_application(
                    replacement,
                    Request::StageRecovered {
                        genesis: genesis.clone(),
                        stage: stage.clone(),
                    },
                    STAGING_TIMEOUT,
                )
                .await?
            {
                Reply::Generation(_) => (),
                _ => {
                    return Err(invalid(format!(
                        "replacement {replacement} refused the recovered copy"
                    )));
                }
            }
        }

        // The catalog records the move before the survivor writes it. Its
        // latest staged move is what fences the lost configuration: a lost
        // voter that restarts asks for it before it campaigns or serves a
        // read (`keeper/certify.rs`). So the recovery refuses without the
        // catalog. It stages after the replacements, so a refused
        // replacement leaves the old configuration unfenced.
        self.stage_in_catalog(disk, rpc, placement, &stage)
            .await
            .map_err(|error| {
                invalid(format!(
                    "refused: the catalog must record the recovery so the lost voters stay \
                     fenced: {error}"
                ))
            })?;
        let log_id = |index| {
            LogId::new(
                openraft::vote::leader_id_std::CommittedLeaderId::new(term),
                index,
            )
        };
        let next = tip.map_or(0, |tip| tip.index + 1);
        let nodes = target
            .into_iter()
            .map(|id| {
                Ok((
                    id.as_u128(),
                    BasicNode::new(
                        self.keepers
                            .get(&id)
                            .ok_or_else(|| invalid("unknown replacement keeper"))?
                            .to_string(),
                    ),
                ))
            })
            .collect::<io::Result<BTreeMap<_, _>>>()?;
        let membership = openraft::Membership::new(vec![nodes.keys().copied().collect()], nodes)
            .map_err(io::Error::other)?;
        let entries = vec![
            Entry {
                log_id: log_id(next),
                payload: EntryPayload::Normal(Command::Recover(stage.clone())),
            },
            Entry {
                log_id: log_id(next + 1),
                payload: EntryPayload::Membership(membership),
            },
        ];
        #[cfg(test)]
        if let Some(cut) = recovery.interrupt {
            disk.interrupt_next(stream, cut);
        }
        disk.write(Record::Owned(
            generation,
            Box::new(Record::Recover(
                stream,
                Vote::new_committed(term, self.keeper.as_u128()),
                entries,
            )),
        ))
        .await?;
        let report = RecoveryReport {
            stream,
            lost: others,
            voters: target,
            revision: stage.source + 1,
            head,
            epoch,
            term,
            written: true,
        };
        crate::stream::consensus::logging::audit_recovery(
            self.keeper,
            stream,
            &report.lost,
            &report.voters,
            report.revision,
            report.head,
            report.epoch,
            report.term,
            report.written,
            "ok",
        );
        Ok(report)
    }

    async fn stage_in_catalog(
        &self,
        disk: &Disk,
        rpc: &Rpc,
        placement: &Placement,
        stage: &Stage,
    ) -> io::Result<()> {
        let reply = match self.catalog_voters {
            None if self.catalog == self.keeper => {
                Catalog::new(disk.clone())
                    .stage(stage.clone(), placement)
                    .await?
            }
            None => {
                rpc.call_application(self.catalog, Request::Stage(stage.clone()), STAGING_TIMEOUT)
                    .await?
            }
            Some(voters) => {
                // Repair may have replaced every configured voter.
                let order = voters
                    .into_iter()
                    .chain(self.keepers.keys().copied())
                    .filter(|voter| *voter != self.keeper)
                    .collect::<Vec<_>>();
                catalog::ask(&order, Instant::now() + STAGING_TIMEOUT, |voter| {
                    rpc.call_application(voter, Request::Stage(stage.clone()), STATUS_TIMEOUT)
                })
                .await
                .map_or_else(
                    || failure(journal_contract::JournalError::Unavailable),
                    |(_, reply)| reply,
                )
            }
        };
        match reply {
            Reply::Staged(receipt) if receipt == *stage => Ok(()),
            Reply::Decision(Outcome::Refused(error)) => {
                Err(invalid(format!("the catalog refused the stage: {error:?}")))
            }
            _ => Err(invalid("the catalog did not stage the recovery")),
        }
    }
}

/// The two voters of `voters` other than `survivor`.
fn lost(voters: &[Uuid; 3], survivor: Uuid) -> [Uuid; 2] {
    let mut others = voters.iter().copied().filter(|voter| *voter != survivor);
    [
        others.next().unwrap_or_default(),
        others.next().unwrap_or_default(),
    ]
}
