//! Keeper status and leader-driven repair.
//!
//! Each pass considers every stream this keeper leads and queues its repair
//! work in priority order: finish a joint configuration change, remove
//! learners an aborted replacement left, then replace dead or quarantined
//! voters. A voter is dead when it has been silent for the repair delay and
//! its keeper does not answer liveness pings, or answers without a healthy
//! replica. It is replaced by the best-ranked live keeper with room in a
//! free failure domain; nothing moves without two live voters.
//!
//! At most `MAX_REPAIRS` repairs run at once, in their own tasks, so a slow
//! replacement never holds up the pass; their snapshot sends share the
//! keeper-wide pacing. Streams take turns from a rotating cursor, and a
//! stream whose repair is refused or fails waits out an exponential backoff
//! so it cannot starve the others. Keeper health comes from the liveness
//! table, fetched once per ping rather than once per stream; only a silent
//! voter whose keeper still answers is asked about its replica.
//!
//! After the queue, a leader on a full keeper sheds its streams and every
//! leader moves a stream back to the voter in its writer's domain.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use journal_contract::StreamId;
use openraft::{Instant as _, ServerState, async_runtime::WatchReceiver};
use tokio::time::{Instant, timeout};
use uuid::Uuid;

use super::{Engine, Group, NodeId, Reply, Request};
use crate::stream::consensus::{
    KeeperStatus,
    assignment::{self, Health, View},
    decisions,
    network::Frame,
};

#[cfg(not(test))]
const REPAIR_INTERVAL: Duration = Duration::from_secs(30);
#[cfg(test)]
const REPAIR_INTERVAL: Duration = Duration::from_millis(500);
const STATUS_TIMEOUT: Duration = Duration::from_secs(2);
/// A learner that outlives two replacement deadlines belongs to an aborted
/// replacement.
#[cfg(not(test))]
const STALE_LEARNER: Duration = Duration::from_secs(60);
#[cfg(test)]
const STALE_LEARNER: Duration = Duration::from_secs(2);
/// Repairs one keeper runs at once.
pub(super) const MAX_REPAIRS: usize = 4;
/// The longest wait before a stream whose repair keeps failing is tried
/// again.
#[cfg(not(test))]
const MAX_REPAIR_BACKOFF: Duration = Duration::from_secs(600);
#[cfg(test)]
const MAX_REPAIR_BACKOFF: Duration = Duration::from_secs(8);

/// Repairs in flight and the backoff of streams whose repair failed.
#[derive(Default)]
pub(super) struct RepairQueue {
    running: HashSet<StreamId>,
    /// Failed attempts and the earliest next attempt of each stream.
    backoff: HashMap<StreamId, (u32, Instant)>,
    /// The stream the last pass started last; the next pass starts after it.
    cursor: Option<StreamId>,
}

/// One unit of repair work, in priority order.
#[derive(Debug)]
enum Work {
    /// Finish the joint change to this voter set.
    Joint(BTreeSet<NodeId>),
    /// Remove these learners.
    Learners(BTreeSet<NodeId>),
    /// Replace one of these silent voters.
    Voters(Vec<Uuid>),
}

impl Work {
    fn rank(&self) -> u8 {
        match self {
            Self::Joint(_) => 0,
            Self::Learners(_) => 1,
            Self::Voters(_) => 2,
        }
    }
}

impl Engine {
    /// This keeper's status without a replica.
    pub(super) async fn keeper_status(&self) -> KeeperStatus {
        let groups = self.groups.lock().await;
        let led = groups
            .values()
            .filter(|group| group.raft.metrics().borrow_watched().state == ServerState::Leader)
            .count();
        KeeperStatus {
            keeper: self.id,
            accepting: self.disk.responsive() && self.disk.space.accepts_streams(),
            streams: groups.len() as u32,
            led: led as u32,
            replica: None,
        }
    }

    pub(super) async fn status(&self, stream: StreamId) -> KeeperStatus {
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let led = groups
            .iter()
            .filter(|group| group.raft.metrics().borrow_watched().state == ServerState::Leader)
            .count();
        // A parked or not yet opened replica still holds the stream: an
        // operator recovery must not count it lost.
        let replica = if self.quarantined.read().contains(&stream) {
            Some(false)
        } else {
            groups
                .iter()
                .find(|group| group.genesis.stream == stream)
                .map(|group| group.state.healthy())
                .or_else(|| {
                    (self.disk.healthy()
                        && !self.deleted.read().contains(&stream)
                        && self.disk.installed(stream))
                    .then_some(true)
                })
        };
        KeeperStatus {
            keeper: self.id,
            accepting: self.disk.responsive() && self.disk.space.accepts_streams(),
            streams: groups.len() as u32,
            led: led as u32,
            replica,
        }
    }

    async fn peer_status(&self, keeper: Uuid, stream: StreamId) -> Option<KeeperStatus> {
        if keeper == self.id {
            return Some(self.status(stream).await);
        }
        match timeout(
            STATUS_TIMEOUT,
            self.rpc.call(
                keeper,
                Frame::Client(Request::KeeperStatus(stream)),
                STATUS_TIMEOUT,
            ),
        )
        .await
        {
            Ok(Ok(Reply::Status(status))) if status.keeper == keeper => Some(status),
            _ => None,
        }
    }

    pub(super) async fn repair_loop(self: &Arc<Self>) {
        let mut schedule = tokio::time::interval(REPAIR_INTERVAL);
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                () = self.retire_now.notified() => self.retire_removed().await,
                () = self.disk.slowed() => self.shed_leadership_when_full().await,
                _ = schedule.tick() => {
                    self.repair_pass().await;
                    self.shed_leadership_when_full().await;
                    self.keep_preferred_leaders().await;
                    self.retire_removed().await;
                    self.park_idle().await;
                }
            }
        }
    }

    /// Queues the repair work of every stream this keeper leads and starts
    /// as much of it as the free repair slots allow.
    async fn repair_pass(self: &Arc<Self>) {
        let groups = self
            .groups
            .lock()
            .await
            .iter()
            .map(|(stream, group)| (*stream, group.clone()))
            .collect::<Vec<_>>();
        let now = Instant::now();
        let mut work = Vec::new();
        {
            let mut led = self.led_since.lock();
            let mut seen = self.learners_seen.lock();
            led.retain(|stream, _| groups.iter().any(|(open, _)| open == stream));
            let mut present = HashSet::new();
            for (stream, group) in &groups {
                let metrics = group.raft.metrics().borrow_watched().clone();
                if metrics.state != ServerState::Leader {
                    led.remove(stream);
                    continue;
                }
                let membership = metrics.membership_config.membership();
                if let [_, target] = membership.get_joint_config().as_slice() {
                    led.remove(stream);
                    work.push((*stream, group.clone(), Work::Joint(target.clone())));
                    continue;
                }
                // A learner is stale once the leader has seen it for
                // `STALE_LEARNER` while no replacement holds the stream's
                // membership lock.
                let mut expired = BTreeSet::new();
                for (learner, _) in membership.nodes() {
                    if membership.voter_ids().any(|voter| voter == *learner) {
                        continue;
                    }
                    present.insert((*stream, *learner));
                    let since = *seen.entry((*stream, *learner)).or_insert(now);
                    if now.duration_since(since) >= STALE_LEARNER {
                        expired.insert(*learner);
                    }
                }
                if !expired.is_empty() {
                    work.push((*stream, group.clone(), Work::Learners(expired)));
                    continue;
                }
                let term = metrics.current_term;
                let since = match led.get(stream) {
                    Some((led_term, since)) if *led_term == term => *since,
                    _ => {
                        led.insert(*stream, (term, now));
                        now
                    }
                };
                let Some(heartbeat) = metrics.heartbeat.as_ref() else {
                    continue;
                };
                // A voter is silent when it has not acknowledged this leader
                // for the repair delay, or its keeper has been unreachable
                // for that long, as after a parked stream wakes.
                let quiet = heartbeat
                    .iter()
                    .filter(|(id, _)| **id != self.id.as_u128())
                    .filter(|(id, acked)| {
                        self.dead(Uuid::from_u128(**id))
                            || match acked {
                                Some(acked) => acked.elapsed() >= self.repair_after,
                                None => now.duration_since(since) >= self.repair_after,
                            }
                    })
                    .map(|(id, _)| Uuid::from_u128(*id))
                    .collect::<Vec<_>>();
                if !quiet.is_empty() {
                    work.push((*stream, group.clone(), Work::Voters(quiet)));
                }
            }
            seen.retain(|key, _| present.contains(key));
        }
        let started = {
            let mut queue = self.repairs.lock();
            queue
                .backoff
                .retain(|stream, _| groups.iter().any(|(open, _)| open == stream));
            let cursor = queue.cursor;
            // Higher priority first; within one priority, the streams after
            // the last one started, then the rest.
            work.sort_by_key(|(stream, _, work)| {
                (
                    work.rank(),
                    cursor.is_some_and(|last| *stream <= last),
                    *stream,
                )
            });
            let mut started = Vec::new();
            for (stream, group, work) in work {
                if queue.running.len() >= MAX_REPAIRS {
                    break;
                }
                if queue.running.contains(&stream)
                    || queue
                        .backoff
                        .get(&stream)
                        .is_some_and(|(_, next)| *next > now)
                {
                    continue;
                }
                queue.running.insert(stream);
                queue.cursor = Some(stream);
                started.push((stream, group, work));
            }
            started
        };
        for (stream, group, work) in started {
            let engine = self.clone();
            tokio::spawn(async move {
                let repaired = tokio::select! {
                    () = engine.stop.cancelled() => false,
                    repaired = engine.repair(stream, &group, work) => repaired,
                };
                let mut queue = engine.repairs.lock();
                queue.running.remove(&stream);
                if repaired {
                    queue.backoff.remove(&stream);
                } else {
                    let failures = queue
                        .backoff
                        .get(&stream)
                        .map_or(0, |(failures, _)| *failures);
                    let wait = decisions::backoff(
                        failures,
                        REPAIR_INTERVAL.as_millis() as u64,
                        MAX_REPAIR_BACKOFF.as_millis() as u64,
                    );
                    queue.backoff.insert(
                        stream,
                        (
                            failures.saturating_add(1),
                            Instant::now() + Duration::from_millis(wait),
                        ),
                    );
                }
            });
        }
    }

    /// Runs one unit of repair work. False when it was refused or failed,
    /// which backs the stream off.
    async fn repair(&self, stream: StreamId, group: &Group, work: Work) -> bool {
        #[cfg(test)]
        {
            *self.repair_attempts.lock().entry(stream).or_default() += 1;
            if self.fail_repairs.read().contains(&stream) {
                return false;
            }
        }
        match work {
            // Whoever holds the membership lock is finishing the change.
            Work::Joint(target) => {
                let Ok(_guard) = group.membership.try_lock() else {
                    return true;
                };
                matches!(
                    timeout(
                        super::replacement::MANAGEMENT_TIMEOUT,
                        group.raft.change_membership(target, false),
                    )
                    .await,
                    Ok(Ok(_))
                )
            }
            Work::Learners(learners) => {
                let Ok(_guard) = group.membership.try_lock() else {
                    return true;
                };
                let removed = matches!(
                    timeout(
                        STATUS_TIMEOUT,
                        group.raft.change_membership(
                            openraft::ChangeMembers::RemoveNodes(learners.clone()),
                            false,
                        ),
                    )
                    .await,
                    Ok(Ok(_))
                );
                eprintln!(
                    "logkeeper removed stale learners {learners:?} of stream {stream:?}: {}",
                    if removed { "removed" } else { "deferred" }
                );
                removed
            }
            Work::Voters(quiet) => self.replace_dead_voter(stream, group, &quiet).await,
        }
    }

    async fn replace_dead_voter(&self, stream: StreamId, group: &Group, quiet: &[Uuid]) -> bool {
        let Ok((_, configuration, _, _)) = group.state.placement() else {
            return false;
        };
        let mut health = BTreeMap::new();
        for keeper in self.placement.domains().keys().copied() {
            let voter = configuration.voters.contains(&keeper);
            if voter && !quiet.contains(&keeper) {
                continue;
            }
            let status = self.reachable(keeper).await;
            // Only a silent voter whose keeper still answers is asked about
            // its replica of this stream.
            let live = match status {
                Some(_) if voter => self
                    .peer_status(keeper, stream)
                    .await
                    .is_some_and(|status| status.replica == Some(true)),
                Some(_) => true,
                None => false,
            };
            health.insert(
                keeper,
                Health {
                    live,
                    accepting: status.is_some_and(|status| status.accepting),
                    streams: status.map_or(0, |status| status.streams),
                },
            );
        }
        let view = View {
            eligible: self.placement.domains(),
            health: &health,
        };
        let Some(next) = assignment::repair_roster(stream, configuration.voters, &view) else {
            return false;
        };
        let result = self.replace(group, configuration.revision, next).await;
        let replaced = matches!(
            result,
            Ok(Reply::Decision(super::Outcome::Configuration(_)))
        );
        eprintln!(
            "logkeeper repair of stream {stream:?}: {:?} to {next:?}: {}",
            configuration.voters,
            match result {
                Ok(_) if replaced => "replaced".to_owned(),
                Ok(_) => "refused".to_owned(),
                Err(error) => error.to_string(),
            }
        );
        replaced
    }

    /// A keeper whose media is unhealthy, slow or full cannot accept the
    /// writes of the streams it leads, even when their followers have room.
    /// It hands each to a follower that has matched its log and whose keeper
    /// accepts streams. Slow media sheds at once, not at the next pass.
    pub(super) async fn shed_leadership_when_full(&self) {
        if self.disk.responsive() && self.disk.space.accepts_streams() {
            return;
        }
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for group in groups {
            let metrics = group.raft.metrics().borrow_watched().clone();
            if metrics.state != ServerState::Leader {
                continue;
            }
            let matched = metrics
                .replication
                .iter()
                .flatten()
                .filter(|(id, log)| {
                    **id != metrics.id && log.map(|log| log.index) == metrics.last_log_index
                })
                .map(|(id, _)| Uuid::from_u128(*id))
                .collect::<Vec<_>>();
            for target in matched {
                if self
                    .reachable(target)
                    .await
                    .is_some_and(|status| status.accepting)
                {
                    let _ = group.raft.trigger().transfer_leader(target.as_u128()).await;
                    break;
                }
            }
        }
    }

    /// Records the failure domain of `keeper` as the one `stream`'s writer
    /// wants its leader in. Kept in memory on every voter: the writer
    /// repeats it after each seal, so it needs no durable record.
    pub(super) fn record_preference(&self, stream: StreamId, keeper: Uuid) {
        if let Some(domain) = self.placement.domains().get(&keeper) {
            self.preferred.lock().insert(stream, domain.clone());
        }
    }

    /// A writer's request for `keeper` to lead. The leader records it,
    /// forwards it to the other voters so a later leader keeps it, and
    /// hands leadership over when the hold-down allows.
    pub(super) async fn prefer_leader(
        &self,
        group: &Group,
        keeper: Uuid,
    ) -> std::io::Result<Reply> {
        let stream = group.genesis.stream;
        if group.raft.metrics().borrow_watched().state == ServerState::Leader {
            self.record_preference(stream, keeper);
            let followers = group
                .state
                .finalized()
                .map(|configuration| configuration.voters)
                .into_iter()
                .flatten()
                .filter(|voter| *voter != self.id);
            futures::future::join_all(followers.map(|follower| {
                self.rpc.call::<Reply>(
                    follower,
                    Frame::Client(Request::PreferLeader { stream, keeper }),
                    STATUS_TIMEOUT,
                )
            }))
            .await;
        }
        Ok(group.prefer_leader(keeper).await)
    }

    /// Moves each stream this keeper leads to the voter in its writer's
    /// preferred domain, once that voter has matched the log, its keeper
    /// accepts streams and the hold-down has passed. This restores the
    /// writer's choice after a park, a restart, a graceful hand-off,
    /// shedding or an election that moved leadership away.
    async fn keep_preferred_leaders(&self) {
        let preferred = self.preferred.lock().clone();
        if preferred.is_empty() {
            return;
        }
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for group in groups {
            let Some(domain) = preferred.get(&group.genesis.stream) else {
                continue;
            };
            if group.raft.metrics().borrow_watched().state != ServerState::Leader {
                continue;
            }
            let Some(target) = group.state.finalized().and_then(|configuration| {
                configuration
                    .voters
                    .into_iter()
                    .find(|voter| self.placement.domains().get(voter) == Some(domain))
            }) else {
                continue;
            };
            if target == self.id
                || !self
                    .reachable(target)
                    .await
                    .is_some_and(|status| status.accepting)
            {
                continue;
            }
            group.prefer_leader(target).await;
        }
    }

    /// Retires this keeper's copy of a stream that has heard from no leader
    /// for the repair delay, or that a peer refused as outside its placement,
    /// and whose current placement, certified by another keeper, no longer
    /// names this keeper. That copy belongs to a voter replaced while it was
    /// down, moved off by a drain, or lost to an operator recovery. A peer
    /// that refused the copy is asked first: a lost voter's old peers may
    /// still certify the placement it lost.
    async fn retire_removed(&self) {
        let groups = self
            .groups
            .lock()
            .await
            .iter()
            .map(|(stream, group)| (*stream, group.clone()))
            .collect::<Vec<_>>();
        let now = Instant::now();
        let orphaned = groups
            .iter()
            .filter(|(_, group)| {
                group.excluded.lock().is_some()
                    || (group.raft.metrics().borrow_watched().state != ServerState::Leader
                        && now.duration_since(*group.heard.lock()) >= self.repair_after)
            })
            .cloned()
            .collect::<Vec<_>>();
        for (stream, group) in orphaned {
            let Some(generation) = self
                .disk
                .ownership(stream)
                .and_then(|book| book.generation())
            else {
                continue;
            };
            let excluder = *group.excluded.lock();
            let authorities = excluder
                .into_iter()
                .chain(self.placement.domains().keys().copied())
                .collect::<Vec<_>>();
            for authority in authorities {
                if authority == self.id {
                    continue;
                }
                let Ok(proof) = self.verified_proof(authority, &group.genesis).await else {
                    continue;
                };
                let named = proof.configuration.voters.contains(&self.id)
                    || proof.joint.is_some_and(|roster| roster.contains(&self.id));
                if named {
                    // The refusal came from a stale or lagging peer.
                    *group.excluded.lock() = None;
                } else {
                    let result = self
                        .retire_copy(stream, authority, proof.configuration.revision, generation)
                        .await;
                    eprintln!(
                        "logkeeper retired its removed copy of stream {stream:?}: {}",
                        match result {
                            Ok(_) => "retired".to_owned(),
                            Err(error) => error.to_string(),
                        }
                    );
                }
                break;
            }
        }
    }
}
