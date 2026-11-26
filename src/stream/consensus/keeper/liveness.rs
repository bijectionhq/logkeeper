//! Keeper-level liveness and the wake sweep for parked streams.
//!
//! Every keeper pings every other keeper on the multiplexed control channel
//! every `PING_INTERVAL` and records when it last answered, together with
//! the keeper-wide status it reported. The table answers three questions
//! without a round trip per stream:
//!
//! - whether a keeper is reachable now, for repair and placement health;
//! - whether a keeper is dead: unreachable for the repair delay;
//! - which keeper campaigns at once when a parked stream reopens.
//!
//! Pings and their answers also carry media incarnations, from which each
//! keeper recognizes a keeper ID reused on new media: see `incarnation`.
//!
//! Repair runs on leaders, and a parked stream has none. So each keeper also
//! sweeps its own parked copies: one whose configuration names a dead keeper
//! reopens, at a bounded rate and with a per-stream backoff, and its new
//! leader repairs it as it would an open stream. Parked streams whose voters
//! all live stay parked. Each holder sweeps its own copies rather than the
//! catalog's leader: only the replicas know a stream's current
//! configuration, and the sweep needs no catalog and no new authority.

use std::{
    collections::{BTreeSet, HashMap},
    time::Duration,
};

use journal_contract::StreamId;
use openraft::async_runtime::WatchReceiver;
use tokio::time::{Instant, timeout};
use uuid::Uuid;

use super::{Engine, Group};
use crate::stream::consensus::{
    KeeperStatus, decisions, metrics,
    network::{Frame, Pong},
};

#[cfg(not(test))]
pub(super) const PING_INTERVAL: Duration = Duration::from_secs(2);
#[cfg(test)]
pub(super) const PING_INTERVAL: Duration = Duration::from_millis(250);
const PING_TIMEOUT: Duration = Duration::from_millis(1500);
/// A keeper that missed this many pings in a row is unreachable.
const MISSED_PINGS: u32 = 3;
/// Parked streams one keeper reopens per sweep.
const WAKES_PER_SWEEP: usize = 8;
/// The longest wait before a woken stream that still names a dead keeper
/// is woken again.
#[cfg(not(test))]
const MAX_WAKE_BACKOFF: Duration = Duration::from_secs(3600);
#[cfg(test)]
const MAX_WAKE_BACKOFF: Duration = Duration::from_secs(16);

pub(super) struct Liveness {
    started: Instant,
    populated: bool,
    peers: HashMap<Uuid, (Instant, KeeperStatus)>,
    /// Failed wakes and the earliest next wake of each parked stream.
    wakes: HashMap<StreamId, (u32, Instant)>,
}

impl Default for Liveness {
    fn default() -> Self {
        Self {
            started: Instant::now(),
            populated: false,
            peers: HashMap::new(),
            wakes: HashMap::new(),
        }
    }
}

impl Liveness {
    /// How long `keeper` has not answered, counted from this keeper's start
    /// when it never has.
    fn silent(&self, keeper: Uuid, now: Instant) -> Duration {
        now.duration_since(
            self.peers
                .get(&keeper)
                .map_or(self.started, |(answered, _)| *answered),
        )
    }
}

impl Engine {
    /// Whether at least one ping round has finished and the keeper can see
    /// at least one peer (or has no peers configured).
    pub(super) fn liveness_populated(&self) -> bool {
        let liveness = self.liveness.lock();
        if !liveness.populated {
            return false;
        }
        let expected_peers = self
            .placement
            .domains()
            .keys()
            .filter(|keeper| **keeper != self.id)
            .count();
        if expected_peers == 0 {
            return true;
        }
        liveness
            .peers
            .values()
            .any(|(answered, _)| answered.elapsed() < PING_INTERVAL * MISSED_PINGS)
    }

    /// Synchronous liveness check for whether `keeper` answered a recent ping.
    pub(super) fn is_peer_reachable(&self, keeper: Uuid) -> bool {
        if keeper == self.id {
            return true;
        }
        let liveness = self.liveness.lock();
        liveness
            .peers
            .get(&keeper)
            .is_some_and(|(answered, _)| answered.elapsed() < PING_INTERVAL * MISSED_PINGS)
    }

    /// Liveness summary for every keeper in the cluster inventory.
    pub(super) fn liveness_snapshot(&self, own_accepting: bool) -> Vec<metrics::KeeperLiveness> {
        let liveness = self.liveness.lock();
        let now = Instant::now();
        let repair_ms = self.repair_after.as_millis() as u64;
        self.placement
            .domains()
            .iter()
            .map(|(&keeper, domain)| {
                if keeper == self.id {
                    return metrics::KeeperLiveness {
                        keeper,
                        domain: domain.clone(),
                        state: metrics::LivenessState::Alive,
                        accepting: own_accepting,
                        silent_secs: 0.0,
                    };
                }
                let silent = liveness.silent(keeper, now);
                let dead = decisions::keeper_dead(silent.as_millis() as u64, repair_ms);
                let (state, accepting) = match liveness.peers.get(&keeper) {
                    Some((answered, status))
                        if answered.elapsed() < PING_INTERVAL * MISSED_PINGS =>
                    {
                        (metrics::LivenessState::Alive, status.accepting)
                    }
                    _ if dead => (metrics::LivenessState::Dead, false),
                    _ => (metrics::LivenessState::Suspect, false),
                };
                metrics::KeeperLiveness {
                    keeper,
                    domain: domain.clone(),
                    state,
                    accepting,
                    silent_secs: silent.as_secs_f64(),
                }
            })
            .collect()
    }

    /// The status `keeper` reported with its last ping answer, when that
    /// answer is recent. This keeper's own status is always current.
    pub(super) async fn reachable(&self, keeper: Uuid) -> Option<KeeperStatus> {
        if keeper == self.id {
            return Some(self.keeper_status().await);
        }
        let liveness = self.liveness.lock();
        let (answered, status) = liveness.peers.get(&keeper)?;
        (answered.elapsed() < PING_INTERVAL * MISSED_PINGS).then_some(*status)
    }

    /// Whether `keeper` has been unreachable for the repair delay.
    pub(super) fn dead(&self, keeper: Uuid) -> bool {
        keeper != self.id
            && decisions::keeper_dead(
                self.liveness
                    .lock()
                    .silent(keeper, Instant::now())
                    .as_millis() as u64,
                self.repair_after.as_millis() as u64,
            )
    }

    /// Whether `keeper` missed its last pings, a much shorter signal than
    /// `dead` that only decides who campaigns first.
    fn suspect(&self, keeper: Uuid) -> bool {
        keeper != self.id
            && self.liveness.lock().silent(keeper, Instant::now()) >= PING_INTERVAL * MISSED_PINGS
    }

    pub(super) async fn liveness_loop(&self) {
        let mut schedule = tokio::time::interval(PING_INTERVAL);
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                () = self.stop.cancelled() => return,
                _ = schedule.tick() => {
                    self.ping().await;
                    self.wake_for_dead().await;
                }
            }
        }
    }

    /// Pings the other keepers at once when no peer has confirmed this
    /// keeper's identity yet, so a bootstrap need not wait for the next
    /// round.
    pub(super) async fn check_identity(&self) {
        if let Some(_checking) = self.recognition.checking().await {
            self.ping().await;
        }
    }

    /// Pings every other keeper concurrently and records who answered, the
    /// incarnation each answered under, and the one each knows this keeper
    /// under.
    async fn ping(&self) {
        let peers = self
            .placement
            .domains()
            .keys()
            .copied()
            .filter(|keeper| *keeper != self.id)
            .collect::<Vec<_>>();
        let own = self.recognition.own();
        let answers = futures::future::join_all(peers.into_iter().map(|keeper| async move {
            let answer = timeout(
                PING_TIMEOUT,
                self.control
                    .call::<Pong>(keeper, Frame::Liveness(own), PING_TIMEOUT),
            )
            .await;
            (keeper, answer)
        }))
        .await;
        let answers = answers
            .into_iter()
            .filter_map(|(keeper, answer)| match answer {
                Ok(Ok(pong)) if pong.status.keeper == keeper => Some((keeper, pong)),
                _ => None,
            })
            .collect::<Vec<_>>();
        if !answers.is_empty() {
            self.recognition
                .answered(
                    &answers
                        .iter()
                        .map(|(keeper, pong)| (*keeper, pong.incarnation, pong.known_as))
                        .collect::<Vec<_>>(),
                )
                .await;
        }
        let now = Instant::now();
        let mut liveness = self.liveness.lock();
        liveness.populated = true;
        for (keeper, pong) in answers {
            liveness.peers.insert(keeper, (now, pong.status));
        }
    }

    /// Reopens parked copies of streams whose configuration names a dead
    /// keeper, so their leaders repair them. A stream with two dead voters
    /// needs an operator and stays parked. Each woken stream waits at least
    /// the repair delay, doubling up to `MAX_WAKE_BACKOFF`, before it is
    /// woken again, so a stream that cannot be repaired does not stay awake.
    async fn wake_for_dead(&self) {
        let dead = self
            .placement
            .domains()
            .keys()
            .copied()
            .filter(|keeper| self.dead(*keeper))
            .collect::<BTreeSet<_>>();
        if dead.is_empty() {
            self.liveness.lock().wakes.clear();
            return;
        }
        // A parked copy knows its current configuration. A copy that never
        // opened, such as one past the stream limit at startup, is judged
        // by its genesis voters.
        let open = self
            .groups
            .lock()
            .await
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let candidates = {
            let parked = self.parked.read();
            let deleted = self.deleted.read();
            let quarantined = self.quarantined.read();
            let closed = self.closed_states.lock();
            let parked_copies = parked.keys().filter_map(|stream| {
                let configuration = closed.get(stream)?.finalized()?;
                Some((*stream, configuration.voters))
            });
            let unopened = self
                .disk
                .streams()
                .into_iter()
                .filter(|genesis| {
                    let stream = genesis.stream;
                    !open.contains(&stream)
                        && !parked.contains_key(&stream)
                        && !deleted.contains(&stream)
                        && !quarantined.contains(&stream)
                        && self.attached(stream)
                })
                .map(|genesis| (genesis.stream, genesis.voters));
            parked_copies.chain(unopened).collect::<Vec<_>>()
        };
        let now = Instant::now();
        let mut woken = Vec::new();
        {
            let mut liveness = self.liveness.lock();
            let backoff = self.repair_after.as_millis() as u64;
            liveness
                .wakes
                .retain(|_, (_, next)| now.saturating_duration_since(*next) < MAX_WAKE_BACKOFF);
            for (stream, voters) in candidates {
                let lost = voters.iter().filter(|voter| dead.contains(voter)).count();
                if lost != 1 {
                    continue;
                }
                let (failures, next) = liveness.wakes.get(&stream).copied().unwrap_or((0, now));
                if next > now {
                    continue;
                }
                let wait =
                    decisions::backoff(failures, backoff, MAX_WAKE_BACKOFF.as_millis() as u64);
                liveness.wakes.insert(
                    stream,
                    (
                        failures.saturating_add(1),
                        now + Duration::from_millis(wait),
                    ),
                );
                woken.push(stream);
                if woken.len() == WAKES_PER_SWEEP {
                    break;
                }
            }
        }
        for stream in woken {
            if self.wake(stream).await.is_some() {
                metrics::count(&self.disk.metrics.unparked_for_repair);
                tracing::info!(
                    keeper = %self.id,
                    stream = %crate::stream::consensus::logging::stream_uuid(stream),
                    "woke parked stream to repair dead voter"
                );
            }
        }
    }

    /// Reopens a parked stream, or one that never opened because startup
    /// found the keeper past its stream limit, and campaigns at once when
    /// this keeper is the voter that should lead it, instead of waiting an
    /// election timeout. `None` when this keeper holds no such closed copy
    /// or it did not open.
    pub(super) async fn unpark(&self, stream: StreamId) -> Option<std::sync::Arc<Group>> {
        let parked = self.parked.write().remove(&stream).is_some();
        if !parked
            && (self.deleted.read().contains(&stream)
                || self.quarantined.read().contains(&stream)
                || !self.attached(stream))
        {
            return None;
        }
        self.wake(stream).await
    }

    /// Whether this keeper holds a current copy of `stream`.
    fn attached(&self, stream: StreamId) -> bool {
        self.disk
            .ownership(stream)
            .is_some_and(|book| book.generation().is_some())
    }

    /// Opens a closed copy and campaigns when this keeper should lead it.
    async fn wake(&self, stream: StreamId) -> Option<std::sync::Arc<Group>> {
        self.parked.write().remove(&stream);
        let genesis = self.disk.genesis(stream)?;
        let group = self.group(genesis).await.ok()?;
        self.campaign_after_wake(&group).await;
        Some(group)
    }

    /// The voter that led the stream before it parked campaigns as soon as
    /// it reopens. Its stored vote reads back uncommitted, so OpenRaft would
    /// otherwise wait an election timeout; the followers still hold its
    /// lease and grant the leader they followed at once. When that voter's
    /// keeper is unreachable, the first reachable voter campaigns as soon
    /// as the followers' leases from the old leader end, instead of after a
    /// further election timeout.
    async fn campaign_after_wake(&self, group: &Group) {
        let Ok(vote) = group.raft.with_raft_state(|state| *state.vote_ref()).await else {
            return;
        };
        let previous = Uuid::from_u128(vote.leader_id().voted_for);
        if previous == self.id {
            let _ = group.raft.trigger().elect(false).await;
            return;
        }
        if !self.suspect(previous) {
            return;
        }
        let first = group
            .state
            .membership()
            .membership()
            .voter_ids()
            .map(Uuid::from_u128)
            .filter(|voter| !self.suspect(*voter))
            .min();
        if first != Some(self.id) {
            return;
        }
        let lease = Duration::from_millis(self.raft_config.election_timeout_max);
        let raft = group.raft.clone();
        let stop = group.stop.clone();
        tokio::spawn(async move {
            tokio::select! {
                () = stop.cancelled() => (),
                () = tokio::time::sleep(lease) => {
                    if raft.metrics().borrow_watched().current_leader.is_none() {
                        let _ = raft.trigger().elect(false).await;
                    }
                }
            }
        });
    }
}
