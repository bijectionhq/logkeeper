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
    BUILD_VERSION, CLUSTER_VERSION_CURRENT, CLUSTER_VERSION_V1, KeeperStatus, decisions, features,
    metrics, network,
};

#[cfg(not(test))]
pub(super) const PING_INTERVAL: Duration = Duration::from_secs(2);
#[cfg(test)]
pub(super) const PING_INTERVAL: Duration = Duration::from_millis(250);
const PING_TIMEOUT: Duration = Duration::from_millis(1500);
/// How often a keeper below this build's cluster version asks the catalog
/// whether the version was finalized.
#[cfg(not(test))]
const VERSION_INTERVAL: Duration = Duration::from_secs(10);
#[cfg(test)]
const VERSION_INTERVAL: Duration = Duration::from_millis(250);
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

struct PeerState {
    answered: Instant,
    status: KeeperStatus,
    /// True when the peer answered with an ALPN/protocol version mismatch.
    /// Such a keeper is alive on another version and never triggers repair.
    version_mismatch: bool,
}

pub(super) struct Liveness {
    started: Instant,
    populated: bool,
    peers: HashMap<Uuid, PeerState>,
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
                .map_or(self.started, |peer| peer.answered),
        )
    }

    fn version_mismatched(&self, keeper: Uuid) -> bool {
        self.peers.get(&keeper).is_some_and(|peer| {
            peer.version_mismatch && peer.answered.elapsed() < PING_INTERVAL * MISSED_PINGS
        })
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
            .all_domains()
            .keys()
            .filter(|keeper| **keeper != self.id)
            .count();
        if expected_peers == 0 {
            return true;
        }
        liveness
            .peers
            .values()
            .any(|peer| peer.answered.elapsed() < PING_INTERVAL * MISSED_PINGS)
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
            .is_some_and(|peer| peer.answered.elapsed() < PING_INTERVAL * MISSED_PINGS)
    }

    /// Liveness summary for every keeper in the cluster inventory.
    pub(super) fn liveness_snapshot(&self, own_accepting: bool) -> Vec<metrics::KeeperLiveness> {
        let liveness = self.liveness.lock();
        let now = Instant::now();
        let repair_ms = self.repair_after.as_millis() as u64;
        self.placement
            .all_domains()
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
                    Some(peer) if peer.answered.elapsed() < PING_INTERVAL * MISSED_PINGS => {
                        (metrics::LivenessState::Alive, peer.status.accepting)
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
        let peer = liveness.peers.get(&keeper)?;
        (peer.answered.elapsed() < PING_INTERVAL * MISSED_PINGS).then(|| peer.status.clone())
    }

    /// Whether `keeper` recently answered with an incompatible protocol version.
    /// A version mismatch counts as alive and never triggers automatic repair.
    pub(super) fn version_mismatched(&self, keeper: Uuid) -> bool {
        keeper != self.id && self.liveness.lock().version_mismatched(keeper)
    }

    /// Feature bits advertised by `keeper`, or 0 when unknown or N-1.
    #[cfg(test)]
    pub(super) fn peer_features(&self, keeper: Uuid) -> u64 {
        if keeper == self.id {
            return features::SUPPORTED;
        }
        self.liveness
            .lock()
            .peers
            .get(&keeper)
            .map_or(0, |peer| peer.status.features)
    }

    /// Whether `keeper` advertises every feature bit in `required`.
    #[cfg(test)]
    pub(super) fn peer_supports(&self, keeper: Uuid, required: u64) -> bool {
        decisions::peer_supports(self.peer_features(keeper), required)
    }

    /// Answers a liveness ping from `sender`, in the layout its lane speaks.
    pub(super) async fn pong(
        &self,
        sender: u128,
        incarnation: Uuid,
        version: network::WireVersion,
    ) -> network::BatchReply {
        let known_as = self
            .recognition
            .greet(Uuid::from_u128(sender), incarnation)
            .await;
        let pong = network::Pong {
            status: self.keeper_status().await,
            incarnation: self.recognition.own(),
            known_as,
        };
        match network::encode_pong(&pong, version) {
            Ok(bytes) => network::BatchReply::Ok(bytes),
            Err(error) => network::BatchReply::Err(error.to_string()),
        }
    }

    /// Records the build version and feature bits carried by an incoming
    /// ping. Only this keeper's own pings decide whether a peer answers, so
    /// an incoming ping neither refreshes nor creates a peer's entry.
    pub(super) fn record_incoming_ping(&self, keeper: Uuid, version: String, peer_features: u64) {
        if let Some(peer) = self.liveness.lock().peers.get_mut(&keeper) {
            peer.status.build_version = version;
            peer.status.features = peer_features;
        }
    }

    /// Whether `keeper` has been unreachable for the repair delay. A peer on
    /// an incompatible protocol version counts as alive and is never dead.
    pub(super) fn dead(&self, keeper: Uuid) -> bool {
        if keeper == self.id {
            return false;
        }
        let liveness = self.liveness.lock();
        let now = Instant::now();
        decisions::triggers_repair(
            liveness.silent(keeper, now).as_millis() as u64,
            self.repair_after.as_millis() as u64,
            liveness.version_mismatched(keeper),
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

    /// Learns the finalized cluster feature level from the catalog until it
    /// reaches this build's level. It runs apart from the pings, so a slow
    /// or unreachable catalog never delays them.
    pub(super) async fn cluster_version_loop(&self) {
        let mut schedule = tokio::time::interval(VERSION_INTERVAL);
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        while self.disk.cluster_version() < CLUSTER_VERSION_CURRENT {
            tokio::select! {
                () = self.stop.cancelled() => return,
                _ = schedule.tick() => self.sync_cluster_version().await,
            }
        }
        // The keeper stops when any of its tasks ends, so this one waits.
        self.stop.cancelled().await;
    }

    /// Queries the catalog for the finalized cluster feature level and
    /// advances this keeper's write-version gate monotonically.
    pub(super) async fn sync_cluster_version(&self) {
        if let Ok(super::Reply::ClusterVersion(version)) =
            self.catalog_request(super::Request::ClusterVersion).await
        {
            self.disk.set_write_version(version);
        }
    }

    /// Whether every other keeper in the inventory answers a live probe now
    /// and advertises the write-version gate: `Ok(())` when all do,
    /// `Unsupported` when one answers without the feature or on another
    /// protocol version, and `Unavailable` when one does not answer. Live
    /// probes, not cached liveness, so a keeper stopped or downgraded since
    /// its last ping cannot slip past.
    pub(super) async fn all_keepers_support_version(
        &self,
        target: u32,
    ) -> Result<(), journal_contract::JournalError> {
        use journal_contract::JournalError;
        if target > CLUSTER_VERSION_CURRENT {
            return Err(JournalError::Unsupported);
        }
        let peers = self
            .placement
            .all_domains()
            .keys()
            .copied()
            .filter(|keeper| *keeper != self.id)
            .collect::<Vec<_>>();
        // A probe retries a lost answer, so one slow round trip does not
        // refuse the finalization; an unreachable keeper still does.
        let checks = futures::future::join_all(peers.into_iter().map(|keeper| async move {
            for _ in 0..3 {
                let probed = timeout(
                    PING_TIMEOUT,
                    self.control.ping(
                        keeper,
                        self.recognition.own(),
                        BUILD_VERSION.to_owned(),
                        features::SUPPORTED,
                        PING_TIMEOUT,
                    ),
                )
                .await;
                match probed {
                    Ok(Ok(pong)) if pong.status.keeper == keeper => {
                        return if decisions::peer_supports(
                            pong.status.features,
                            features::WRITE_VERSION_GATE,
                        ) {
                            Ok(())
                        } else {
                            Err(JournalError::Unsupported)
                        };
                    }
                    Ok(Err(error)) if network::is_version_mismatch(&error) => {
                        return Err(JournalError::Unsupported);
                    }
                    _ => (),
                }
            }
            Err(JournalError::Unavailable)
        }))
        .await;
        // A keeper without the feature outranks one that did not answer: the
        // first will not change by retrying.
        let mut result = Ok(());
        for check in checks {
            match check {
                Err(JournalError::Unsupported) => return Err(JournalError::Unsupported),
                Err(error) => result = Err(error),
                Ok(()) => (),
            }
        }
        result
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
            .all_domains()
            .keys()
            .copied()
            .filter(|keeper| *keeper != self.id)
            .collect::<Vec<_>>();
        let own = self.recognition.own();
        let answers = futures::future::join_all(peers.into_iter().map(|keeper| async move {
            let answer = timeout(
                PING_TIMEOUT,
                self.control.ping(
                    keeper,
                    own,
                    BUILD_VERSION.to_owned(),
                    features::SUPPORTED,
                    PING_TIMEOUT,
                ),
            )
            .await;
            (keeper, answer)
        }))
        .await;
        let mut mismatched = Vec::new();
        let answers = answers
            .into_iter()
            .filter_map(|(keeper, answer)| match answer {
                Ok(Ok(pong)) if pong.status.keeper == keeper => Some((keeper, pong)),
                Ok(Err(error)) if network::is_version_mismatch(&error) => {
                    mismatched.push((keeper, error));
                    None
                }
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
            liveness.peers.insert(
                keeper,
                PeerState {
                    answered: now,
                    status: pong.status,
                    version_mismatch: false,
                },
            );
        }
        // A keeper on an incompatible protocol version is alive: it counts
        // as answering, accepts no new streams, and never triggers repair.
        for (keeper, error) in mismatched {
            let first = !liveness
                .peers
                .get(&keeper)
                .is_some_and(|peer| peer.version_mismatch);
            if first {
                tracing::warn!(
                    keeper = %self.id,
                    peer = %keeper,
                    error = %error,
                    "peer runs an incompatible protocol version; counted as alive, not repaired"
                );
            }
            liveness
                .peers
                .entry(keeper)
                .and_modify(|peer| {
                    peer.answered = now;
                    peer.version_mismatch = true;
                    peer.status.accepting = false;
                })
                .or_insert_with(|| PeerState {
                    answered: now,
                    status: KeeperStatus {
                        keeper,
                        accepting: false,
                        streams: 0,
                        led: 0,
                        replica: None,
                        build_version: String::new(),
                        features: 0,
                        cluster_version: CLUSTER_VERSION_V1,
                    },
                    version_mismatch: true,
                });
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
            .all_domains()
            .keys()
            .copied()
            .filter(|keeper| self.dead(*keeper))
            .collect::<BTreeSet<_>>();
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
        let needs_wake = |voters: &[Uuid; 3]| {
            let lost = voters
                .iter()
                .filter(|voter| {
                    dead.contains(voter) || !self.placement.all_domains().contains_key(voter)
                })
                .count();
            lost == 1 || (lost == 0 && !self.placement.roster(voters))
        };
        if !candidates.iter().any(|(_, voters)| needs_wake(voters)) {
            // A woken stream leaves the candidates while it is open, so its
            // backoff is kept as long as a keeper is dead.
            if dead.is_empty() {
                self.liveness.lock().wakes.clear();
            }
            return;
        }
        let now = Instant::now();
        let mut woken = Vec::new();
        {
            let mut liveness = self.liveness.lock();
            let backoff = self.repair_after.as_millis() as u64;
            liveness
                .wakes
                .retain(|_, (_, next)| now.saturating_duration_since(*next) < MAX_WAKE_BACKOFF);
            for (stream, voters) in candidates {
                if !needs_wake(&voters) {
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
                    "woke parked stream to repair placement or a dead voter"
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
        if self.mode.draining() {
            return;
        }
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
