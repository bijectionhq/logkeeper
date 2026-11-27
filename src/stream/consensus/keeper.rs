mod admission;
mod catalog_stream;
mod incarnation;
mod ingress;
mod liveness;
mod park;
mod recovery;
mod repair;
mod replacement;
mod replicas;
#[cfg(test)]
mod tests;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    io,
    net::SocketAddr,
    path::{Path, PathBuf},
    sync::{Arc, Weak},
    time::Duration,
};

use bytes::Bytes;
use journal_contract::{Epoch, JournalError, Lsn, StreamId};
use openraft::{
    BasicNode, ReadPolicy, SnapshotPolicy,
    async_runtime::WatchReceiver,
    errors::{ClientWriteError, InitializeError, RaftError},
    impls::ProgressResponder,
};
use serde::Deserialize;
use tokio::{
    net::TcpListener,
    sync::{Mutex, Semaphore, mpsc, oneshot, watch},
    task::JoinSet,
    time::{Instant, timeout, timeout_at},
};
use tokio_rustls::TlsAcceptor;
use tokio_util::sync::CancellationToken;

use super::{
    Credentials, Domains, Fence, Genesis, Keepers, NodeId, Raft, Vote,
    catalog::Catalog,
    invalid,
    network::{Frame, Lane, Network, Reply, Request, Rpc},
    placement::Placement,
    state::{Command, Outcome},
    storage::{self, Authority, Disk, Enrollment, FollowerAppend, LogStore, Record, StateMachine},
};
use crate::server::durability::SyncMode;
use crate::stream::{transport, wire::KeeperId};
use admission::ReplicationIngress;
pub use recovery::{Recovery, RecoveryReport};

const REQUEST_TIMEOUT: Duration = Duration::from_secs(5);
const MAX_HEAD_REQUESTS: usize = 256;
const MAX_PENDING_WRITES: usize = 16;
const MAX_LOG_SUFFIX: u64 = 512;
/// The least time between two leadership hand-offs of one stream.
#[cfg(not(test))]
const LEADER_HOLD_DOWN: Duration = Duration::from_secs(60);
#[cfg(test)]
const LEADER_HOLD_DOWN: Duration = Duration::from_secs(4);
/// How long a deleted stream's settled group stays open for late requests.
#[cfg(not(test))]
const DELETED_GROUP_GRACE: Duration = Duration::from_secs(30);
#[cfg(test)]
const DELETED_GROUP_GRACE: Duration = Duration::from_secs(2);
const SNAPSHOT_CHUNK_BYTES: u64 = 1024 * 1024;
use ingress::{MAX_BULK_CONNECTIONS, MAX_CLIENT_CONNECTIONS};

fn default_max_streams() -> usize {
    128
}

fn default_repair_after_secs() -> u64 {
    600
}

fn default_park_after_secs() -> u64 {
    600
}

fn default_snapshot_send_bytes_per_second() -> u64 {
    64 * 1024 * 1024
}

/// Installed, authenticated keeper inventory and local service settings.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub keeper: uuid::Uuid,
    pub listen: SocketAddr,
    pub data: PathBuf,
    pub tls: Credentials,
    pub keepers: Keepers,
    pub peers: Keepers,
    pub bulk: Keepers,
    pub domains: Domains,
    pub enrollment: PathBuf,
    pub catalog: uuid::Uuid,
    /// Three keepers in distinct failure domains that host the catalog as a
    /// consensus stream of its own. Without them `catalog` alone holds it.
    /// `catalog` must be one of them: it seeds the replicated catalog with
    /// its single-keeper entries once.
    #[serde(default)]
    pub catalog_voters: Option<[uuid::Uuid; 3]>,
    pub readers: Vec<String>,
    pub writers: Vec<String>,
    pub administrators: Vec<String>,
    #[serde(default = "default_max_streams")]
    pub max_streams: usize,
    /// How long a voter stays silent before its stream's leader replaces it.
    #[serde(default = "default_repair_after_secs")]
    pub repair_after_secs: u64,
    /// How long a stream serves no client and appends nothing before its
    /// voters park it.
    #[serde(default = "default_park_after_secs")]
    pub park_after_secs: u64,
    /// Bytes per second this keeper sends in snapshot transfers across all
    /// its streams; zero sends without pacing.
    #[serde(default = "default_snapshot_send_bytes_per_second")]
    pub snapshot_send_bytes_per_second: u64,
    /// Installed timed-original trust and, on a signing keeper, its clock
    /// and attestation key, in the stream keeper's mount format.
    #[serde(default)]
    pub timed_original: Option<crate::stream::transport::TimedOriginalConfig>,
    /// How durable writes reach stable storage: `"full"` (the default) or
    /// `"fsync"`. On Apple platforms only `"full"`, which issues
    /// `F_FULLFSYNC`, survives power loss; elsewhere both flush alike.
    #[serde(default)]
    pub sync_mode: SyncMode,
    /// A timed authority supplied in process, which takes precedence over
    /// `timed_original`.
    #[serde(skip)]
    pub timed_authority: Option<super::timed::TimedAuthority>,
}

impl Config {
    pub fn read(path: &Path) -> io::Result<Self> {
        Ok(serde_json::from_slice(&std::fs::read(path)?)?)
    }

    pub fn initialize(&self) -> io::Result<()> {
        self.validate()?;
        self.tls
            .peer_protocol(KeeperId(self.keeper.as_u128()), Lane::Control.alpn())?;
        self.enrollment()?.initialize()
    }

    pub async fn repair_snapshot(&self, stream: StreamId, backup: &Path) -> io::Result<()> {
        let placement = self.validate()?;
        self.tls
            .peer_protocol(KeeperId(self.keeper.as_u128()), Lane::Control.alpn())?;
        let enrollment = self.enrollment()?;
        let backup = backup.to_owned();
        let (disk, result) = tokio::task::spawn_blocking(move || {
            let disk = Disk::open(enrollment)?;
            let result = storage::repair_snapshot(&disk, stream, &backup, &placement);
            Ok::<_, io::Error>((disk, result))
        })
        .await??;
        let shutdown = disk.shutdown().await;
        result.and(shutdown)
    }

    /// Every path that writes this keeper's media opens its enrollment
    /// first, so installing the sync mode here covers them all.
    fn enrollment(&self) -> io::Result<Enrollment> {
        self.sync_mode.install();
        Enrollment::authorized(
            &self.enrollment,
            &self.data,
            self.keeper,
            self.catalog,
            &self.domains[&self.keeper],
            &self.tls.certificate,
        )
    }

    fn validate(&self) -> io::Result<Placement> {
        if !(3..=1024).contains(&self.keepers.len())
            || self.max_streams == 0
            || !self.keepers.contains_key(&self.keeper)
            || !self.keepers.contains_key(&self.catalog)
            || self.keepers.keys().any(uuid::Uuid::is_nil)
            || !self.keepers.keys().eq(self.peers.keys())
            || !self.keepers.keys().eq(self.bulk.keys())
            || self
                .keepers
                .values()
                .chain(self.peers.values())
                .chain(self.bulk.values())
                .collect::<BTreeSet<_>>()
                .len()
                != self.keepers.len() * 3
            || self
                .readers
                .iter()
                .chain(&self.writers)
                .chain(&self.administrators)
                .any(|uri| !transport::valid_client_uri(uri))
        {
            return Err(invalid("invalid consensus keeper configuration"));
        }
        let authority = Authority::read(&self.enrollment)?;
        if authority.catalog != self.catalog || authority.domains != self.domains {
            return Err(invalid(
                "inventory does not match its trusted placement authority",
            ));
        }
        let placement = Placement::new(&self.keepers, authority.domains)?;
        if let Some(voters) = &self.catalog_voters
            && (!placement.roster(voters) || !voters.contains(&self.catalog))
        {
            return Err(invalid(
                "catalog voters must be three sorted keepers in distinct domains, one the catalog",
            ));
        }
        Ok(placement)
    }

    pub async fn serve(self, listener: TcpListener, stop: CancellationToken) -> io::Result<()> {
        let peer = self
            .peers
            .get(&self.keeper)
            .ok_or_else(|| invalid("missing local peer address"))?;
        let bulk = self
            .bulk
            .get(&self.keeper)
            .ok_or_else(|| invalid("missing local bulk address"))?;
        let control = TcpListener::bind(peer).await?;
        let bulk = TcpListener::bind(bulk).await?;
        let (engine, acceptors) = self.prepare(stop).await?;
        engine.serve([listener, control, bulk], acceptors).await
    }

    async fn prepare(self, stop: CancellationToken) -> io::Result<(Arc<Engine>, [TlsAcceptor; 3])> {
        let placement = self.validate()?;
        let keeper = KeeperId(self.keeper.as_u128());
        let acceptors = [
            self.tls.server_protocol(keeper, Lane::Application.alpn())?,
            self.tls.server_protocol(keeper, Lane::Control.alpn())?,
            self.tls
                .server_protocols(keeper, &[Lane::Bulk.alpn(), Lane::Replication.alpn()])?,
        ];
        let enrollment = self.enrollment()?;
        let (rpc, control, bulk, replication) = (
            Rpc::new(
                self.tls.peer_protocol(keeper, Lane::Application.alpn())?,
                self.keepers,
                Lane::Application,
            ),
            Rpc::new(
                self.tls.peer_protocol(keeper, Lane::Control.alpn())?,
                self.peers,
                Lane::Control,
            ),
            Rpc::new(
                self.tls.peer_protocol(keeper, Lane::Bulk.alpn())?,
                self.bulk.clone(),
                Lane::Bulk,
            ),
            Rpc::new(
                self.tls.peer_protocol(keeper, Lane::Replication.alpn())?,
                self.bulk,
                Lane::Replication,
            ),
        );
        let id = self.keeper;
        let registry = self.enrollment.clone();
        let (disk, recognition) = tokio::task::spawn_blocking(move || {
            let disk = Disk::open(enrollment)?;
            let recognition = incarnation::Recognition::open(&registry, id, disk.incarnation)?;
            Ok::<_, io::Error>((disk, recognition))
        })
        .await??;
        let raft_config = openraft::Config {
            heartbeat_interval: 100,
            election_timeout_min: 450,
            election_timeout_max: 900,
            max_payload_entries: super::network::MAX_PEER_ENTRIES as u64,
            snapshot_policy: SnapshotPolicy::LogsSinceLast(128),
            snapshot_max_chunk_size: SNAPSHOT_CHUNK_BYTES,
            max_in_snapshot_log_to_keep: 16,
            purge_batch_size: 16,
            // A follower asks for votes without raising its term first, so a
            // keeper that rejoins after a partition does not depose a leader.
            enable_pre_vote: Some(true),
            // A leader that cannot confirm its quorum for a lease plus an
            // election timeout yields, instead of refusing writes forever.
            quorum_loss_probe_interval: Some(1800),
            ..Default::default()
        }
        .validate()
        .map_err(io::Error::other)?;
        let timed = match (self.timed_authority.clone(), self.timed_original.clone()) {
            (Some(authority), _) => Some(authority),
            (None, Some(config)) => {
                let public_key = self.tls.public_key(keeper)?;
                Some(config.authority(keeper, &public_key, tokio::runtime::Handle::current())?)
            }
            (None, None) => None,
        };
        let timed = match timed {
            Some(authority) => {
                let data = self.data.clone();
                let stages = tokio::task::spawn_blocking(move || super::timed::Stages::open(&data))
                    .await??;
                Some(Arc::new(TimedState { authority, stages }))
            }
            None => None,
        };
        let engine = Arc::new(Engine {
            timed,
            id,
            catalog_id: self.catalog,
            catalog: (id == self.catalog && self.catalog_voters.is_none())
                .then(|| Catalog::new(disk.clone())),
            catalog_stream: self
                .catalog_voters
                .map(|voters| catalog_stream::CatalogStream::new(voters, self.catalog)),
            disk,
            recognition,
            rpc,
            control,
            bulk,
            replication,
            replication_ingress: Arc::default(),
            placement,
            raft_config: Arc::new(raft_config),
            readers: self.readers.into_iter().collect(),
            writers: self.writers.into_iter().collect(),
            administrators: self.administrators.into_iter().collect(),
            openings: Mutex::default(),
            detached_pins: Default::default(),
            quarantined: parking_lot::RwLock::default(),
            max_streams: self.max_streams,
            repair_after: Duration::from_secs(self.repair_after_secs),
            led_since: parking_lot::Mutex::default(),
            learners_seen: parking_lot::Mutex::default(),
            groups: Mutex::default(),
            deletions: parking_lot::Mutex::default(),
            deleted: parking_lot::RwLock::default(),
            parked: parking_lot::RwLock::default(),
            closed_states: parking_lot::Mutex::default(),
            activity: parking_lot::Mutex::default(),
            liveness: parking_lot::Mutex::default(),
            repairs: parking_lot::Mutex::default(),
            preferred: parking_lot::Mutex::default(),
            park_after: Duration::from_secs(self.park_after_secs),
            snapshot_rate: super::network::RateLimiter::new(self.snapshot_send_bytes_per_second),
            retire_now: Arc::default(),
            stop: stop.child_token(),
            #[cfg(test)]
            reject_append: Default::default(),
            #[cfg(test)]
            read_delay: Default::default(),
            #[cfg(test)]
            scoped_reads: Default::default(),
            #[cfg(test)]
            busy_replies: Default::default(),
            #[cfg(test)]
            fail_repairs: Default::default(),
            #[cfg(test)]
            repair_attempts: Default::default(),
        });
        Ok((engine, acceptors))
    }
}

struct TimedState {
    authority: super::timed::TimedAuthority,
    stages: super::timed::Stages,
}

struct Engine {
    timed: Option<Arc<TimedState>>,
    id: uuid::Uuid,
    catalog_id: uuid::Uuid,
    catalog: Option<Catalog>,
    catalog_stream: Option<catalog_stream::CatalogStream>,
    disk: Disk,
    /// The media incarnations of this keeper and its peers.
    recognition: incarnation::Recognition,
    rpc: Rpc,
    control: Rpc,
    bulk: Rpc,
    replication: Rpc,
    replication_ingress: Arc<ReplicationIngress>,
    placement: Placement,
    raft_config: Arc<openraft::Config>,
    readers: HashSet<String>,
    writers: HashSet<String>,
    administrators: HashSet<String>,
    openings: Mutex<BTreeMap<StreamId, Arc<Mutex<()>>>>,
    detached_pins: parking_lot::Mutex<BTreeMap<(StreamId, u64), Weak<()>>>,
    quarantined: parking_lot::RwLock<HashSet<StreamId>>,
    max_streams: usize,
    repair_after: Duration,
    /// The term and time from which this keeper has led each stream.
    led_since: parking_lot::Mutex<HashMap<StreamId, (u64, Instant)>>,
    /// When the leader first saw each learner of each stream it leads.
    learners_seen: parking_lot::Mutex<HashMap<(StreamId, NodeId), Instant>>,
    groups: Mutex<BTreeMap<StreamId, Arc<Group>>>,
    deletions: parking_lot::Mutex<HashMap<StreamId, Instant>>,
    /// Deleted streams whose groups this keeper closed. Clients are answered
    /// `Deleted` and peers are refused instead of reopening the group.
    deleted: parking_lot::RwLock<HashSet<StreamId>>,
    /// Idle streams whose groups this keeper closed until the next request,
    /// and when each parked.
    parked: parking_lot::RwLock<HashMap<StreamId, Instant>>,
    /// State machines of parked and deleted groups, kept so the reaper
    /// cannot delete what only they reference.
    closed_states: parking_lot::Mutex<HashMap<StreamId, StateMachine>>,
    /// The last log index of each led stream and when it last changed.
    activity: parking_lot::Mutex<HashMap<StreamId, (Option<u64>, Instant)>>,
    /// When each other keeper last answered a ping, and what it reported.
    liveness: parking_lot::Mutex<liveness::Liveness>,
    repairs: parking_lot::Mutex<repair::RepairQueue>,
    /// The failure domain each stream's writer asked its leader to be in.
    /// Every voter keeps it, so whichever voter leads restores it.
    preferred: parking_lot::Mutex<HashMap<StreamId, String>>,
    park_after: Duration,
    snapshot_rate: Arc<super::network::RateLimiter>,
    /// Wakes the repair loop when a peer excluded one of this keeper's
    /// replicas, so a removed copy retires at once.
    retire_now: Arc<tokio::sync::Notify>,
    stop: CancellationToken,
    #[cfg(test)]
    reject_append: parking_lot::RwLock<Option<tests::RejectAppend>>,
    #[cfg(test)]
    read_delay: std::sync::atomic::AtomicU64,
    #[cfg(test)]
    scoped_reads: std::sync::atomic::AtomicU64,
    #[cfg(test)]
    busy_replies: std::sync::atomic::AtomicU64,
    #[cfg(test)]
    fail_repairs: parking_lot::RwLock<HashSet<StreamId>>,
    #[cfg(test)]
    repair_attempts: parking_lot::Mutex<HashMap<StreamId, u32>>,
}

enum Identity {
    Keeper(NodeId),
    Client(journal_contract::Identity),
}

impl Engine {
    async fn serve(
        self: Arc<Self>,
        listeners: [TcpListener; 3],
        acceptors: [TlsAcceptor; 3],
    ) -> io::Result<()> {
        let mut sockets = JoinSet::new();
        let result = async {
            for genesis in self.disk.streams() {
                if self
                    .disk
                    .ownership(genesis.stream)
                    .is_some_and(|owner| owner.generation().is_none())
                {
                    continue;
                }
                if let Err(error) = self.group(genesis.clone()).await {
                    if !self.disk.healthy() {
                        return Err(error);
                    }
                    // Past the stream limit a replica opens on its first
                    // request instead of being quarantined. Until then no
                    // state machine pins its snapshot's objects and
                    // segments, so the reaper must leave them.
                    if error.kind() == io::ErrorKind::QuotaExceeded {
                        self.disk.protect_objects(genesis.stream);
                    } else {
                        self.quarantine(genesis.stream, &error);
                    }
                }
            }
            self.disk.enable_reaping();
            let repairing = self.clone();
            sockets.spawn(async move {
                repairing.repair_loop().await;
                Ok(())
            });
            let pinging = self.clone();
            sockets.spawn(async move {
                pinging.liveness_loop().await;
                Ok(())
            });
            if self.catalog_stream.is_some() {
                let tending = self.clone();
                sockets.spawn(async move {
                    tending.tend_catalog_stream().await;
                    Ok(())
                });
            }
            tokio::spawn(super::metrics::report(
                self.id,
                Duration::from_secs(5),
                self.stop.clone(),
            ));
            let engine = self.clone();
            let stop = self.stop.clone();
            sockets.spawn(async move {
                let mut schedule = tokio::time::interval(Duration::from_millis(50));
                schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
                let mut cursor = None;
                let mut ticks = 0u64;
                loop {
                    tokio::select! {
                        _ = stop.cancelled() => return Ok(()),
                        _ = schedule.tick() => {
                            ticks += 1;
                            if ticks % 20 == 0 {
                                engine.close_settled_deletions().await;
                            }
                            if let Err(error) = engine.disk.reap_objects().await {
                                eprintln!("logkeeper object cleanup deferred: {error}");
                            }
                            if let Err(error) = engine.reclaim_detached(&mut cursor).await {
                                eprintln!("logkeeper replica cleanup deferred: {error}");
                            }
                        },
                    }
                }
            });
            for ((listener, acceptor), (lane, capacity)) in
                listeners.into_iter().zip(acceptors).zip([
                    (Lane::Application, MAX_CLIENT_CONNECTIONS),
                    (Lane::Control, 0),
                    (Lane::Bulk, MAX_BULK_CONNECTIONS),
                ])
            {
                let engine = self.clone();
                sockets
                    .spawn(async move { engine.listen(listener, acceptor, lane, capacity).await });
            }
            tokio::select! {
                _ = self.stop.cancelled() => Ok(()),
                result = sockets.join_next() => result.expect("keeper has listeners")?,
            }
        }
        .await;
        self.stop.cancel();
        self.disk.disable_reaping();
        self.evict_leaders(Duration::from_secs(3)).await;
        sockets.shutdown().await;
        for group in std::mem::take(&mut *self.groups.lock().await).into_values() {
            let _ = group.raft.shutdown().await;
            group.state.shutdown().await;
        }
        let shutdown = self.disk.shutdown().await;
        result.and(shutdown)
    }

    /// Hands every stream this keeper leads to a caught-up voter before a
    /// graceful shutdown, so its streams elect no new leader after a lease
    /// expires. Waits at most `limit` for leadership to move.
    async fn evict_leaders(&self, limit: Duration) {
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let mut leading = Vec::new();
        for group in groups {
            let metrics = group.raft.metrics().borrow_watched().clone();
            if metrics.state != openraft::ServerState::Leader {
                continue;
            }
            let last = metrics.last_log_index;
            let target = metrics.replication.as_ref().and_then(|progress| {
                progress
                    .iter()
                    .filter(|(id, matched)| {
                        **id != self.id.as_u128() && matched.map(|log| log.index) == last
                    })
                    .map(|(id, _)| *id)
                    .next()
            });
            if let Some(target) = target
                && group.raft.trigger().transfer_leader(target).await.is_ok()
            {
                leading.push(group);
            }
        }
        let _ = timeout(limit, async {
            for group in leading {
                let mut metrics = group.raft.metrics();
                while metrics.borrow_watched().state == openraft::ServerState::Leader {
                    if metrics.changed().await.is_err() {
                        break;
                    }
                }
            }
        })
        .await;
    }

    fn quarantine(&self, stream: StreamId, error: &io::Error) {
        self.disk.protect_objects(stream);
        if self.quarantined.write().insert(stream) {
            eprintln!("logkeeper quarantined stream {stream:?}: {error}");
        }
    }

    fn require_media(&self) -> io::Result<()> {
        if self.disk.healthy() {
            Ok(())
        } else {
            Err(invalid("keeper media is unavailable"))
        }
    }

    /// The opening lock of `stream`, which takes one of the keeper's
    /// `max_streams` slots. A slot whose group is closed and that no caller
    /// holds is released when the keeper reaches its limit, so deleted and
    /// retired streams do not count.
    async fn opening(&self, stream: StreamId) -> io::Result<Arc<Mutex<()>>> {
        let mut openings = self.openings.lock().await;
        if openings.len() >= self.max_streams && !openings.contains_key(&stream) {
            if let Ok(groups) = self.groups.try_lock() {
                openings.retain(|id, slot| groups.contains_key(id) || Arc::strong_count(slot) > 1);
            }
            if openings.len() >= self.max_streams {
                return Err(io::Error::new(
                    io::ErrorKind::QuotaExceeded,
                    "keeper stream limit reached",
                ));
            }
        }
        Ok(openings.entry(stream).or_default().clone())
    }

    /// Closes the groups of deleted streams once the deletion is applied on
    /// this replica, replicated to every voter it can see, and older than
    /// `DELETED_GROUP_GRACE`. Later requests are answered `Deleted` without
    /// reopening the group.
    async fn close_settled_deletions(&self) {
        let groups = self
            .groups
            .lock()
            .await
            .iter()
            .map(|(stream, group)| (*stream, group.clone()))
            .collect::<Vec<_>>();
        let now = Instant::now();
        let mut closing = Vec::new();
        {
            let mut seen = self.deletions.lock();
            seen.retain(|stream, _| groups.iter().any(|(open, _)| open == stream));
            for (stream, group) in &groups {
                if !matches!(group.state.head(), Err(JournalError::Deleted)) || !group.settled() {
                    seen.remove(stream);
                    continue;
                }
                let since = *seen.entry(*stream).or_insert(now);
                if now.duration_since(since) >= DELETED_GROUP_GRACE
                    && now.duration_since(*group.used.lock()) >= DELETED_GROUP_GRACE
                {
                    closing.push(*stream);
                }
            }
            for stream in &closing {
                seen.remove(stream);
            }
        }
        for stream in closing {
            // Marked first: a request that races the close is refused
            // rather than reopening the group.
            self.deleted.write().insert(stream);
            self.close_retaining(stream, || ()).await;
            self.preferred.lock().remove(&stream);
        }
    }

    async fn group(&self, genesis: Genesis) -> io::Result<Arc<Group>> {
        self.require_media()?;
        if self.quarantined.read().contains(&genesis.stream) {
            return Err(invalid("stream replica is quarantined"));
        }
        if let Some(group) = self.groups.lock().await.get(&genesis.stream).cloned() {
            return group.for_genesis(&genesis);
        }
        let opening = self.opening(genesis.stream).await?;
        let _guard = opening.lock().await;
        if let Some(group) = self.groups.lock().await.get(&genesis.stream).cloned() {
            return group.for_genesis(&genesis);
        }
        if self.quarantined.read().contains(&genesis.stream) {
            return Err(invalid("stream replica is quarantined"));
        }
        match self.disk.genesis(genesis.stream) {
            Some(previous) if previous != genesis => {
                return Err(invalid("stream genesis mismatch"));
            }
            Some(_)
                if self
                    .disk
                    .ownership(genesis.stream)
                    .is_some_and(|book| book.generation().is_some()) =>
            {
                ()
            }
            Some(_) => return Err(invalid("replica is detached")),
            None if !genesis.voters.contains(&self.id) => {
                return Err(invalid("learner has no staged ownership"));
            }
            // A genesis voter registers the stream when a peer or a
            // bootstrap names it, unless its media may have lost a replica
            // it held: see `incarnation`.
            None if !self.recognition.registers(true) => {
                return Err(invalid(if self.recognition.reused() {
                    "keeper ID was reused on new media; only staging adds its replicas"
                } else {
                    "no peer has confirmed this keeper's media incarnation yet"
                }));
            }
            None => {
                self.disk
                    .maintenance(Record::Register(genesis.clone()))
                    .await?
            }
        }
        let startup = async {
            self.disk.check_placement(genesis.stream, &self.placement)?;
            StateMachine::open(&self.disk, genesis.clone(), self.placement.clone()).await
        }
        .await;
        let state = match startup {
            // The open state machine pins what its replica references, so
            // a copy protected while it could not open no longer needs to be.
            Ok(state) => {
                self.disk.unprotect_objects(genesis.stream);
                state
            }
            Err(error) => {
                self.quarantine(genesis.stream, &error);
                return Err(error);
            }
        };
        let follower = Arc::new(FollowerAppend::default());
        let store = LogStore {
            disk: self.disk.clone(),
            stream: genesis.stream,
            state: state.clone(),
            keeper: self.id.as_u128(),
            generation: state.generation(),
            follower: follower.clone(),
        };
        let (split_vote, collisions) = watch::channel(None);
        let excluded = Arc::new(parking_lot::Mutex::new(None));
        let raft = Raft::new(
            self.id.as_u128(),
            self.raft_config.clone(),
            Network {
                snapshot_rate: self.snapshot_rate.clone(),
                control: self.control.clone(),
                bulk: self.bulk.clone(),
                replication: self.replication.clone(),
                genesis: genesis.clone(),
                state: state.clone(),
                split_vote,
                excluded: excluded.clone(),
                retire: self.retire_now.clone(),
                reincarnated: self.recognition.reincarnated_peers(),
            },
            store,
            state.clone(),
        )
        .await
        .map_err(io::Error::other)?;
        let (heads, pending_heads) = mpsc::channel(MAX_HEAD_REQUESTS);
        let group = Arc::new(Group {
            genesis,
            raft,
            state,
            membership: Mutex::new(()),
            snapshot_receive: Mutex::new(None),
            append_order: Arc::default(),
            follower,
            heads,
            writes: Arc::new(Semaphore::new(MAX_PENDING_WRITES)),
            used: parking_lot::Mutex::new(Instant::now()),
            handoff: parking_lot::Mutex::new(None),
            heard: parking_lot::Mutex::new(Instant::now()),
            excluded,
            stop: self.stop.child_token(),
        });
        self.groups
            .lock()
            .await
            .insert(group.genesis.stream, group.clone());
        // The reopened group references its snapshot and records itself,
        // and is no longer parked.
        self.closed_states.lock().remove(&group.genesis.stream);
        self.parked.write().remove(&group.genesis.stream);
        let resume = group.clone();
        let stop = group.stop.clone();
        let id = self.id.as_u128();
        tokio::spawn(async move {
            resume.resume_membership(id, stop).await;
        });
        let elector = group.clone();
        let stop = group.stop.clone();
        tokio::spawn(async move {
            elector.retry_split_elections(collisions, stop).await;
        });
        let serve = group.clone();
        let stop = group.stop.clone();
        tokio::spawn(async move {
            serve.serve_heads(pending_heads, stop).await;
        });
        Ok(group)
    }

    fn authorize(&self, identity: &Identity, request: &Request) -> io::Result<Option<String>> {
        let denied = || {
            io::Error::new(
                io::ErrorKind::PermissionDenied,
                "unauthorized journal request",
            )
        };
        match identity {
            Identity::Keeper(_)
                if matches!(
                    request,
                    Request::Locate(_)
                        | Request::KeeperStatus(_)
                        | Request::PlacementProof(_)
                        | Request::StageReplica { .. }
                        | Request::InstallReplica { .. }
                        | Request::StageRecovered { .. }
                        | Request::PreferLeader { .. }
                ) =>
            {
                Ok(None)
            }
            Identity::Keeper(id)
                if matches!(request, Request::Stage(stage)
                if stage.old.contains(&uuid::Uuid::from_u128(*id))) =>
            {
                Ok(None)
            }
            Identity::Keeper(_) => Err(denied()),
            Identity::Client(identity) => {
                let uri = identity.as_str();
                let admin = self.administrators.contains(uri);
                let writer = self.writers.contains(uri);
                let reader = self.readers.contains(uri);
                let allowed = match request {
                    Request::Locate(_)
                    | Request::KeeperStatus(_)
                    | Request::Head(_)
                    | Request::Configuration(_)
                    | Request::Read { .. }
                    | Request::ReadAt { .. } => admin || writer || reader,
                    Request::Seal { .. }
                    | Request::Append { .. }
                    | Request::AppendBatch { .. }
                    | Request::StageOriginal { .. }
                    | Request::AppendOriginal { .. }
                    | Request::PreferLeader { .. }
                    | Request::Trim { .. } => writer,
                    // An administrator may acknowledge a recovery, but only a
                    // writer may write to the stream.
                    Request::AcknowledgeRecovery(_) => writer || admin,
                    Request::ProveOriginal { .. } => admin || writer || reader,
                    Request::Stage(_)
                    | Request::StageReplica { .. }
                    | Request::InstallReplica { .. }
                    | Request::StageRecovered { .. } => false,
                    _ => admin,
                };
                if allowed {
                    Ok(Some(uri.to_owned()))
                } else {
                    Err(denied())
                }
            }
        }
    }

    async fn request(&self, identity: &Identity, request: Request) -> io::Result<Reply> {
        self.require_media()?;
        let owner = self.authorize(identity, &request)?;
        let stream = request.stream();
        if self.catalog_stream.is_some()
            && matches!(identity, Identity::Client(_))
            && catalog_stream::internal(&request)
        {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "the catalog stream is internal",
            ));
        }
        match request {
            Request::KeeperStatus(stream) => Ok(Reply::Status(self.status(stream).await)),
            Request::LocalCopy(_) => Ok(self
                .disk
                .ownership(stream)
                .and_then(|book| book.generation())
                .map(Reply::Generation)
                .unwrap_or_else(|| failure(JournalError::Unavailable))),
            Request::RetireCopy {
                authority,
                revision,
                generation,
                ..
            } => {
                self.retire_copy(stream, authority, revision, generation)
                    .await
            }
            Request::StageReplica { genesis, stage } => {
                let Identity::Keeper(id) = identity else {
                    return Err(invalid("invalid staging sender"));
                };
                self.stage_replica(uuid::Uuid::from_u128(*id), genesis, stage)
                    .await
            }
            Request::StageRecovered { genesis, stage } => {
                let Identity::Keeper(id) = identity else {
                    return Err(invalid("invalid staging sender"));
                };
                self.stage_recovered(uuid::Uuid::from_u128(*id), genesis, stage)
                    .await
            }
            Request::InstallReplica {
                genesis,
                stage,
                generation,
                through,
            } => {
                let Identity::Keeper(id) = identity else {
                    return Err(invalid("invalid installation sender"));
                };
                self.install_replica(
                    uuid::Uuid::from_u128(*id),
                    genesis,
                    stage,
                    generation,
                    through,
                )
                .await
            }
            // A leader forwards its writer's preference to the other voters,
            // which only record it.
            Request::PreferLeader { keeper, .. } if matches!(identity, Identity::Keeper(_)) => {
                self.record_preference(stream, keeper);
                Ok(Reply::Decision(Outcome::Unit))
            }
            Request::Claim(_) | Request::Locate(_) | Request::Stage(_)
                if self.catalog_stream.is_some() =>
            {
                self.serve_catalog_stream(request).await
            }
            Request::Claim(genesis) => self.catalog()?.claim(genesis, &self.placement).await,
            Request::Locate(stream) => self.catalog()?.locate(stream),
            Request::Stage(stage) => self.catalog()?.stage(stage, &self.placement).await,
            Request::Bootstrap(stream) => self.bootstrap(stream).await,
            request => {
                let group = self.groups.lock().await.get(&stream).cloned();
                let Some(group) = group else {
                    if self.deleted.read().contains(&stream) {
                        let refused = Outcome::Refused(JournalError::Deleted);
                        return Ok(match (&request, self.disk.genesis(stream)) {
                            (Request::ReadAt { .. }, Some(genesis)) => Reply::ScopedPage {
                                genesis,
                                configuration: None,
                                outcome: refused,
                            },
                            _ => Reply::Decision(refused),
                        });
                    }
                    // Reopen a parked or never opened copy; it elects a
                    // leader at once and the client retries.
                    if self.unpark(stream).await.is_some() {
                        super::metrics::count(&super::metrics::COUNTERS.unparked_by_client);
                    }
                    return Ok(Reply::Leader(None));
                };
                *group.used.lock() = Instant::now();
                if !self.disk.installed(stream) {
                    return Ok(failure(JournalError::Unavailable));
                }
                group.require_healthy()?;
                let reply = match request {
                    Request::Head(_) => Ok(group.head().await),
                    Request::PlacementProof(_) => Ok(group.proof().await),
                    Request::Configuration(_) => Ok(group.configuration().await),
                    Request::Read {
                        from,
                        limit,
                        wait_ms,
                        ..
                    } => Ok(Reply::Decision(
                        group.read(from, limit, wait_ms, Lsn(0)).await,
                    )),
                    Request::ReadAt {
                        genesis,
                        from,
                        minimum_head,
                        limit,
                        wait_ms,
                    } => {
                        #[cfg(test)]
                        {
                            use std::sync::atomic::Ordering::Relaxed;
                            self.scoped_reads.fetch_add(1, Relaxed);
                            let delay = self.read_delay.load(Relaxed);
                            if delay != 0 {
                                tokio::time::sleep(Duration::from_millis(delay)).await;
                            }
                        }
                        if genesis != group.genesis {
                            return Err(invalid("page scope differs"));
                        }
                        if !group.state.serves_applied_pages(self.id.as_u128()) {
                            return Ok(failure(JournalError::Unavailable));
                        }
                        let outcome = group.read(from, limit, wait_ms, minimum_head).await;
                        Ok(Reply::ScopedPage {
                            genesis,
                            configuration: group.state.finalized(),
                            outcome,
                        })
                    }
                    Request::Replace {
                        expected, voters, ..
                    } => self.replace(&group, expected, voters).await,
                    Request::PreferLeader { keeper, .. } => {
                        self.prefer_leader(&group, keeper).await
                    }
                    Request::Create(_) => Ok(group.write(Command::Create).await),
                    Request::Seal {
                        expected, writer, ..
                    } if !writer.is_nil() => Ok(group
                        .write(Command::Seal {
                            expected,
                            writer,
                            owner: owner.unwrap(),
                        })
                        .await),
                    Request::Append {
                        fence, at, payload, ..
                    } => {
                        if payload.len() > super::MAX_RECORD {
                            return Ok(failure(JournalError::TooLarge {
                                max: super::MAX_RECORD,
                            }));
                        }
                        Ok(group
                            .write(Command::Append {
                                fence,
                                owner: owner.unwrap(),
                                at,
                                payload,
                            })
                            .await)
                    }
                    Request::AppendBatch {
                        fence,
                        at,
                        payloads,
                        ..
                    } => {
                        if !super::state::valid_batch(&payloads) {
                            return Ok(failure(JournalError::TooLarge {
                                max: super::MAX_RECORD,
                            }));
                        }
                        Ok(group
                            .write(Command::AppendBatch {
                                fence,
                                owner: owner.unwrap(),
                                at,
                                payloads,
                            })
                            .await)
                    }
                    Request::StageOriginal {
                        revision,
                        original,
                        payload,
                        ..
                    } => {
                        self.stage_original(&group, owner.unwrap(), revision, &original, payload)
                            .await
                    }
                    Request::AppendOriginal {
                        fence,
                        evidence,
                        payload,
                        ..
                    } => {
                        self.append_original(&group, owner.unwrap(), fence, &evidence, payload)
                            .await
                    }
                    // Prove from the leader's applied state after a read
                    // barrier, so a restoring or lagging keeper never answers.
                    Request::ProveOriginal { at, .. } => {
                        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
                            return Ok(reply);
                        }
                        Ok(Reply::Decision(match group.state.timed_record(at) {
                            Ok(record) => {
                                match tokio::task::spawn_blocking(move || record.load()).await {
                                    Ok(Ok(bytes)) => Outcome::OriginalEvidence(
                                        bytes[..crate::stream::timed::EVIDENCE_BYTES].to_vec(),
                                    ),
                                    _ => Outcome::Refused(JournalError::Unavailable),
                                }
                            }
                            Err(error) => Outcome::Refused(error),
                        }))
                    }
                    Request::Trim { fence, through, .. } => Ok(group
                        .write(Command::Trim {
                            fence,
                            owner: owner.unwrap(),
                            through,
                        })
                        .await),
                    Request::Delete(_) => Ok(group.write(Command::Delete).await),
                    Request::AcknowledgeRecovery(_) => {
                        Ok(group.write(Command::AcknowledgeRecovery).await)
                    }
                    _ => Err(invalid("invalid application request")),
                }?;
                group.require_healthy()?;
                Ok(reply)
            }
        }
    }

    async fn stage_original(
        &self,
        group: &Group,
        owner: String,
        revision: u64,
        original: &[u8],
        payload: Bytes,
    ) -> io::Result<Reply> {
        use crate::stream::timed::{EVIDENCE_BYTES, MAX_TIMED_PAYLOAD, TimedOriginal};
        let refused = |error| Ok(Reply::Decision(Outcome::Refused(error)));
        let Some(timed) = self.timed.clone() else {
            return refused(JournalError::Unavailable);
        };
        let Some(clock) = timed.authority.clock.clone() else {
            return refused(JournalError::Unavailable);
        };
        let max = MAX_TIMED_PAYLOAD.min(super::MAX_RECORD - EVIDENCE_BYTES);
        if payload.len() > max {
            return refused(JournalError::TooLarge { max });
        }
        let Some(original) = TimedOriginal::decode(original).filter(|original| {
            original.stream == group.genesis.stream && original.matches(&payload)
        }) else {
            return refused(JournalError::Unavailable);
        };
        let view = match group.state.timed_view(payload.len()) {
            Ok(view) => view,
            Err(error) => return refused(error),
        };
        let mut voters = view.configuration.voters;
        voters.sort_unstable();
        if view.changing
            || view.configuration.revision != revision
            || !voters[..2].contains(&self.id)
        {
            return refused(JournalError::Unavailable);
        }
        match &view.writer {
            Some((fence, principal)) if fence.epoch == original.epoch && *principal == owner => (),
            writer => {
                return refused(JournalError::Fenced {
                    current: writer.as_ref().map_or(Epoch(0), |(fence, _)| fence.epoch),
                });
            }
        }
        if original.at.0 != view.head.0 + 1 {
            return refused(JournalError::Conflict { head: view.head });
        }
        if !view.fits {
            return refused(JournalError::Full { floor: view.floor });
        }
        let origin = super::timed::origin(original, voters, revision);
        let keeper = crate::stream::wire::KeeperId(self.id.as_u128());
        let (head, epoch) = (view.head.0, original.epoch.0);
        let sample = tokio::task::spawn_blocking(move || {
            timed.stages.stage(
                keeper,
                origin,
                &payload,
                head,
                epoch,
                &*clock,
                &*timed.authority.verifier,
            )
        })
        .await??;
        Ok(Reply::Decision(match sample {
            Some(sample) => Outcome::OriginalSample(sample.encode().to_vec()),
            None => Outcome::Refused(JournalError::Unavailable),
        }))
    }

    async fn append_original(
        &self,
        group: &Group,
        owner: String,
        fence: Fence,
        evidence: &[u8],
        payload: Bytes,
    ) -> io::Result<Reply> {
        use crate::stream::timed::{EVIDENCE_BYTES, TimedEvidence};
        let refused = |error| Ok(Reply::Decision(Outcome::Refused(error)));
        let Some(timed) = self.timed.clone() else {
            return refused(JournalError::Unavailable);
        };
        let Some(evidence) = TimedEvidence::decode(evidence) else {
            return refused(JournalError::Unavailable);
        };
        let original = evidence.origin.original;
        if original.stream != group.genesis.stream
            || original.epoch != fence.epoch
            || EVIDENCE_BYTES + payload.len() > super::MAX_RECORD
            || !original.matches(&payload)
            || evidence.proof(&*timed.authority.verifier).is_none()
        {
            return refused(JournalError::Unavailable);
        }
        // A new record must carry evidence from the current roster. A retry
        // of a committed record is compared byte for byte when it applies.
        let view = match group.state.timed_view(payload.len()) {
            Ok(view) => view,
            Err(error) => return refused(error),
        };
        if original.at > view.head
            && (view.changing
                || super::timed::origin(
                    original,
                    view.configuration.voters,
                    view.configuration.revision,
                ) != evidence.origin)
        {
            return refused(JournalError::Unavailable);
        }
        let mut record = Vec::with_capacity(EVIDENCE_BYTES + payload.len());
        record.extend_from_slice(&evidence.encode());
        record.extend_from_slice(&payload);
        Ok(group
            .write(Command::AppendOriginal {
                fence,
                owner,
                at: original.at,
                record: Bytes::from(record),
            })
            .await)
    }

    fn catalog(&self) -> io::Result<&Catalog> {
        self.catalog
            .as_ref()
            .ok_or_else(|| invalid("request requires the catalog keeper"))
    }

    async fn catalog_request(&self, request: Request) -> io::Result<Reply> {
        if self.catalog_stream.is_some() {
            self.ask_catalog_stream(request).await
        } else if let Some(catalog) = &self.catalog {
            match request {
                Request::Locate(stream) => catalog.locate(stream),
                Request::Stage(stage) => catalog.stage(stage, &self.placement).await,
                _ => Err(invalid("invalid internal catalog request")),
            }
        } else {
            self.rpc
                .call(self.catalog_id, Frame::Client(request), REQUEST_TIMEOUT)
                .await
        }
    }

    async fn bootstrap(&self, stream: StreamId) -> io::Result<Reply> {
        let Reply::Catalog(genesis, _) = self.catalog_request(Request::Locate(stream)).await?
        else {
            return Ok(failure(JournalError::NotFound));
        };
        if !genesis.voters.contains(&self.id) {
            return Err(invalid("keeper is outside the genesis configuration"));
        }
        if self.deleted.read().contains(&stream) {
            return Ok(failure(JournalError::Deleted));
        }
        let members = self.nodes(genesis.voters);
        if self.disk.genesis(stream).is_none() {
            self.check_identity().await;
        }
        let group = self.group(genesis).await?;
        let initialized = group.raft.initialize(members).await;
        group.require_healthy()?;
        match initialized {
            Ok(()) | Err(RaftError::APIError(InitializeError::NotAllowed(_))) => {
                Ok(Reply::Decision(Outcome::Unit))
            }
            Err(error) => Err(io::Error::other(error)),
        }
    }

    fn nodes(&self, voters: [uuid::Uuid; 3]) -> BTreeMap<NodeId, BasicNode> {
        voters
            .into_iter()
            .map(|id| {
                (
                    id.as_u128(),
                    BasicNode::new(self.rpc.keepers()[&id].to_string()),
                )
            })
            .collect()
    }
}

struct Group {
    genesis: Genesis,
    raft: Raft,
    state: StateMachine,
    membership: Mutex<()>,
    snapshot_receive: Mutex<Option<ingress::Incoming>>,
    append_order: Arc<Mutex<()>>,
    follower: Arc<FollowerAppend>,
    heads: mpsc::Sender<oneshot::Sender<Reply>>,
    writes: Arc<Semaphore>,
    /// When a request last reached this group.
    used: parking_lot::Mutex<Instant>,
    /// When this replica last handed leadership away or was handed it. A
    /// leader refuses another hand-off for a minute after either.
    pub(super) handoff: parking_lot::Mutex<Option<Instant>>,
    /// When this replica last received an append from a leader.
    heard: parking_lot::Mutex<Instant>,
    /// The last peer that refused this replica as outside its placement.
    excluded: Arc<parking_lot::Mutex<Option<uuid::Uuid>>>,
    stop: CancellationToken,
}

impl Group {
    fn for_genesis(self: Arc<Self>, genesis: &Genesis) -> io::Result<Arc<Self>> {
        if &self.genesis != genesis {
            return Err(invalid("stream genesis mismatch"));
        }
        self.require_healthy()?;
        Ok(self)
    }

    /// Hands leadership to `target`, a voter that has matched the whole log,
    /// at most once a minute so a moving writer cannot cause churn.
    async fn prefer_leader(&self, target: uuid::Uuid) -> Reply {
        let metrics = self.raft.metrics().borrow_watched().clone();
        if metrics.state != openraft::ServerState::Leader {
            return leader_reply(metrics.current_leader);
        }
        let matched = metrics
            .replication
            .as_ref()
            .and_then(|progress| progress.get(&target.as_u128()).copied().flatten())
            .map(|log| log.index);
        let recent = self
            .handoff
            .lock()
            .is_some_and(|at| at.elapsed() < LEADER_HOLD_DOWN);
        if target.as_u128() != metrics.id
            && matched.is_some()
            && matched == metrics.last_log_index
            && !recent
            && self
                .raft
                .trigger()
                .transfer_leader(target.as_u128())
                .await
                .is_ok()
        {
            *self.handoff.lock() = Some(Instant::now());
        }
        Reply::Decision(Outcome::Unit)
    }

    /// Whether this replica has applied its whole log and, when it leads,
    /// every voter has matched it.
    fn settled(&self) -> bool {
        self.settled_except(&|_| false)
    }

    /// Whether this replica is settled, leaving out the voters `ignored`
    /// names, such as followers on dead keepers.
    fn settled_except(&self, ignored: &dyn Fn(NodeId) -> bool) -> bool {
        let metrics = self.raft.metrics().borrow_watched().clone();
        let last = metrics.last_log_index;
        metrics.last_applied.map(|applied| applied.index) == last
            && metrics.replication.as_ref().is_none_or(|progress| {
                progress
                    .iter()
                    .all(|(id, matched)| ignored(*id) || matched.map(|id| id.index) == last)
            })
    }

    fn require_healthy(&self) -> io::Result<()> {
        if self.state.healthy() {
            Ok(())
        } else {
            Err(invalid("stream replica is quarantined"))
        }
    }

    async fn retry_split_elections(
        &self,
        mut collisions: watch::Receiver<Option<Vote>>,
        stop: CancellationToken,
    ) {
        let mut metrics = self.raft.server_metrics();
        loop {
            let collision = *collisions.borrow_and_update();
            let candidate = {
                let current = metrics.borrow_and_update();
                current.state == openraft::ServerState::Candidate && collision == Some(current.vote)
            };
            // Fresh jitter lets split same-term candidacies escape repeated
            // tick alignment.
            let retry = async {
                if candidate {
                    let random = uuid::Uuid::new_v4().as_u128() as u64;
                    tokio::time::sleep(Duration::from_millis(220 + random % 200)).await;
                } else {
                    std::future::pending::<()>().await;
                }
            };
            tokio::select! {
                _ = stop.cancelled() => return,
                changed = metrics.changed() => if changed.is_err() { return; },
                changed = collisions.changed() => if changed.is_err() { return; },
                _ = retry => {
                    if !self.state.healthy() || self.raft.trigger().elect(false).await.is_err() { return; }
                }
            }
        }
    }

    async fn write(&self, command: Command) -> Reply {
        use super::metrics::{COUNTERS, count};
        if self.require_healthy().is_err() {
            count(&COUNTERS.write_unhealthy);
            return failure(JournalError::Unavailable);
        }
        let Ok(permit) = self.writes.clone().try_acquire_owned() else {
            count(&COUNTERS.write_pending);
            return failure(JournalError::Unavailable);
        };
        let ticket = uuid::Uuid::new_v4();
        let space = match self
            .state
            .reserve_command(&command, ticket, MAX_LOG_SUFFIX as usize)
        {
            Ok(space) => space,
            Err(storage::Admission::FullSuffix) => {
                count(&COUNTERS.write_full_suffix);
                self.request_covered_purge().await;
                return failure(JournalError::Unavailable);
            }
            Err(storage::Admission::Space) => {
                count(&COUNTERS.write_space);
                return failure(JournalError::Unavailable);
            }
        };
        let raft = self.raft.clone();
        // The proposal owns its reservation even when the caller drops the
        // request or times out. The WAL settles it as it publishes the slot.
        let proposal = tokio::spawn(async move {
            let (_permit, _space) = (permit, space);
            let (responder, response) = ProgressResponder::complete_only();
            if let Err(error) = raft
                .client_write_ff(
                    Command::Admitted(ticket, Box::new(command)),
                    Some(responder),
                )
                .await
            {
                super::metrics::sample("write.proposal_failed", || format!("{error:?}"));
                count(&COUNTERS.write_proposal);
                return failure(JournalError::Unavailable);
            }
            match response.await {
                Ok(Ok(response)) => Reply::Decision(response.data),
                Ok(Err(ClientWriteError::ForwardToLeader(leader))) => {
                    leader_reply(leader.leader_id)
                }
                other => {
                    super::metrics::sample("write.proposal_failed", || format!("{other:?}"));
                    count(&COUNTERS.write_proposal);
                    failure(JournalError::Unavailable)
                }
            }
        });
        timeout(REQUEST_TIMEOUT, proposal)
            .await
            .ok()
            .and_then(Result::ok)
            .unwrap_or_else(|| {
                count(&COUNTERS.write_timeout);
                failure(JournalError::Unavailable)
            })
    }

    async fn request_covered_purge(&self) {
        if let Some(covered) = self.state.covered() {
            let _ = self.raft.trigger().purge_log(covered.index).await;
        }
        let _ = self.raft.trigger().snapshot().await;
    }

    async fn head(&self) -> Reply {
        let (send, receive) = oneshot::channel();
        if self.heads.try_send(send).is_err() {
            super::metrics::count(&super::metrics::COUNTERS.head_queue);
        } else if let Ok(Ok(reply)) = timeout(REQUEST_TIMEOUT, receive).await {
            return reply;
        } else {
            super::metrics::count(&super::metrics::COUNTERS.head_timeout);
        }
        failure(JournalError::Unavailable)
    }

    async fn serve_heads(
        &self,
        mut pending: mpsc::Receiver<oneshot::Sender<Reply>>,
        stop: CancellationToken,
    ) {
        loop {
            let first = tokio::select! {
                _ = stop.cancelled() => return,
                first = pending.recv() => first,
            };
            let Some(first) = first else { return };
            let mut batch = vec![first];
            while batch.len() < MAX_HEAD_REQUESTS {
                let Ok(waiter) = pending.try_recv() else {
                    break;
                };
                batch.push(waiter);
            }
            // Every caller in this batch arrived before the quorum round opened.
            let reply = tokio::select! {
                _ = stop.cancelled() => return,
                result = self.barrier(Instant::now() + REQUEST_TIMEOUT) => match result {
                    Ok(()) => Reply::Decision(self.state.head().map(Outcome::At).into()),
                    Err(reply) => reply,
                },
            };
            for caller in batch {
                let _ = caller.send(reply.clone());
            }
        }
    }

    async fn barrier(&self, deadline: Instant) -> Result<(), Reply> {
        if self.require_healthy().is_err() {
            return Err(failure(JournalError::Unavailable));
        }
        match timeout_at(
            deadline,
            self.raft.ensure_linearizable(ReadPolicy::ReadIndex),
        )
        .await
        {
            Ok(Ok(_)) => Ok(()),
            Ok(Err(error)) => Err(leader_reply(
                error
                    .forward_to_leader()
                    .and_then(|leader| leader.leader_id),
            )),
            Err(_) => Err(failure(JournalError::Unavailable)),
        }
    }

    async fn read(&self, from: Lsn, limit: usize, wait_ms: u32, minimum_head: Lsn) -> Outcome {
        let mut changed = self.state.subscribe();
        let deadline =
            Instant::now() + Duration::from_millis(u64::from(wait_ms)).min(REQUEST_TIMEOUT);
        loop {
            if self.state.head().is_ok_and(|head| head < minimum_head) {
                if timeout_at(deadline, changed.changed()).await.is_err() {
                    return Outcome::Refused(JournalError::Unavailable);
                }
                continue;
            }
            let page = self.state.page(from, limit).await;
            if !page
                .as_ref()
                .is_ok_and(|page| limit != 0 && from > page.head)
                || timeout_at(deadline, changed.changed()).await.is_err()
            {
                return page.map(Outcome::Page).into();
            }
        }
    }
}

fn leader_reply(id: Option<NodeId>) -> Reply {
    Reply::Leader(id.map(uuid::Uuid::from_u128))
}

fn failure(error: JournalError) -> Reply {
    Reply::Decision(Outcome::Refused(error))
}
