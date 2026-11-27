mod admin;
mod admission;
mod bundle;
mod catalog_stream;
mod certify;
mod compaction;
mod drain;
mod incarnation;
mod ingress;
mod lease;
mod liveness;
mod offload;
mod park;
mod recovery;
mod repair;
mod replacement;
mod replicas;
mod retirement;
mod scrub;
#[cfg(test)]
mod tests;
pub(super) mod tls;

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
use tokio_util::sync::CancellationToken;

use super::{
    Credentials, Domains, Fence, Genesis, Keepers, NodeId, Raft, Vote,
    catalog::Catalog,
    invalid,
    network::{Lane, Network, Reply, Request, Rpc},
    placement::Placement,
    state::{Command, Outcome},
    storage::{self, Authority, Disk, Enrollment, FollowerAppend, LogStore, Record, StateMachine},
};
use crate::server::durability::SyncMode;
use crate::stream::consensus::Voters;
use crate::stream::{transport, wire::KeeperId};
use admission::ReplicationIngress;
pub use offload::OffloadStatus;
pub use recovery::{Recovery, RecoveryReport};
pub use retirement::FenceProof;

const REQUEST_TIMEOUT: Duration = Duration::from_secs(5);
const MAX_HEAD_REQUESTS: usize = 256;
const MAX_PENDING_WRITES: usize = 16;
const MAX_LOG_SUFFIX: u64 = 512;
/// The least time between two leadership hand-offs of one stream.
#[cfg(not(test))]
const LEADER_HOLD_DOWN: Duration = Duration::from_secs(60);
#[cfg(test)]
const LEADER_HOLD_DOWN: Duration = Duration::from_secs(4);
/// How long an open copy must have been idle before a new stream past the
/// stream limit closes it, unless the park delay is shorter.
const EVICT_AFTER: Duration = Duration::from_secs(30);

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

fn default_scrub_bytes_per_second() -> u64 {
    scrub::DEFAULT_BYTES_PER_SECOND
}

fn default_snapshot_send_bytes_per_second() -> u64 {
    64 * 1024 * 1024
}

fn default_async_append() -> bool {
    true
}

fn default_lease_millis() -> u64 {
    30_000
}

fn default_lease_drift_margin_millis() -> u64 {
    3_000
}

fn default_admin_listen() -> SocketAddr {
    SocketAddr::from(([127, 0, 0, 1], 9100))
}

/// Configuration for the separate operational HTTP/mTLS admin listener.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdminConfig {
    /// Address to bind the admin HTTP listener on. Defaults to `127.0.0.1:9100`.
    #[serde(default = "default_admin_listen")]
    pub listen: SocketAddr,
    /// Require mutual TLS using the keeper's credentials and configured
    /// `administrators` principals, or other keepers of this cluster.
    /// Plain HTTP (default) requires a loopback bind address.
    #[serde(default)]
    pub mtls: bool,
    /// The admin listeners of the other keepers, which
    /// `logkeeper keeper debug-bundle` collects from: `IP:port` or
    /// `name:port`, resolved when the bundle is collected.
    #[serde(default)]
    pub cluster: BTreeMap<uuid::Uuid, super::Address>,
    /// Client URI principals authorized for metrics and health over mTLS.
    #[serde(default)]
    pub metrics_readers: Vec<String>,
    /// Optional plain HTTP endpoint for node-local liveness and readiness.
    #[serde(default)]
    pub probe_listen: Option<SocketAddr>,
}

/// How long a keeper keeps retrying a listening port that is in use.
const BIND_RETRY: Duration = Duration::from_secs(5);

/// Binds a keeper's fixed listening port, retrying while it is in use. The
/// listener already reuses addresses in TIME_WAIT; a port can still be held
/// for a moment by an outgoing connection that drew it from the ephemeral
/// range after the keeper's previous run released it, as test keepers
/// restarted next to other tests' clients do.
pub(in crate::stream::consensus) async fn bind_listener(
    address: std::net::SocketAddr,
) -> io::Result<TcpListener> {
    let end = tokio::time::Instant::now() + BIND_RETRY;
    let mut delay = Duration::from_millis(10);
    loop {
        match TcpListener::bind(address).await {
            Err(error)
                if error.kind() == io::ErrorKind::AddrInUse
                    && tokio::time::Instant::now() + delay < end =>
            {
                tokio::time::sleep(delay).await;
                delay = (delay * 2).min(Duration::from_millis(250));
            }
            result => return result,
        }
    }
}

/// Installed, authenticated keeper inventory and local service settings.
/// `Config::read` ignores unknown top-level fields with a warning, so a
/// configuration may name a setting of a newer release before its binary.
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
    /// Retired keeper identities kept in the inventory so historical stream
    /// records remain valid while repair moves streams off them.
    #[serde(default)]
    pub retired: BTreeSet<uuid::Uuid>,
    pub enrollment: PathBuf,
    pub catalog: uuid::Uuid,
    /// Three keepers in distinct failure domains that host the catalog as a
    /// consensus stream of its own. Without them `catalog` alone holds it.
    /// `catalog` must be one of them: it seeds the replicated catalog with
    /// its single-keeper entries once.
    #[serde(default)]
    pub catalog_voters: Option<[uuid::Uuid; 3]>,
    /// Lets `catalog` alone hold the catalog, without `catalog_voters`. For
    /// development only: production replicates the catalog, which is the
    /// configuration authority every keeper's lease depends on.
    #[serde(default)]
    pub allow_single_catalog: bool,
    /// How long a liveness lease from the catalog lasts. A keeper whose
    /// lease lapses stops leading and serving, and an operator recovery
    /// waits this long plus the drift margin before the recovered
    /// configuration serves. Configure the same value on every keeper.
    #[serde(default = "default_lease_millis")]
    pub lease_millis: u64,
    /// How much shorter than the lease its holder counts it, to cover clock
    /// rate drift between keepers. Positive and below half the lease.
    #[serde(default = "default_lease_drift_margin_millis")]
    pub lease_drift_margin_millis: u64,
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
    /// How fast the background scrubber reads back retained slices and
    /// snapshots to check them, in bytes per second; 0 disables it.
    #[serde(default = "default_scrub_bytes_per_second")]
    pub scrub_bytes_per_second: u64,
    /// A leader replicates its own appends while its WAL write of them is
    /// still in flight, and counts itself toward commit once it lands.
    #[serde(default = "default_async_append")]
    pub async_append: bool,
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
    /// Structured log format (`human` by default, or `json`).
    #[serde(default)]
    pub log_format: super::logging::LogFormat,
    /// Optional operational HTTP/mTLS admin listener for `/metrics`, `/live`,
    /// `/ready`, `/safe-to-stop`, and `/problems`.
    #[serde(default)]
    pub admin: Option<AdminConfig>,
    /// Continuous offload of committed records to object storage. Every
    /// keeper of a cluster names the same store.
    #[serde(default)]
    pub offload: Option<super::OffloadConfig>,
}

impl Config {
    pub fn read(path: &Path) -> io::Result<Self> {
        Self::from_json_slice(&std::fs::read(path)?)
    }

    /// Parses keeper JSON configuration, warning on unknown top-level fields
    /// instead of refusing so config rollouts can precede binary upgrades.
    pub fn from_json_slice(bytes: &[u8]) -> io::Result<Self> {
        let (config, warnings) = Self::from_json_slice_with_warnings(bytes)?;
        for field in warnings {
            eprintln!("logkeeper warning: ignoring unknown keeper config field {field:?}");
        }
        Ok(config)
    }

    /// Parses keeper JSON configuration and names the unknown top-level
    /// fields it ignored. Fields inside nested settings stay strict.
    pub fn from_json_slice_with_warnings(bytes: &[u8]) -> io::Result<(Self, Vec<String>)> {
        let mut value: serde_json::Value = serde_json::from_slice(bytes)?;
        let mut warnings = Vec::new();
        loop {
            let error = match serde_json::from_value::<Self>(value.clone()) {
                Ok(config) => return Ok((config, warnings)),
                Err(error) => error,
            };
            // `deny_unknown_fields` names the first unknown field it meets.
            let unknown = error
                .to_string()
                .strip_prefix("unknown field `")
                .and_then(|rest| rest.split_once('`'))
                .map(|(field, _)| field.to_owned());
            let removed = match (unknown, value.as_object_mut()) {
                (Some(field), Some(object)) => object.remove(&field).map(|_| field),
                _ => None,
            };
            match removed {
                Some(field) => warnings.push(field),
                None => return Err(error.into()),
            }
        }
    }

    pub fn initialize(&self) -> io::Result<()> {
        self.validate()?;
        self.tls
            .peer_protocol(KeeperId(self.keeper.as_u128()), Lane::Control.alpn())?;
        self.enrollment()?.initialize()
    }

    /// Inspects every stream (or one stream when `filter` is `Some`) in this
    /// stopped keeper's data directory strictly read-only.
    pub fn inspect(&self, filter: Option<StreamId>) -> io::Result<storage::InspectReport> {
        let placement = self.validate()?;
        let enrollment = self.enrollment()?;
        storage::inspect(enrollment, &placement, filter)
    }

    /// Walks every WAL segment frame CRC, checkpoint digest, and running hash
    /// chain against the trusted boundary slots on this stopped keeper.
    pub fn verify(&self) -> io::Result<storage::VerifyReport> {
        self.validate()?;
        let enrollment = self.enrollment()?;
        storage::verify(enrollment)
    }

    /// Dumps segment `segment_id` from this stopped keeper's WAL directory.
    pub fn dump_segment(
        &self,
        segment_id: u64,
        limit: Option<usize>,
    ) -> io::Result<storage::SegmentDump> {
        self.validate()?;
        let enrollment = self.enrollment()?;
        storage::dump_segment_for_keeper(enrollment, segment_id, limit)
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

    /// Offline operator command that clears a durable quarantine marker in the
    /// enrollment registry for `stream` on this stopped keeper.
    pub fn clear_quarantine(&self, stream: StreamId) -> io::Result<bool> {
        self.validate()?;
        self.tls
            .peer_protocol(KeeperId(self.keeper.as_u128()), Lane::Control.alpn())?;
        let enrollment = self.enrollment()?;
        let _lock = enrollment.lock_offline()?;
        enrollment.quarantine_store()?.clear(stream)
    }

    /// Offline operator command that walks past damaged WAL spans, durably
    /// quarantines every stream with slices in a damaged span, and publishes a
    /// clean checkpoint so unaffected streams can boot and serve.
    pub fn salvage(&self) -> io::Result<storage::SalvageReport> {
        self.validate()?;
        self.tls
            .peer_protocol(KeeperId(self.keeper.as_u128()), Lane::Control.alpn())?;
        let enrollment = self.enrollment()?;
        Disk::salvage(enrollment)
    }

    /// Every path that writes this keeper's media opens its enrollment
    /// first, so installing the sync mode here covers them all.
    fn enrollment(&self) -> io::Result<Enrollment> {
        use sha2::{Digest, Sha256};

        let digest = Sha256::digest(std::fs::read(&self.tls.certificate)?).into();
        self.enrollment_with_certificate_digest(digest)
    }

    fn enrollment_with_certificate_digest(&self, digest: [u8; 32]) -> io::Result<Enrollment> {
        self.sync_mode.install();
        Enrollment::authorized(
            &self.enrollment,
            &self.data,
            self.keeper,
            self.catalog,
            &self.domains[&self.keeper],
            digest,
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
        if authority.catalog != self.catalog
            || authority.domains != self.domains
            || authority.retired != self.retired
        {
            return Err(invalid(
                "inventory does not match its trusted placement authority",
            ));
        }
        let placement = Placement::new(&self.keepers, authority.domains, authority.retired)?;
        if placement.is_retired(self.catalog) {
            return Err(invalid("catalog keeper cannot be retired"));
        }
        if !super::decisions::lease_bounds(self.lease_millis, self.lease_drift_margin_millis) {
            return Err(invalid(
                "lease_drift_margin_millis must be positive and below half of lease_millis",
            ));
        }
        if self.catalog_voters.is_none() && !self.allow_single_catalog {
            return Err(invalid(
                "production keepers replicate the catalog: name catalog_voters, or set \
                 allow_single_catalog for a development cluster",
            ));
        }
        if let Some(voters) = &self.catalog_voters
            && (!placement.structural_roster(&Voters::from(*voters))
                || !voters.contains(&self.catalog))
        {
            return Err(invalid(
                "catalog voters must be three sorted keepers in distinct domains, one the catalog",
            ));
        }
        if let Some(admin) = &self.admin {
            if !admin.mtls && !admin.listen.ip().is_loopback() {
                return Err(invalid(
                    "plain HTTP admin listener must bind to a loopback address; enable mtls for non-loopback addresses",
                ));
            }
            if admin.listen.port() != 0
                && (admin.listen == self.listen
                    || self
                        .peers
                        .get(&self.keeper)
                        .is_some_and(|peer| peer.bind_addr() == admin.listen)
                    || self
                        .bulk
                        .get(&self.keeper)
                        .is_some_and(|bulk| bulk.bind_addr() == admin.listen))
            {
                return Err(invalid(
                    "admin listener address must be separate from consensus listeners",
                ));
            }
            if admin
                .probe_listen
                .is_some_and(|probe| !probe.ip().is_loopback())
            {
                return Err(invalid(
                    "plain HTTP probe listener must bind to a loopback address",
                ));
            }
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
        // An IP address binds as given; a DNS name binds every interface
        // on its port, since the keeper may not know its IP for the name.
        let control = bind_listener(peer.bind_addr()).await?;
        let bulk = bind_listener(bulk.bind_addr()).await?;
        let admin_listener = match &self.admin {
            Some(admin) => Some((bind_listener(admin.listen).await?, admin.mtls)),
            None => None,
        };
        #[cfg(unix)]
        let reload = self.clone();
        let engine = self.prepare(stop).await?;
        #[cfg(unix)]
        let reloader = engine.tls.listen_for_reload(reload, engine.stop.clone())?;
        let result = engine
            .serve([listener, control, bulk], admin_listener)
            .await;
        #[cfg(unix)]
        let _ = reloader.await;
        result
    }

    pub(super) async fn prepare(self, stop: CancellationToken) -> io::Result<Arc<Engine>> {
        let placement = self.validate()?;
        let summary = self.summary();
        let keeper = KeeperId(self.keeper.as_u128());
        let material = self.tls.keeper_tls(keeper)?;
        let enrollment = self.enrollment_with_certificate_digest(material.certificate_digest)?;
        let public_key = material.public_key.clone();
        let tls = tls::Tls::new(material);
        let (rpc, control, bulk, replication) = (
            Rpc::keeper(tls.clone(), self.keepers, Lane::Application),
            Rpc::keeper(tls.clone(), self.peers, Lane::Control),
            Rpc::keeper(tls.clone(), self.bulk.clone(), Lane::Bulk),
            Rpc::keeper(tls.clone(), self.bulk, Lane::Replication),
        );
        let id = self.keeper;
        let registry = self.enrollment.clone();
        let data = self.data.clone();
        let (disk, recognition, mode) = tokio::task::spawn_blocking(move || {
            let disk = Disk::open(enrollment)?;
            let recognition = incarnation::Recognition::open(&registry, id, disk.incarnation)?;
            let mode = drain::OperatorMode::open(&data)?;
            Ok::<_, io::Error>((disk, recognition, mode))
        })
        .await??;
        let lease = Arc::new(lease::Lease::open(
            &self.data,
            Duration::from_millis(self.lease_millis),
            Duration::from_millis(self.lease_drift_margin_millis),
        )?);
        let catalog = if id == self.catalog && self.catalog_voters.is_none() {
            Some(Catalog::new(disk.clone(), &self.data)?)
        } else {
            None
        };
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
        let offload = match &self.offload {
            Some(config) => Some(Arc::new(offload::Offloader::open(config.clone())?)),
            None => None,
        };
        let engine = Arc::new(Engine {
            offload,
            summary,
            tls,
            probe_listen: self.admin.as_ref().and_then(|admin| admin.probe_listen),
            metrics_readers: self
                .admin
                .into_iter()
                .flat_map(|admin| admin.metrics_readers)
                .collect(),
            timed,
            id,
            catalog_id: self.catalog,
            catalog,
            lease,
            catalog_stream: self.catalog_voters.map(|voters| {
                catalog_stream::CatalogStream::new(Voters::from(voters), self.catalog)
            }),
            disk,
            recognition,
            mode,
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
            compaction: parking_lot::Mutex::default(),
            activity: parking_lot::Mutex::default(),
            liveness: parking_lot::Mutex::default(),
            repairs: parking_lot::Mutex::default(),
            preferred: parking_lot::Mutex::default(),
            park_after: Duration::from_secs(self.park_after_secs),
            async_append: self.async_append,
            snapshot_rate: super::network::RateLimiter::new(self.snapshot_send_bytes_per_second),
            scrub_rate: self.scrub_bytes_per_second,
            retire_now: Arc::default(),
            placement_confirmed: parking_lot::Mutex::default(),
            certification: Arc::default(),
            replayed: std::sync::atomic::AtomicBool::new(false),
            stop: stop.child_token(),
            #[cfg(test)]
            reject_append: Default::default(),
            #[cfg(test)]
            read_delay: Default::default(),
            #[cfg(test)]
            status_delay: Default::default(),
            #[cfg(test)]
            scoped_reads: Default::default(),
            #[cfg(test)]
            busy_replies: Default::default(),
            #[cfg(test)]
            fail_repairs: Default::default(),
            #[cfg(test)]
            repair_attempts: Default::default(),
            #[cfg(test)]
            crash: std::sync::atomic::AtomicBool::new(false),
        });
        Ok(engine)
    }
}

struct TimedState {
    authority: super::timed::TimedAuthority,
    stages: super::timed::Stages,
}

pub(super) struct Engine {
    /// Continuous offload to object storage, when configured.
    pub(super) offload: Option<Arc<offload::Offloader>>,
    /// This keeper's settings without secrets, which `/status` reports.
    summary: serde_json::Value,
    tls: tls::Tls,
    probe_listen: Option<SocketAddr>,
    metrics_readers: HashSet<String>,
    timed: Option<Arc<TimedState>>,
    pub(super) id: uuid::Uuid,
    catalog_id: uuid::Uuid,
    catalog: Option<Catalog>,
    catalog_stream: Option<catalog_stream::CatalogStream>,
    /// This keeper's liveness lease with the catalog.
    pub(super) lease: Arc<lease::Lease>,
    pub(super) disk: Disk,
    /// The media incarnations of this keeper and its peers.
    recognition: incarnation::Recognition,
    /// Whether the operator drains or decommissions this keeper.
    mode: drain::OperatorMode,
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
    async_append: bool,
    /// The term and time from which this keeper has led each stream.
    led_since: parking_lot::Mutex<HashMap<StreamId, (u64, Instant)>>,
    /// When the leader first saw each learner of each stream it leads.
    learners_seen: parking_lot::Mutex<HashMap<(StreamId, NodeId), Instant>>,
    pub(super) groups: Mutex<BTreeMap<StreamId, Arc<Group>>>,
    deletions: parking_lot::Mutex<HashMap<StreamId, Instant>>,
    /// Deleted streams whose groups this keeper closed. Clients are answered
    /// `Deleted` and peers are refused instead of reopening the group.
    pub(super) deleted: parking_lot::RwLock<HashSet<StreamId>>,
    /// Idle streams whose groups this keeper closed until the next request,
    /// and when each parked. A copy closed to free its slot has no time: it
    /// refuses empty heartbeats until other traffic reopens it.
    pub(super) parked: parking_lot::RwLock<HashMap<StreamId, Option<Instant>>>,
    /// Pins of parked and deleted groups, kept so the reaper cannot delete
    /// what only they reference.
    pub(super) closed_states: parking_lot::Mutex<HashMap<StreamId, Closed>>,
    compaction: parking_lot::Mutex<compaction::Compaction>,
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
    /// The scrubber's pace in bytes per second; 0 disables it.
    scrub_rate: u64,
    /// Wakes the repair loop when a peer excluded one of this keeper's
    /// replicas, so a removed copy retires at once.
    retire_now: Arc<tokio::sync::Notify>,
    /// Streams whose copy no other keeper's newer configuration excludes,
    /// checked since this keeper started, and when a check some keeper did
    /// not answer ran; see `confirm_placement`.
    placement_confirmed: parking_lot::Mutex<HashMap<StreamId, Option<Instant>>>,
    /// The copies this keeper certified or the catalog fenced: see
    /// `certify`.
    certification: Arc<certify::Certification>,
    /// True once startup WAL replay and initial stream opens have finished.
    replayed: std::sync::atomic::AtomicBool,
    pub(super) stop: CancellationToken,
    #[cfg(test)]
    reject_append: parking_lot::RwLock<Option<tests::RejectAppend>>,
    #[cfg(test)]
    read_delay: std::sync::atomic::AtomicU64,
    /// Milliseconds this keeper waits before answering a status request.
    #[cfg(test)]
    status_delay: std::sync::atomic::AtomicU64,
    #[cfg(test)]
    scoped_reads: std::sync::atomic::AtomicU64,
    #[cfg(test)]
    busy_replies: std::sync::atomic::AtomicU64,
    #[cfg(test)]
    fail_repairs: parking_lot::RwLock<HashSet<StreamId>>,
    #[cfg(test)]
    repair_attempts: parking_lot::Mutex<HashMap<StreamId, u32>>,
    #[cfg(test)]
    pub(super) crash: std::sync::atomic::AtomicBool,
}

/// What a closed replica keeps so the reaper spares what reopening needs.
pub(super) enum Closed {
    /// The group is shutting down; its state machine still holds everything.
    Closing(StateMachine),
    /// The group shut down; only pins remain, and the image is dropped.
    Pinned(Arc<storage::Pin>),
}

impl Closed {
    pub(super) fn finalized(&self) -> Option<super::Configuration> {
        match self {
            Self::Closing(state) => state.finalized(),
            Self::Pinned(pin) => pin.finalized,
        }
    }

    fn generation(&self) -> u64 {
        match self {
            Self::Closing(state) => state.generation(),
            Self::Pinned(pin) => pin.generation,
        }
    }

    fn lifetime(&self) -> Weak<()> {
        match self {
            Self::Closing(state) => state.lifetime(),
            Self::Pinned(pin) => pin.lifetime(),
        }
    }
}

enum Identity {
    Keeper(NodeId),
    Client(journal_contract::Identity),
}

impl Engine {
    /// Accepts keeper IDs reused on new media, as keepers did before media
    /// incarnations, so the fault harness can show it still finds amnesia.
    #[cfg(test)]
    pub(super) fn ignore_reused_ids(&self) {
        self.recognition.ignore_reuse();
    }

    #[cfg(test)]
    pub(super) fn set_transport_filter(&self, filter: Option<super::network::TransportFilter>) {
        self.rpc.set_filter(self.id, filter.clone());
        self.control.set_filter(self.id, filter.clone());
        self.replication.set_filter(self.id, filter.clone());
        self.bulk.set_filter(self.id, filter);
    }

    pub(super) async fn serve(
        self: Arc<Self>,
        listeners: [TcpListener; 3],
        admin: Option<(TcpListener, bool)>,
    ) -> io::Result<()> {
        let _serving_media = self.disk.hold_media_lock()?;
        let mut sockets = JoinSet::new();
        let result = async {
            for (stream, reason) in self.disk.quarantined_streams() {
                self.disk.protect_objects(stream);
                if self.quarantined.write().insert(stream) {
                    tracing::warn!(
                        keeper = %self.id,
                        stream = %super::logging::stream_uuid(stream),
                        reason = %reason,
                        "loaded a durable quarantine"
                    );
                }
            }
            if let Some((listener, mtls)) = admin {
                let engine = self.clone();
                sockets.spawn(async move { engine.listen_admin(listener, mtls, false).await });
            }
            if let Some(address) = self.probe_listen {
                let listener = bind_listener(address).await?;
                let engine = self.clone();
                sockets.spawn(async move { engine.listen_admin(listener, false, true).await });
            }
            for genesis in self.disk.streams() {
                if self.is_quarantined(genesis.stream) {
                    continue;
                }
                if self
                    .disk
                    .ownership(genesis.stream)
                    .is_some_and(|owner| owner.generation().is_none())
                {
                    continue;
                }
                // A copy parked before the restart stays parked, with the
                // pins its park mark names, until traffic reopens it.
                let disk = self.disk.clone();
                let stream = genesis.stream;
                match tokio::task::spawn_blocking(move || storage::Pin::restore(&disk, stream))
                    .await
                    .map_err(io::Error::other)
                    .and_then(|restored| restored)
                {
                    Ok(Some(pin)) => {
                        self.closed_states
                            .lock()
                            .insert(stream, Closed::Pinned(Arc::new(pin)));
                        self.parked.write().insert(stream, Some(Instant::now()));
                        continue;
                    }
                    Ok(None) => (),
                    Err(error) => {
                        tracing::warn!(
                            keeper = %self.id,
                            stream = %crate::stream::consensus::logging::stream_uuid(stream),
                            error = %error,
                            "ignored the park mark"
                        );
                    }
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
            self.replayed
                .store(true, std::sync::atomic::Ordering::Release);
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
            let compacting = self.clone();
            sockets.spawn(async move {
                compacting.compaction_loop().await;
                Ok(())
            });
            let offloading = self.clone();
            let stopping = self.stop.clone();
            sockets.spawn(async move {
                offloading.offload_loop().await;
                // A keeper stops when any of its tasks ends.
                stopping.cancelled().await;
                Ok(())
            });
            let scrubbing = self.clone();
            sockets.spawn(async move {
                scrubbing.scrub_loop().await;
                Ok(())
            });
            let certifying = self.clone();
            sockets.spawn(async move {
                certifying.certify_loop().await;
                Ok(())
            });
            let versioning = self.clone();
            sockets.spawn(async move {
                versioning.cluster_version_loop().await;
                Ok(())
            });
            let leasing = self.clone();
            sockets.spawn(async move {
                leasing.lease_loop().await;
                Ok(())
            });
            let draining = self.clone();
            sockets.spawn(async move {
                draining.drain_loop().await;
                Ok(())
            });
            if self.catalog_stream.is_some() {
                let tending = self.clone();
                sockets.spawn(async move {
                    tending.tend_catalog_stream().await;
                    Ok(())
                });
            }
            let gauges = self.disk.clone();
            tokio::spawn(super::metrics::report(
                self.id,
                self.disk.metrics.clone(),
                Duration::from_secs(5),
                self.stop.clone(),
                move || gauges.segment_usage().to_string(),
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
                            if let Err(error) = engine.disk.reap_objects().await
                                && let Some(dropped) =
                                    super::logging::rate_limit("keeper.object_cleanup", None)
                            {
                                tracing::warn!(
                                    keeper = %engine.id,
                                    error = %error,
                                    dropped = dropped,
                                    "object cleanup deferred"
                                );
                            }
                            if let Err(error) = engine.reclaim_detached(&mut cursor).await
                                && let Some(dropped) =
                                    super::logging::rate_limit("keeper.replica_cleanup", None)
                            {
                                tracing::warn!(
                                    keeper = %engine.id,
                                    error = %error,
                                    dropped = dropped,
                                    "replica cleanup deferred"
                                );
                            }
                        },
                    }
                }
            });
            for (listener, (lane, capacity)) in listeners.into_iter().zip([
                (Lane::Application, MAX_CLIENT_CONNECTIONS),
                (Lane::Control, 0),
                (Lane::Bulk, MAX_BULK_CONNECTIONS),
            ]) {
                let engine = self.clone();
                sockets.spawn(async move { engine.listen(listener, lane, capacity).await });
            }
            tokio::select! {
                _ = self.stop.cancelled() => Ok(()),
                result = sockets.join_next() => result.expect("keeper has listeners")?,
            }
        }
        .await;
        self.stop.cancel();
        self.disk.disable_reaping();
        #[cfg(test)]
        let evict = !self.crash.load(std::sync::atomic::Ordering::Acquire);
        #[cfg(not(test))]
        let evict = true;
        if evict {
            self.evict_leaders(Duration::from_secs(3), false).await;
        }
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
    async fn evict_leaders(&self, limit: Duration, require_accepting: bool) {
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let _ = timeout(
            limit,
            futures::future::join_all(groups.into_iter().map(|group| async move {
                let mut metrics = group.raft.metrics();
                let mut targets = BTreeSet::new();
                let current = metrics.borrow_watched().clone();
                if current.state != openraft::ServerState::Leader {
                    return;
                }
                for id in current.membership_config.membership().voter_ids() {
                    if id != self.id.as_u128()
                        && self
                            .reachable(uuid::Uuid::from_u128(id))
                            .await
                            .map_or(!require_accepting, |status| status.accepting)
                    {
                        targets.insert(id);
                    }
                }
                if targets.is_empty() {
                    return;
                }
                let Ok(_membership) = group.membership.try_lock() else {
                    return;
                };
                // Bound the write pause by the hand-off deadline. A busy
                // stream's followers can now catch up to the last proposal.
                let Ok(_writes) = group.writes.acquire_many(MAX_PENDING_WRITES as u32).await else {
                    return;
                };
                loop {
                    let current = metrics.borrow_watched().clone();
                    if current.state != openraft::ServerState::Leader {
                        return;
                    }
                    let matched = current
                        .replication
                        .iter()
                        .flatten()
                        .find_map(|(id, matched)| {
                            (targets.contains(id)
                                && matched.map(|log| log.index) == current.last_log_index)
                                .then_some(*id)
                        });
                    if let Some(target) = matched {
                        if group.raft.trigger().transfer_leader(target).await.is_err() {
                            return;
                        }
                        break;
                    }
                    if metrics.changed().await.is_err() {
                        return;
                    }
                }
                while metrics.borrow_watched().state == openraft::ServerState::Leader {
                    if metrics.changed().await.is_err() {
                        return;
                    }
                }
                super::metrics::count(&self.disk.metrics.handoffs);
            })),
        )
        .await;
    }

    /// Takes a copy that failed to open out of service. A copy whose data
    /// fails its checksum or does not decode stays quarantined across
    /// restarts until repair restores it or an operator clears it; one that
    /// failed otherwise is retried at the next start.
    fn quarantine(&self, stream: StreamId, error: &io::Error) {
        if error.kind() == io::ErrorKind::InvalidData {
            self.disk.quarantine_stream(stream, &error.to_string());
        } else {
            self.disk.protect_objects(stream);
        }
        if self.quarantined.write().insert(stream) {
            tracing::error!(
                keeper = %self.id,
                stream = %super::logging::stream_uuid(stream),
                error = %error,
                "quarantined stream replica"
            );
        }
    }

    pub(super) fn is_quarantined(&self, stream: StreamId) -> bool {
        self.quarantined.read().contains(&stream) || self.disk.is_quarantined(stream)
    }

    async fn clear_quarantine(&self, stream: StreamId) -> io::Result<Reply> {
        let opening = self.opening(stream).await?;
        let _guard = opening.lock().await;
        self.disk.clear_quarantine(stream)?;
        self.quarantined.write().remove(&stream);
        self.close_copy(stream).await;
        Ok(Reply::Decision(Outcome::Unit))
    }

    fn require_media(&self) -> io::Result<()> {
        if self.disk.healthy() {
            Ok(())
        } else {
            Err(invalid("keeper media is unavailable"))
        }
    }

    /// The state machine of a closed copy of `stream`, for inspection. A
    /// pinned copy is loaded from its snapshot and WAL suffix under the
    /// opening lock, so no group opens beside it.
    #[cfg(test)]
    pub(super) async fn closed_state(&self, stream: StreamId) -> Option<StateMachine> {
        if let Closed::Closing(state) = self.closed_states.lock().get(&stream)? {
            return Some(state.clone());
        }
        let opening = self.opening(stream).await.ok()?;
        let _guard = opening.lock().await;
        if self.groups.lock().await.contains_key(&stream) {
            return None;
        }
        let genesis = self.disk.genesis(stream)?;
        let state = StateMachine::open(&self.disk, genesis, self.placement.clone())
            .await
            .ok()?;
        Some(state)
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

    /// The opening lock of `stream`. At the stream limit the least recently
    /// used idle copy closes to free its slot instead of refusing the open.
    async fn opening_or_evict(&self, stream: StreamId) -> io::Result<Arc<Mutex<()>>> {
        match self.opening(stream).await {
            Err(error) if error.kind() == io::ErrorKind::QuotaExceeded => {
                if self.evict_idle(stream).await {
                    self.opening(stream).await
                } else {
                    Err(error)
                }
            }
            result => result,
        }
    }

    /// Closes the least recently used open copy that has served no client,
    /// grown no log and run no repair for `EVICT_AFTER` (or the park delay,
    /// if shorter), other than `except`. A copy this keeper leads first
    /// hands its leadership to a matched follower, so the stream elects no
    /// new leader; copies it follows go first. The closed copy is parked
    /// with a durable mark and refuses empty heartbeats until entries, a
    /// vote, a snapshot or a client reopen it. False when no copy qualifies.
    async fn evict_idle(&self, except: StreamId) -> bool {
        let after = self.park_after.min(EVICT_AFTER);
        let now = Instant::now();
        let groups = self
            .groups
            .lock()
            .await
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let mut candidates = groups
            .into_iter()
            .filter(|group| {
                let stream = group.genesis.stream;
                let metrics = group.raft.metrics().borrow_watched().clone();
                let grew = self
                    .activity
                    .lock()
                    .get(&stream)
                    .is_some_and(|(_, since)| now.duration_since(*since) < after);
                stream != except
                    && !(self.catalog_stream.is_some() && stream == catalog_stream::STREAM)
                    && !self.repairing(stream)
                    && !grew
                    && now.duration_since(*group.used.lock()) >= after
                    && metrics.last_applied.map(|applied| applied.index) == metrics.last_log_index
                    && metrics
                        .membership_config
                        .membership()
                        .get_joint_config()
                        .len()
                        == 1
            })
            .map(|group| {
                let leads =
                    group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader;
                let used = *group.used.lock();
                (leads, used, group)
            })
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(leads, used, _)| (*leads, *used));
        for (leads, _, group) in candidates {
            if leads && !self.hand_off(&group).await {
                continue;
            }
            let stream = group.genesis.stream;
            drop(group);
            let closed = self
                .close_retaining(
                    stream,
                    || {
                        self.parked.write().insert(stream, None);
                        self.activity.lock().remove(&stream);
                    },
                    true,
                )
                .await;
            if closed {
                super::metrics::count(&self.disk.metrics.evicted);
                return true;
            }
        }
        false
    }

    /// Hands a led stream to a voter that matched its whole log, and waits
    /// up to a second for this keeper to stop leading it.
    async fn hand_off(&self, group: &Group) -> bool {
        let metrics = group.raft.metrics().borrow_watched().clone();
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
        let Some(target) = target else {
            return false;
        };
        if group.raft.trigger().transfer_leader(target).await.is_err() {
            return false;
        }
        let mut metrics = group.raft.metrics();
        timeout(Duration::from_secs(1), async {
            while metrics.borrow_watched().state == openraft::ServerState::Leader {
                if metrics.changed().await.is_err() {
                    break;
                }
            }
        })
        .await
        .is_ok()
            && group.raft.metrics().borrow_watched().state != openraft::ServerState::Leader
    }

    /// Closes the groups of deleted streams once the deletion is applied on
    /// this replica, replicated to every voter it can see, and older than
    /// `DELETED_GROUP_GRACE`. The terminal snapshot preserves the applied
    /// deletion across restart. Client requests never reopen a closed copy.
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
        let mut snapshotting = Vec::new();
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
                    && let Some(applied) = group.raft.metrics().borrow_watched().last_applied
                {
                    if group
                        .state
                        .covered()
                        .is_some_and(|covered| covered == applied)
                    {
                        closing.push(*stream);
                    } else {
                        snapshotting.push(group.clone());
                    }
                }
            }
            for stream in &closing {
                seen.remove(stream);
            }
        }
        for group in snapshotting {
            let _ = group.raft.trigger().snapshot().await;
        }
        for stream in closing {
            // Marked first: a request that races the close is refused
            // rather than reopening the group. The writer's preference goes
            // with the mark, so a closed stream is never seen holding one,
            // and again after the close in case a request raced it.
            self.deleted.write().insert(stream);
            self.preferred.lock().remove(&stream);
            self.close_retaining(stream, || (), false).await;
            self.preferred.lock().remove(&stream);
        }
    }

    /// Closes a copy whose Raft core stopped, so the next request or peer
    /// message opens it again from its durable state. OpenRaft stops a
    /// group for good on any log storage error, such as a vote refused
    /// below the protocol space floor, while the keeper's media stays
    /// healthy; without this the copy would stay a voter that never
    /// answers. The copy stays as it is while the space is still short.
    async fn close_stopped(&self, group: &Group) -> io::Result<()> {
        let stream = group.genesis.stream;
        if !self.disk.healthy() || !self.disk.space.accepts_protocol() {
            return Err(invalid("stream replica stopped and its media has no room"));
        }
        super::metrics::count(&self.disk.metrics.reopened_stopped);
        tracing::warn!(
            keeper = %self.id,
            stream = %super::logging::stream_uuid(stream),
            "reopening stream replica whose Raft core stopped"
        );
        self.close_retaining(stream, || (), false).await;
        Ok(())
    }

    async fn group(&self, genesis: Genesis) -> io::Result<Arc<Group>> {
        self.require_media()?;
        if self.is_quarantined(genesis.stream) {
            return Err(invalid("stream replica is quarantined"));
        }
        let existing = self.groups.lock().await.get(&genesis.stream).cloned();
        match existing {
            Some(group) if !group.stopped() => return group.for_genesis(&genesis),
            Some(group) => self.close_stopped(&group).await?,
            None => {}
        }
        let opening = self.opening_or_evict(genesis.stream).await?;
        let _guard = opening.lock().await;
        if let Some(group) = self.groups.lock().await.get(&genesis.stream).cloned() {
            return group.for_genesis(&genesis);
        }
        if self.is_quarantined(genesis.stream) {
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
                let _placement = self.mode.admit_placement().await?;
                self.disk
                    .maintenance(Record::Register(genesis.clone()))
                    .await?
            }
        }
        // A closed group's appends may still be in flight; open on the
        // log they leave.
        let inflight = self.disk.inflight(genesis.stream);
        inflight.drained().await;
        inflight.reset();
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
                // An open copy is no longer parked across a restart.
                let (disk, stream, generation) =
                    (self.disk.clone(), genesis.stream, state.generation());
                let forgotten = tokio::task::spawn_blocking(move || {
                    storage::Pin::forget(&disk, stream, generation)
                })
                .await
                .map_err(io::Error::other)
                .and_then(|result| result);
                if let Err(error) = forgotten {
                    tracing::warn!(
                        keeper = %self.id,
                        stream = %crate::stream::consensus::logging::stream_uuid(stream),
                        error = %error,
                        "park mark not removed"
                    );
                }
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
            asynchronous: self.async_append,
            inflight,
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
                certified: {
                    let certification = self.certification.clone();
                    let (stream, generation) = (genesis.stream, state.generation());
                    Arc::new(move || certification.require(stream, generation))
                },
                authority: {
                    let (lease, stream, state) =
                        (self.lease.clone(), genesis.stream, state.clone());
                    Arc::new(move || lease::permits(&lease, stream, &state))
                },
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
            leader_matched: parking_lot::Mutex::new(None),
            proposals: Arc::default(),
            excluded,
            draining: self.mode.flag.clone(),
            stop: self.stop.child_token(),
        });
        self.apply_mode(&group);
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
                        | Request::Staging(_)
                        | Request::KeeperStatus(_)
                        | Request::PlacementProof(_)
                        | Request::LocalConfiguration(_)
                        | Request::LocalTip(_)
                        | Request::StageReplica { .. }
                        | Request::InstallReplica { .. }
                        | Request::StageRecovered { .. }
                        | Request::PreferLeader { .. }
                        | Request::ClusterVersion
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
            // A keeper renews only its own lease, fences only itself once it
            // decommissioned, and only a recovery's survivor recovers.
            Identity::Keeper(id)
                if matches!(request, Request::RenewLease { keeper, .. }
                    if keeper.as_u128() == *id)
                    || matches!(request, Request::FenceKeeper(keeper)
                    if keeper.as_u128() == *id)
                    || matches!(request, Request::RecoverStream { stage, .. }
                    if stage.survivors().iter().any(|survivor| survivor.as_u128() == *id)) =>
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
                    | Request::ClusterVersion
                    | Request::Head(_)
                    | Request::RecoveryFence(_)
                    | Request::Configuration(_)
                    | Request::Read { .. }
                    | Request::ReadAt { .. } => admin || writer || reader,
                    Request::Seal { .. }
                    | Request::SealSession { .. }
                    | Request::Append { .. }
                    | Request::AppendBatch { .. }
                    | Request::StageOriginal { .. }
                    | Request::StageSessionOriginal { .. }
                    | Request::AppendOriginal { .. }
                    | Request::Written { .. }
                    | Request::AcknowledgeRecoveryWithMarker { .. }
                    | Request::Trim { .. } => writer,
                    // An administrator may move leadership; it writes nothing.
                    Request::PreferLeader { .. } => writer || admin,
                    // An administrator may acknowledge a recovery, but only a
                    // writer may write to the stream.
                    Request::AcknowledgeRecovery(_) => writer || admin,
                    Request::ProveOriginal { .. } => admin || writer || reader,
                    Request::Stage(_)
                    | Request::StageReplica { .. }
                    | Request::InstallReplica { .. }
                    | Request::StageRecovered { .. }
                    | Request::RenewLease { .. }
                    | Request::RecoverStream { .. } => false,
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
        if matches!(&request, Request::Claim(genesis) if genesis.immutable)
            && !self.disk.write_version_allows(super::CLUSTER_VERSION_V4)
        {
            self.sync_cluster_version().await;
            if !self.disk.write_version_allows(super::CLUSTER_VERSION_V4) {
                return Ok(failure(JournalError::Unsupported));
            }
        }
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
            Request::KeeperStatus(stream) => {
                #[cfg(test)]
                tokio::time::sleep(Duration::from_millis(
                    self.status_delay.load(std::sync::atomic::Ordering::Relaxed),
                ))
                .await;
                Ok(Reply::Status(self.status(stream).await))
            }
            Request::LocalConfiguration(stream) => {
                let open = self
                    .groups
                    .lock()
                    .await
                    .get(&stream)
                    .map(|group| group.state.finalized());
                let configuration = match open {
                    Some(configuration) => configuration,
                    None => self
                        .closed_states
                        .lock()
                        .get(&stream)
                        .and_then(Closed::finalized),
                };
                Ok(Reply::Configured(configuration))
            }
            Request::ClearQuarantine(stream) => self.clear_quarantine(stream).await,
            Request::LocalTip(stream) => Ok(Reply::Tip(
                self.disk
                    .genesis(stream)
                    .is_some()
                    .then(|| self.disk.recovery_point(stream).tip)
                    .flatten(),
            )),
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
                let actor = owner.as_deref().unwrap_or("unknown");
                let result = self
                    .retire_copy(stream, authority, revision, generation)
                    .await;
                let outcome = describe_audit_result(&result);
                super::logging::audit_retire(
                    self.id, stream, actor, authority, revision, generation, &outcome,
                );
                result
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
                if genesis.immutable
                    || self
                        .disk
                        .genesis(stream)
                        .is_some_and(|local| local.immutable)
                {
                    return Ok(failure(JournalError::Unsupported));
                }
                // The replacement may not hold this stream yet. Validate
                // its history mode against the catalog's durable claim.
                match self.catalog_request(Request::Locate(stream)).await? {
                    Reply::Catalog(claimed, _) if claimed == genesis => (),
                    Reply::Catalog(claimed, _) if claimed.immutable => {
                        return Ok(failure(JournalError::Unsupported));
                    }
                    _ => return Ok(failure(JournalError::Unavailable)),
                }
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
            Request::FinalizeVersion(target) => {
                if target > super::CLUSTER_VERSION_V1
                    && let Err(error) = self.all_keepers_support_version(target).await
                {
                    return Ok(failure(error));
                }
                if self.catalog_stream.is_some() {
                    self.serve_catalog_stream(Request::FinalizeVersion(target))
                        .await
                } else {
                    self.catalog()?.finalize_version(target).await
                }
            }
            // A renewal from another catalog voter is not forwarded again,
            // so two followers with stale leaders cannot pass it around.
            Request::RenewLease { .. } if self.catalog_stream.is_some() => {
                let forward = !matches!(identity, Identity::Keeper(id)
                    if self.catalog_voter(uuid::Uuid::from_u128(*id)));
                self.serve_renewal(request, forward).await
            }
            Request::Claim(_)
            | Request::Locate(_)
            | Request::Stage(_)
            | Request::Staging(_)
            | Request::ClusterVersion
            | Request::FenceKeeper(_)
            | Request::RecoverStream { .. }
                if self.catalog_stream.is_some() =>
            {
                self.serve_catalog_stream(request).await
            }
            Request::RenewLease {
                keeper,
                incarnation,
                epoch,
            } => {
                self.catalog()?
                    .renew(keeper, incarnation, epoch, self.lease_millis())
                    .await
            }
            Request::FenceKeeper(keeper) => self.catalog()?.fence(keeper).await,
            Request::RecoverStream {
                stage,
                dead,
                record,
            } => {
                self.catalog()?
                    .recover(
                        stage,
                        dead,
                        record,
                        &self.placement,
                        self.recovery_wait_ms()?,
                    )
                    .await
            }
            Request::Claim(genesis) => self.catalog()?.claim(genesis, &self.placement).await,
            Request::Locate(stream) => self.catalog()?.locate(stream),
            Request::Stage(stage) => self.catalog()?.stage(stage, &self.placement).await,
            Request::Staging(stream) => self.catalog()?.staged(stream),
            Request::ClusterVersion => self.catalog()?.cluster_version(),
            Request::Bootstrap(stream) => self.bootstrap(stream).await,
            request => {
                // Only a copy whose data failed its checksum is Corrupted; one
                // out of service for another reason is merely unavailable.
                if self.disk.is_quarantined(stream) {
                    let refused = Outcome::Refused(JournalError::Corrupted);
                    return Ok(match (&request, self.disk.genesis(stream)) {
                        (Request::ReadAt { .. }, Some(genesis)) => Reply::ScopedPage {
                            genesis,
                            configuration: None,
                            outcome: refused,
                        },
                        _ => Reply::Decision(refused),
                    });
                }
                let group = self.groups.lock().await.get(&stream).cloned();
                if let Some(stopped) = group.as_ref().filter(|group| group.stopped()) {
                    // Reopen the copy; it elects a leader and the client
                    // retries.
                    if self.group(stopped.genesis.clone()).await.is_err() {
                        return Ok(failure(JournalError::Unavailable));
                    }
                    return Ok(Reply::Leader(None));
                }
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
                        super::metrics::count(&self.disk.metrics.unparked_by_client);
                    }
                    return Ok(Reply::Leader(None));
                };
                *group.used.lock() = Instant::now();
                if !self.disk.installed(stream) {
                    return Ok(failure(JournalError::Unavailable));
                }
                if group.state.is_quarantined() {
                    self.quarantined.write().insert(stream);
                    let refused = Outcome::Refused(JournalError::Corrupted);
                    return Ok(match &request {
                        Request::ReadAt { .. } => Reply::ScopedPage {
                            genesis: group.genesis.clone(),
                            configuration: None,
                            outcome: refused,
                        },
                        _ => Reply::Decision(refused),
                    });
                }
                group.require_healthy()?;
                // Leading and serving need authority: a valid liveness lease,
                // the current epoch and no catalog fence (`keeper/lease.rs`).
                // It is checked again before the answer leaves, so nothing
                // read or acknowledged after a lapse is served.
                if !self.holds_authority(&group) {
                    super::metrics::count(&self.lease.gated);
                    return Ok(failure(JournalError::Unavailable));
                }
                if matches!(
                    request,
                    Request::Append { .. }
                        | Request::AppendBatch { .. }
                        | Request::AppendOriginal { .. }
                ) && let Some(offload) = &self.offload
                    && offload.backpressured(stream)
                {
                    super::metrics::count(&offload.store.metrics.backpressured_appends);
                    return Ok(failure(JournalError::Unavailable));
                }
                let reply = match request {
                    Request::Head(_) => Ok(group.head().await),
                    Request::RecoveryFence(_) => Ok(group.recovery_fence().await),
                    Request::OffloadStatus { flush, .. } => {
                        Ok(self.offload_status(&group, flush).await)
                    }
                    Request::Restore { restore, .. } => {
                        let actor = owner.as_deref().unwrap_or("unknown");
                        let reply = self.restore_fresh(&group, restore.clone()).await;
                        tracing::info!(
                            target: "logkeeper::audit",
                            keeper = %self.id,
                            stream = %format!("{:032x}", stream.0),
                            actor = actor,
                            head = restore.head.0,
                            floor = restore.floor.0,
                            outcome = %describe_audit_reply(&reply),
                            "restore stream from offload store"
                        );
                        Ok(reply)
                    }
                    Request::Written {
                        fence,
                        at,
                        payloads,
                        ..
                    } => Ok(group.written(fence, at, payloads).await),
                    Request::PlacementProof(_) => Ok(group.proof().await),
                    Request::Configuration(_) => Ok(group.configuration().await),
                    Request::Read {
                        from,
                        limit,
                        wait_ms,
                        ..
                    } => Ok(Reply::Decision(if self.certified(&group) {
                        group
                            .read(from, limit, wait_ms, Lsn(0), self.offload.as_deref())
                            .await
                    } else {
                        Outcome::Refused(JournalError::Unavailable)
                    })),
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
                        if !super::decisions::serves_reads(
                            group.state.serves_applied_pages(self.id.as_u128()),
                            self.certified(&group),
                        ) {
                            return Ok(failure(JournalError::Unavailable));
                        }
                        let outcome = group
                            .read(from, limit, wait_ms, minimum_head, self.offload.as_deref())
                            .await;
                        Ok(Reply::ScopedPage {
                            genesis,
                            configuration: group.state.finalized(),
                            outcome,
                        })
                    }
                    Request::Replace {
                        expected, voters, ..
                    } => {
                        let actor = owner.as_deref().unwrap_or("unknown");
                        let result = self.replace(&group, expected, voters).await;
                        let outcome = describe_audit_result(&result);
                        super::logging::audit_replace(
                            self.id, stream, actor, expected, &voters, &outcome,
                        );
                        result
                    }
                    Request::PreferLeader { keeper, .. } => {
                        let actor = owner.as_deref().unwrap_or("unknown");
                        let result = self.prefer_leader(&group, keeper).await;
                        let outcome = describe_audit_result(&result);
                        super::logging::audit_prefer_leader(
                            self.id, stream, actor, keeper, &outcome,
                        );
                        result
                    }
                    Request::Create(_) => Ok(group.write(Command::Create).await),
                    Request::SealSession {
                        expected_writer_epoch,
                        writer_session_id,
                        ..
                    } => {
                        if !group.genesis.immutable {
                            return Ok(failure(JournalError::Unsupported));
                        }
                        Ok(group
                            .write(Command::SealSession {
                                expected_writer_epoch,
                                writer_session_id,
                                owner: owner.unwrap(),
                            })
                            .await)
                    }
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
                        self.stage_original(
                            &group,
                            owner.unwrap(),
                            revision,
                            &original,
                            payload,
                            None,
                        )
                        .await
                    }
                    Request::StageSessionOriginal {
                        fence,
                        revision,
                        original,
                        payload,
                    } => {
                        self.stage_original(
                            &group,
                            owner.unwrap(),
                            revision,
                            &original,
                            payload,
                            Some(fence),
                        )
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
                                    Ok(Err(error))
                                        if error.kind() == io::ErrorKind::InvalidData =>
                                    {
                                        group.state.quarantine_corrupt(&error.to_string());
                                        self.quarantined.write().insert(stream);
                                        Outcome::Refused(JournalError::Corrupted)
                                    }
                                    Ok(Err(_)) => Outcome::Refused(JournalError::Unavailable),
                                    Err(_) => Outcome::Refused(JournalError::Unavailable),
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
                        let actor = owner.as_deref().unwrap_or("unknown");
                        let reply = group.write(Command::AcknowledgeRecovery).await;
                        let outcome = describe_audit_reply(&reply);
                        super::logging::audit_acknowledge_recovery(
                            self.id, stream, actor, &outcome,
                        );
                        Ok(reply)
                    }
                    Request::AcknowledgeRecoveryWithMarker { fence, payload, .. } => {
                        if !self.disk.write_version_allows(super::CLUSTER_VERSION_V3) {
                            self.sync_cluster_version().await;
                            if !self.disk.write_version_allows(super::CLUSTER_VERSION_V3) {
                                return Ok(failure(JournalError::Unsupported));
                            }
                        }
                        if payload.len() > super::MAX_RECORD {
                            return Ok(failure(JournalError::TooLarge {
                                max: super::MAX_RECORD,
                            }));
                        }
                        let Some(at) = fence.head.0.checked_add(1).map(Lsn) else {
                            return Ok(failure(JournalError::Conflict { head: fence.head }));
                        };
                        let reply = group
                            .write(Command::AcknowledgeRecoveryWithMarker { fence, at, payload })
                            .await;
                        let actor = owner.as_deref().unwrap_or("unknown");
                        let outcome = describe_audit_reply(&reply);
                        super::logging::audit_acknowledge_recovery(
                            self.id, stream, actor, &outcome,
                        );
                        Ok(reply)
                    }
                    _ => Err(invalid("invalid application request")),
                }?;
                if group.state.is_quarantined() {
                    self.quarantined.write().insert(stream);
                    return Ok(reply);
                }
                group.require_healthy()?;
                if !self.holds_authority(&group) {
                    super::metrics::count(&self.lease.gated);
                    return Ok(failure(JournalError::Unavailable));
                }
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
        session: Option<journal_contract::WriterFence>,
    ) -> io::Result<Reply> {
        use crate::stream::timed::{EVIDENCE_BYTES, MAX_TIMED_PAYLOAD, TimedOriginal};
        let refused = |error| Ok(Reply::Decision(Outcome::Refused(error)));
        if group.genesis.immutable != session.is_some() {
            return refused(JournalError::Unsupported);
        }
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
            Some((fence, principal))
                if fence.epoch == original.epoch
                    && *principal == owner
                    && session.is_none_or(|session| {
                        session.stream == original.stream
                            && session.writer_epoch == fence.epoch
                            && session.writer_session_id.0 == fence.writer.as_u128()
                    }) => {}
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
        let Some(origin) = super::timed::origin(original, voters, revision) else {
            return refused(JournalError::Unsupported);
        };
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
                ) != Some(evidence.origin))
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
                Request::Staging(stream) => catalog.staged(stream),
                Request::ClusterVersion => catalog.cluster_version(),
                Request::RenewLease {
                    keeper,
                    incarnation,
                    epoch,
                } => {
                    catalog
                        .renew(keeper, incarnation, epoch, self.lease_millis())
                        .await
                }
                Request::FenceKeeper(keeper) => catalog.fence(keeper).await,
                _ => Err(invalid("invalid internal catalog request")),
            }
        } else {
            self.rpc
                .call_application(self.catalog_id, request, REQUEST_TIMEOUT)
                .await
        }
    }

    /// The lease and drift margin this keeper grants as a catalog keeper,
    /// in milliseconds.
    fn lease_millis(&self) -> (u64, u64) {
        (
            self.lease.duration().as_millis() as u64,
            self.lease.margin().as_millis() as u64,
        )
    }

    fn recovery_wait_ms(&self) -> io::Result<u64> {
        let (duration, margin) = self.lease_millis();
        super::decisions::recovery_wait(duration, margin)
            .ok_or_else(|| invalid("lease duration overflows"))
    }

    fn catalog_voter(&self, keeper: uuid::Uuid) -> bool {
        self.catalog_stream
            .as_ref()
            .is_some_and(|catalog| catalog.voters().contains(&keeper))
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
        let fresh = self.disk.genesis(stream).is_none();
        if fresh {
            self.check_identity().await;
        }
        let group = self.group(genesis).await?;
        // A copy the catalog's genesis registers empty cannot hold a
        // history any move or recovery left behind.
        if fresh {
            self.certification.certify(stream, group.state.generation());
        }
        let initialized = group.raft.initialize(members).await;
        group.require_healthy()?;
        match initialized {
            Ok(()) | Err(RaftError::APIError(InitializeError::NotAllowed(_))) => {
                Ok(Reply::Decision(Outcome::Unit))
            }
            Err(error) => Err(io::Error::other(error)),
        }
    }

    fn nodes(&self, voters: Voters) -> BTreeMap<NodeId, BasicNode> {
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

pub(super) struct Group {
    pub(super) genesis: Genesis,
    pub(super) raft: Raft,
    pub(super) state: StateMachine,
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
    /// The term and time when a leader's append last matched this follower's log.
    leader_matched: parking_lot::Mutex<Option<(u64, Instant)>>,
    /// This stream's proposals in flight, for the slow-proposal gauges.
    proposals: Arc<Proposals>,
    /// The last peer that refused this replica as outside its placement.
    excluded: Arc<parking_lot::Mutex<Option<uuid::Uuid>>>,
    /// Set while the operator drains this keeper: it starts no election.
    draining: Arc<std::sync::atomic::AtomicBool>,
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
        if super::decisions::hands_off(
            target.as_u128() == metrics.id,
            matched,
            metrics.last_log_index,
            recent,
        ) && self
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

    /// Whether OpenRaft stopped this group's core, after a storage error
    /// or a panic.
    fn stopped(&self) -> bool {
        self.raft.metrics().borrow_watched().running_state.is_err()
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
                    if self.draining.load(std::sync::atomic::Ordering::Acquire) { continue; }
                    if !self.state.healthy() || self.raft.trigger().elect(false).await.is_err() { return; }
                }
            }
        }
    }

    async fn write(&self, command: Command) -> Reply {
        use super::metrics::count;
        // Borrowed, not cloned: one shared refcount bumped by every write
        // on every stream would be a contended cache line.
        let metrics = self.state.metrics();
        let started = std::time::Instant::now();
        if self.require_healthy().is_err() {
            count(&metrics.write_unhealthy);
            return failure(JournalError::Unavailable);
        }
        let Ok(permit) = self.writes.clone().try_acquire_owned() else {
            count(&metrics.write_pending);
            return failure(JournalError::Unavailable);
        };
        let ticket = uuid::Uuid::new_v4();
        let space = match self
            .state
            .reserve_command(&command, ticket, MAX_LOG_SUFFIX as usize)
        {
            Ok(space) => space,
            Err(storage::Admission::FullSuffix) => {
                count(&metrics.write_full_suffix);
                self.request_covered_purge().await;
                return failure(JournalError::Unavailable);
            }
            Err(storage::Admission::Space) => {
                count(&metrics.write_space);
                return failure(JournalError::Unavailable);
            }
        };
        let raft = self.raft.clone();
        let in_flight = InFlight::start(&self.proposals, ticket, started, metrics.clone());
        // The proposal owns its reservation even when the caller drops the
        // request or times out. The WAL settles it as it publishes the slot.
        let proposal = tokio::spawn(async move {
            let (_permit, _space) = (permit, space);
            let proposal_metrics = &in_flight.metrics;
            let (responder, response) = ProgressResponder::complete_only();
            if let Err(error) = raft
                .client_write_ff(
                    Command::Admitted(ticket, Box::new(command)),
                    Some(responder),
                )
                .await
            {
                super::metrics::sample("write.proposal_failed", || format!("{error:?}"));
                count(&proposal_metrics.write_proposal);
                return failure(JournalError::Unavailable);
            }
            match response.await {
                Ok(Ok(response)) => {
                    proposal_metrics.commit_duration.observe(started.elapsed());
                    Reply::Decision(response.data)
                }
                Ok(Err(ClientWriteError::ForwardToLeader(leader))) => {
                    leader_reply(leader.leader_id)
                }
                other => {
                    super::metrics::sample("write.proposal_failed", || format!("{other:?}"));
                    count(&proposal_metrics.write_proposal);
                    failure(JournalError::Unavailable)
                }
            }
        });
        timeout(REQUEST_TIMEOUT, proposal)
            .await
            .ok()
            .and_then(Result::ok)
            .unwrap_or_else(|| {
                count(&metrics.write_timeout);
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
            super::metrics::count(&self.state.metrics().head_queue);
        } else if let Ok(Ok(reply)) = timeout(REQUEST_TIMEOUT, receive).await {
            return reply;
        } else {
            super::metrics::count(&self.state.metrics().head_timeout);
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

    /// Answers `Request::Written` from state that includes every entry
    /// committed before the request, like a linearizable head.
    async fn written(&self, fence: Fence, at: Lsn, payloads: Vec<Bytes>) -> Reply {
        if let Err(reply) = self.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        Reply::Decision(
            self.state
                .written(fence.epoch, at, payloads)
                .await
                .map(Outcome::At)
                .into(),
        )
    }

    async fn recovery_fence(&self) -> Reply {
        if let Err(reply) = self.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        Reply::Decision(
            self.state
                .recovery_fence()
                .map(Outcome::RecoveryFence)
                .into(),
        )
    }

    async fn read(
        &self,
        from: Lsn,
        limit: usize,
        wait_ms: u32,
        minimum_head: Lsn,
        offload: Option<&offload::Offloader>,
    ) -> Outcome {
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
            if self.state.remote(from).is_some() {
                // The store still holds records the writer trimmed, and a
                // follower may not have applied the latest trim. Only the
                // leader, after a read barrier that applies every committed
                // trim, serves from the store; it then checks the floor
                // again. Others answer `Unavailable`, and the client asks
                // the leader.
                let Some(offload) = offload else {
                    return Outcome::Refused(JournalError::Unavailable);
                };
                if self.raft.metrics().borrow_watched().state != openraft::ServerState::Leader
                    || self
                        .barrier(Instant::now() + REQUEST_TIMEOUT)
                        .await
                        .is_err()
                {
                    return Outcome::Refused(JournalError::Unavailable);
                }
                if let Some(remote) = self.state.remote(from) {
                    return offload
                        .read(self.genesis.stream, remote, limit)
                        .await
                        .map(Outcome::Page)
                        .into();
                }
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

/// Proposals in flight for at least this long count as slow.
pub(super) const SLOW_PROPOSAL: Duration = Duration::from_secs(1);

/// One stream's proposals in flight and when each started. A stream holds
/// at most its pending-write limit, so a scrape scans few entries.
#[derive(Default)]
struct Proposals(parking_lot::Mutex<HashMap<uuid::Uuid, std::time::Instant>>);

impl Proposals {
    /// The proposals in flight for at least `SLOW_PROPOSAL`, and the age of
    /// the oldest one in flight.
    fn slow(&self) -> (u64, Duration) {
        let proposals = self.0.lock();
        let mut slow = 0;
        let mut oldest = Duration::ZERO;
        for started in proposals.values() {
            let age = started.elapsed();
            slow += u64::from(age >= SLOW_PROPOSAL);
            oldest = oldest.max(age);
        }
        (slow, oldest)
    }
}

/// Registers a proposal while it runs; dropping it, however the proposal
/// ends, removes it and counts it when it was slow.
struct InFlight {
    proposals: Arc<Proposals>,
    ticket: uuid::Uuid,
    started: std::time::Instant,
    metrics: Arc<super::metrics::Metrics>,
}

impl InFlight {
    fn start(
        proposals: &Arc<Proposals>,
        ticket: uuid::Uuid,
        started: std::time::Instant,
        metrics: Arc<super::metrics::Metrics>,
    ) -> Self {
        proposals.0.lock().insert(ticket, started);
        Self {
            proposals: proposals.clone(),
            ticket,
            started,
            metrics,
        }
    }
}

impl Drop for InFlight {
    fn drop(&mut self) {
        self.proposals.0.lock().remove(&self.ticket);
        if self.started.elapsed() >= SLOW_PROPOSAL {
            super::metrics::count(&self.metrics.slow_proposals);
        }
    }
}

fn failure(error: JournalError) -> Reply {
    Reply::Decision(Outcome::Refused(error))
}

fn describe_audit_reply(reply: &Reply) -> String {
    match reply {
        Reply::Decision(Outcome::Refused(error)) => format!("refused:{error:?}"),
        Reply::Decision(Outcome::At(lsn)) => format!("ok:head={}", lsn.0),
        Reply::Decision(Outcome::Configuration(cfg)) => format!("ok:revision={}", cfg.revision),
        Reply::Decision(_) => "ok".to_owned(),
        Reply::Leader(Some(leader)) => format!("forward:{leader}"),
        Reply::Leader(None) => "no_leader".to_owned(),
        _ => "ok".to_owned(),
    }
}

fn describe_audit_result(result: &io::Result<Reply>) -> String {
    match result {
        Ok(reply) => describe_audit_reply(reply),
        Err(error) => format!("error:{error}"),
    }
}
