//! In-process consensus cluster controller for randomized fault injection.

use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    sync::{Arc, atomic::Ordering},
    time::Duration,
};

use bytes::Bytes;
use journal_contract::{JournalError, Lsn, StreamId};
use openraft::async_runtime::WatchReceiver;
use rcgen::ExtendedKeyUsagePurpose::{ClientAuth, ServerAuth};
use tokio::{net::TcpListener, time::timeout};
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

use super::faults::FaultNetwork;
use crate::stream::consensus::Voters;
use crate::stream::{
    consensus::{
        Client, Config, Configuration, ConsensusJournal, Credentials, Domains, JournalConfig,
        Keepers,
        keeper::{Engine, Recovery, RecoveryReport},
        storage::{Authority, Provision, ReplicaFault, hex, sha256},
    },
    transport::tests::{ca, credentials_with_usages},
};

pub(super) const WRITER_A: &str = "urn:logkeeper:client:writer-a";
pub(super) const WRITER_B: &str = "urn:logkeeper:client:writer-b";
pub(super) const READER: &str = "urn:logkeeper:client:reader";

/// Synthetic client source IDs for `TransportFilter`.
pub(super) const CLIENT_A_ID: Uuid = Uuid::from_u128(0x1001);
pub(super) const CLIENT_B_ID: Uuid = Uuid::from_u128(0x1002);
pub(super) const CLIENT_R_ID: Uuid = Uuid::from_u128(0x1003);

pub(super) const WAIT: Duration = Duration::from_secs(12);

/// Cluster startup parameters controlled by each seed.
#[derive(Clone, Debug)]
pub(super) struct ClusterOptions {
    pub replicated_catalog: bool,
    pub park_after_secs: u64,
    pub repair_after_secs: u64,
    pub max_streams: usize,
    pub quota_bytes: u64,
    pub max_record_bytes: usize,
    pub client_deadline_ms: u64,
    /// Keepers accept a keeper ID reused on new media, as before media
    /// incarnations, which reopens the Raft amnesia bug.
    pub ignore_reused_ids: bool,
    /// Voters of every stream: 3, or 5 on a cluster that adds keepers 8
    /// and 9 (domains g and h) and finalizes the replication-factor
    /// version before the first create.
    pub replication: usize,
    /// Every keeper offloads to a directory store with small batches, a
    /// small lag bound and aggressive local retention.
    pub offload: bool,
}

impl Default for ClusterOptions {
    fn default() -> Self {
        Self {
            replicated_catalog: false,
            park_after_secs: 2,
            repair_after_secs: 2,
            max_streams: 32,
            quota_bytes: 512 * 1024,
            max_record_bytes: 4096,
            client_deadline_ms: 4_000,
            replication: 3,
            ignore_reused_ids: false,
            offload: false,
        }
    }
}

/// Which WAL crash cut to arm on a keeper.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum WalCrashKind {
    LeaderBeforeBoundary,
    LeaderAfterBoundary,
    LeaderFailedSync,
    LeaderTornFrame,
    FollowerBeforeSelection,
    FollowerAfterSelection,
    FollowerFailedSync,
    FollowerPartialSegment,
}

impl WalCrashKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::LeaderBeforeBoundary => "wal:leader_before_boundary",
            Self::LeaderAfterBoundary => "wal:leader_after_boundary",
            Self::LeaderFailedSync => "wal:leader_failed_sync",
            Self::LeaderTornFrame => "wal:leader_torn_frame",
            Self::FollowerBeforeSelection => "wal:follower_before_selection",
            Self::FollowerAfterSelection => "wal:follower_after_selection",
            Self::FollowerFailedSync => "wal:follower_failed_sync",
            Self::FollowerPartialSegment => "wal:follower_partial_segment",
        }
    }
}

/// Direct snapshot of one voter's local applied state for a stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct VoterSnapshot {
    pub keeper: Uuid,
    pub deleted: bool,
    pub floor: Lsn,
    pub head: Lsn,
    pub records: Vec<(Lsn, Bytes)>,
    /// The positions of `records` that are typed recovery entries.
    pub recoveries: std::collections::BTreeSet<Lsn>,
    pub configuration: Option<Configuration>,
}

struct Running {
    engine: Arc<Engine>,
    task: tokio::task::JoinHandle<io::Result<()>>,
}

impl Running {
    async fn spawn(
        config: Config,
        listeners: [TcpListener; 3],
        faults: &FaultNetwork,
        ignore_reused_ids: bool,
    ) -> Self {
        let engine = config.prepare(CancellationToken::new()).await.unwrap();
        if ignore_reused_ids {
            engine.ignore_reused_ids();
        }
        engine.set_transport_filter(Some(faults.filter()));
        let task = tokio::spawn(engine.clone().serve(listeners, None));
        Self { engine, task }
    }

    async fn stop_graceful(self) {
        self.engine.stop.cancel();
        // A keeper whose disk was faulted earlier may exit with an I/O error.
        let _ = self.task.await;
    }

    async fn stop_crash(self) {
        self.engine.crash.store(true, Ordering::Release);
        self.engine.stop.cancel();
        let _ = self.task.await;
    }
}

/// Seven in-process consensus keepers in distinct failure domains, nine for
/// five-voter streams, with fault injection wired into every RPC lane and
/// WAL disk.
pub(super) struct SimCluster {
    running: BTreeMap<Uuid, Running>,
    configs: BTreeMap<Uuid, Config>,
    pub keepers: Keepers,
    /// Four primary data keepers (indices 0..4).
    pub data_ids: [Uuid; 4],
    /// All keeper IDs: data keepers, catalog/spare keepers 5, 6, 7, and
    /// spares 8 and 9 for five-voter streams.
    pub all_ids: Vec<Uuid>,
    pub catalog: Uuid,
    pub catalog_voters: Option<Voters>,
    /// Keepers wiped and initialized again under their old IDs.
    pub wiped: BTreeSet<Uuid>,
    pub faults: FaultNetwork,
    pub options: ClusterOptions,
    creds_a: Credentials,
    creds_b: Credentials,
    creds_r: Credentials,
    _dir: tempfile::TempDir,
}

/// The harness's offload store: small objects and batches, a lag bound a
/// short outage reaches, and retention that keeps about 1 KiB per stream.
fn offload_config(directory: &std::path::Path) -> crate::stream::consensus::OffloadConfig {
    serde_json::from_value(serde_json::json!({
        "url": format!("file://{}", directory.display()),
        "batch_bytes": 1024,
        "batch_interval_ms": 150,
        "max_lag_bytes": 2048,
        "retain_local_bytes": 1024,
    }))
    .unwrap()
}

impl SimCluster {
    /// Takes the offload store away (its directory becomes a file) or
    /// brings it back.
    pub fn store_outage(&self, down: bool) {
        let store = self._dir.path().join("offload");
        let away = self._dir.path().join("offload-away");
        if down && store.is_dir() {
            std::fs::rename(&store, &away).unwrap();
            std::fs::write(&store, b"store outage").unwrap();
        } else if !down && away.is_dir() {
            std::fs::remove_file(&store).unwrap();
            std::fs::rename(&away, &store).unwrap();
        }
    }

    /// The offload store as the keepers see it.
    pub fn offload_store(&self) -> Option<crate::stream::consensus::offload::Store> {
        self.options.offload.then(|| {
            crate::stream::consensus::offload::Store::open(&offload_config(
                &self._dir.path().join("offload"),
            ))
            .unwrap()
        })
    }

    /// The offload counters summed over the running keepers.
    pub fn offload_counts(&self) -> (u64, u64) {
        use std::sync::atomic::Ordering::Relaxed;
        self.running
            .values()
            .filter_map(|running| running.engine.offload.as_ref())
            .fold((0, 0), |(reads, refused), offload| {
                let metrics = &offload.store.metrics;
                (
                    reads + metrics.remote_reads.load(Relaxed),
                    refused + metrics.backpressured_appends.load(Relaxed),
                )
            })
    }

    pub async fn start(seed: u64, options: ClusterOptions) -> Self {
        let faults = FaultNetwork::new(seed);
        let dir = tempfile::tempdir().unwrap();
        let roots = dir.path().join("ca.pem");
        let ca = ca(&roots);
        let data_ids = [1, 2, 3, 4].map(Uuid::from_u128);
        let catalog = Uuid::from_u128(5);
        let keeper_count = if options.replication == 5 { 9 } else { 7 };
        let all_ids = (1..=keeper_count).map(Uuid::from_u128).collect::<Vec<_>>();
        let catalog_voters = options
            .replicated_catalog
            .then_some(Voters::from([5, 6, 7].map(Uuid::from_u128)));
        let domains: Domains = all_ids
            .iter()
            .copied()
            .zip(["a", "b", "c", "d", "directory", "e", "f", "g", "h"])
            .map(|(id, domain)| (id, domain.into()))
            .collect();
        let enrollment = dir.path().join("registry");
        std::fs::create_dir(&enrollment).unwrap();
        std::fs::write(
            enrollment.join("placement.json"),
            serde_json::to_vec(&Authority {
                catalog,
                domains: domains.clone(),
                retired: BTreeSet::new(),
            })
            .unwrap(),
        )
        .unwrap();

        let mut keepers = Keepers::new();
        let mut peers = Keepers::new();
        let mut bulk = Keepers::new();
        let mut listeners = BTreeMap::new();
        for id in all_ids.iter().copied() {
            let app = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let control = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let snapshot = TcpListener::bind("127.0.0.1:0").await.unwrap();
            keepers.insert(id, app.local_addr().unwrap().into());
            peers.insert(id, control.local_addr().unwrap().into());
            bulk.insert(id, snapshot.local_addr().unwrap().into());
            listeners.insert(id, [app, control, snapshot]);
        }

        let mut configs = BTreeMap::new();
        let mut running = BTreeMap::new();
        for (id, listener) in listeners {
            let tls = credentials_with_usages(
                dir.path(),
                &id.to_string(),
                &format!("urn:logkeeper:keeper:{id}"),
                vec![ClientAuth, ServerAuth],
                &ca,
                &roots,
            );
            let config = Config {
                keeper: id,
                listen: keepers[&id].socket_addr().unwrap(),
                data: dir.path().join(format!("data-{id}")),
                tls,
                keepers: keepers.clone(),
                peers: peers.clone(),
                bulk: bulk.clone(),
                domains: domains.clone(),
                enrollment: enrollment.clone(),
                catalog,
                catalog_voters,
                allow_single_catalog: true,
                lease_millis: 2_000,
                lease_drift_margin_millis: 200,
                readers: vec![WRITER_A.into(), WRITER_B.into(), READER.into()],
                writers: vec![WRITER_A.into(), WRITER_B.into()],
                administrators: vec![WRITER_A.into()],
                max_streams: options.max_streams,
                repair_after_secs: options.repair_after_secs,
                park_after_secs: options.park_after_secs,
                snapshot_send_bytes_per_second: 0,
                scrub_bytes_per_second: 0,
                async_append: std::env::var("LOGKEEPER_ASYNC_APPEND")
                    .map_or(true, |value| value != "0"),
                timed_original: None,
                timed_authority: None,
                log_format: Default::default(),
                admin: None,
                offload: options
                    .offload
                    .then(|| offload_config(&dir.path().join("offload"))),
                sync_mode: crate::server::durability::SyncMode::Fsync,
                retired: BTreeSet::new(),
            };
            provision(&config);
            config.initialize().unwrap();
            running.insert(
                id,
                Running::spawn(config.clone(), listener, &faults, options.ignore_reused_ids).await,
            );
            configs.insert(id, config);
        }

        let creds_a = credentials_with_usages(
            dir.path(),
            "writer-a",
            WRITER_A,
            vec![ClientAuth],
            &ca,
            &roots,
        );
        let creds_b = credentials_with_usages(
            dir.path(),
            "writer-b",
            WRITER_B,
            vec![ClientAuth],
            &ca,
            &roots,
        );
        let creds_r =
            credentials_with_usages(dir.path(), "reader", READER, vec![ClientAuth], &ca, &roots);

        Self {
            running,
            configs,
            keepers,
            data_ids,
            all_ids,
            catalog,
            catalog_voters,
            wiped: BTreeSet::new(),
            faults,
            options,
            creds_a,
            creds_b,
            creds_r,
            _dir: dir,
        }
    }

    pub fn journal_config(&self, voters: Voters, domain: Option<&str>) -> JournalConfig {
        JournalConfig {
            keepers: self.keepers.clone(),
            catalog: self.catalog,
            catalog_voters: self.catalog_voters,
            voters: Some(voters),
            replication_factor: voters.len(),
            placement: None,
            draining: BTreeSet::new(),
            retired: BTreeSet::new(),
            quota_bytes: self.options.quota_bytes,
            max_record_bytes: self.options.max_record_bytes,
            deadline_ms: self.options.client_deadline_ms,
            domain: domain.map(str::to_owned),
        }
    }

    pub fn journal(&self, principal: &str, voters: Voters) -> ConsensusJournal {
        let (creds, source) = self.creds_for(principal);
        let config = self.journal_config(voters, None);
        let journal = ConsensusJournal::new(creds, &config).unwrap();
        journal
            .client()
            .set_transport_filter(source, Some(self.faults.filter()));
        journal
    }

    /// Waits until every running keeper holds an enforced lease.
    pub async fn await_leases(&self) {
        let end = tokio::time::Instant::now() + std::time::Duration::from_secs(30);
        while !self
            .running
            .values()
            .all(|running| running.engine.lease.enforced() && running.engine.lease.valid())
        {
            assert!(
                tokio::time::Instant::now() < end,
                "keepers hold no enforced lease"
            );
            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
        }
    }

    /// Finalizes the cluster version through the catalog and sets it on every
    /// running keeper, as each keeper's 10 s version loop would.
    pub async fn finalize_version(&self) {
        let version = crate::stream::consensus::CLUSTER_VERSION_CURRENT;
        let client = self.probe_client();
        let end = tokio::time::Instant::now() + std::time::Duration::from_secs(30);
        loop {
            match client.finalize_version(version).await {
                Ok(finalized) => break assert_eq!(finalized, version),
                Err(journal_contract::JournalError::Unavailable)
                    if tokio::time::Instant::now() < end =>
                {
                    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                }
                Err(error) => panic!("finalize refused: {error:?}"),
            }
        }
        for running in self.running.values() {
            running.engine.disk.set_write_version(version);
        }
    }

    /// Unfiltered client used for final convergence and invariant probing after healing.
    pub fn probe_client(&self) -> Client {
        let client = Client::new(&self.creds_a, self.keepers.clone(), self.catalog, WAIT).unwrap();
        match self.catalog_voters {
            Some(voters) => client.with_catalog_voters(voters),
            None => client,
        }
    }

    fn creds_for(&self, principal: &str) -> (&Credentials, Uuid) {
        match principal {
            WRITER_A => (&self.creds_a, CLIENT_A_ID),
            WRITER_B => (&self.creds_b, CLIENT_B_ID),
            READER => (&self.creds_r, CLIENT_R_ID),
            other => panic!("unknown test principal {other}"),
        }
    }

    pub fn is_running(&self, id: Uuid) -> bool {
        self.running
            .get(&id)
            .is_some_and(|server| !server.task.is_finished() && server.engine.disk.healthy())
    }

    pub async fn stop_graceful(&mut self, id: Uuid) {
        if let Some(server) = self.running.remove(&id) {
            server.stop_graceful().await;
            self.faults.hit("fault:stop_graceful");
        }
    }

    pub async fn crash(&mut self, id: Uuid) {
        if let Some(server) = self.running.remove(&id) {
            server.stop_crash().await;
            self.faults.hit("fault:crash");
        }
    }

    /// Removes any keeper whose WAL thread died from an injected WAL fault and
    /// returns their IDs so the caller can restart them cleanly.
    pub async fn reap_crashed(&mut self) -> Vec<Uuid> {
        let dead: Vec<Uuid> = self
            .running
            .iter()
            .filter(|(_, s)| s.task.is_finished() || !s.engine.disk.healthy())
            .map(|(id, _)| *id)
            .collect();
        for id in &dead {
            if let Some(server) = self.running.remove(id) {
                server.stop_crash().await;
            }
        }
        dead
    }

    pub async fn restart(&mut self, id: Uuid) {
        if let Some(existing) = self.running.remove(&id) {
            existing.stop_crash().await;
        }
        let config = self.configs[&id].clone();
        let listeners = [
            crate::stream::consensus::keeper::bind_listener(config.listen)
                .await
                .unwrap(),
            crate::stream::consensus::keeper::bind_listener(config.peers[&id].bind_addr())
                .await
                .unwrap(),
            crate::stream::consensus::keeper::bind_listener(config.bulk[&id].bind_addr())
                .await
                .unwrap(),
        ];
        self.running.insert(
            id,
            Running::spawn(
                config,
                listeners,
                &self.faults,
                self.options.ignore_reused_ids,
            )
            .await,
        );
        self.faults.hit("fault:restart");
    }

    pub async fn restart_all_stopped(&mut self) {
        self.reap_crashed().await;
        for id in self.all_ids.clone() {
            if !self.running.contains_key(&id) {
                self.restart(id).await;
            }
        }
    }

    /// Arms a WAL crash cut on `id` for `stream`.
    pub fn arm_wal_fault(&self, id: Uuid, stream: StreamId, kind: WalCrashKind) -> bool {
        let Some(server) = self.running.get(&id) else {
            return false;
        };
        let disk = &server.engine.disk;
        match kind {
            WalCrashKind::LeaderBeforeBoundary => disk.interrupt_next(stream, 2),
            WalCrashKind::LeaderAfterBoundary => disk.interrupt_next(stream, 3),
            WalCrashKind::LeaderFailedSync => disk.interrupt_next(stream, 5),
            WalCrashKind::LeaderTornFrame => disk.interrupt_next(stream, 6),
            WalCrashKind::FollowerBeforeSelection => {
                disk.fail_replication_at(stream, ReplicaFault::BeforeSelection)
            }
            WalCrashKind::FollowerAfterSelection => {
                disk.fail_replication_at(stream, ReplicaFault::AfterSelection)
            }
            WalCrashKind::FollowerFailedSync => {
                disk.fail_replication_at(stream, ReplicaFault::FailedSync)
            }
            WalCrashKind::FollowerPartialSegment => {
                disk.fail_replication_at(stream, ReplicaFault::PartialSegment)
            }
        }
        self.faults.hit(kind.name());
        true
    }

    pub fn set_slow_disk(&self, id: Uuid, delay: Duration) {
        if let Some(server) = self.running.get(&id) {
            server.engine.disk.set_wal_delay(delay);
            if !delay.is_zero() {
                self.faults.hit("fault:slow_disk");
            }
        }
    }

    /// Simulates ordinary disk exhaustion (80 MiB left: below `ORDINARY_FLOOR`
    /// of 88 MiB so `accepts_streams()` is false, ordinary writes fail and E5
    /// sheds leadership, while leaving the protected `PROTOCOL_FLOOR` intact).
    pub fn set_disk_full(&self, id: Uuid, full: bool) {
        if let Some(server) = self.running.get(&id) {
            server
                .engine
                .disk
                .space
                .set_available(if full { 80 * 1024 * 1024 } else { u64::MAX });
            if full {
                self.faults.hit("fault:disk_full");
            }
        }
    }

    /// Simulates complete disk exhaustion (`0` bytes left, below `PROTOCOL_FLOOR`).
    pub fn set_disk_zero(&self, id: Uuid, zero: bool) {
        if let Some(server) = self.running.get(&id) {
            server
                .engine
                .disk
                .space
                .set_available(if zero { 0 } else { u64::MAX });
        }
    }

    pub fn clear_disk_faults(&self) {
        for server in self.running.values() {
            server.engine.disk.set_wal_delay(Duration::ZERO);
            server.engine.disk.space.set_available(u64::MAX);
        }
    }

    /// Destroys both data and enrollment volumes of `id`, re-initializes it
    /// under the SAME keeper ID, and restarts it (amnesia scenario).
    pub async fn wipe_and_reinitialize(&mut self, id: Uuid) {
        if let Some(server) = self.running.remove(&id) {
            server.stop_crash().await;
        }
        let config = self.configs[&id].clone();
        let _ = std::fs::remove_dir_all(&config.data);
        for suffix in ["enrolled", "wal", "boundary", "incarnations.json"] {
            let _ = std::fs::remove_file(
                config
                    .enrollment
                    .join(format!("{}.{suffix}", config.keeper)),
            );
        }
        config.initialize().unwrap();
        self.wiped.insert(id);
        self.faults.hit("fault:wipe_and_reinit");
        self.restart(id).await;
    }

    /// Runs the offline `recover-stream` command on `survivor` for `stream`
    /// (stopping `survivor` first, recovering with `--acknowledge-data-loss`,
    /// then restarting `survivor`).
    pub async fn recover_stream_offline(
        &mut self,
        survivor: Uuid,
        lost: &[Uuid],
        stream: StreamId,
    ) -> io::Result<RecoveryReport> {
        self.stop_graceful(survivor).await;
        let mut req = Recovery::default();
        req.acknowledge_data_loss = true;
        req.lost = Some(lost.to_vec());
        // Explore histories created by older operator recovery tools, whose
        // replaced keepers can still restart as part of the fault schedule.
        req.legacy_unfenced = true;
        let report = self.configs[&survivor].recover_stream(stream, req).await;
        self.restart(survivor).await;
        if report.is_ok() {
            self.faults.hit("op:recover_stream");
        }
        report
    }

    /// Returns the current leader of `stream`, if any running keeper currently leads it.
    pub async fn leader(&self, stream: StreamId) -> Option<Uuid> {
        for (id, server) in &self.running {
            if let Some(group) = server.engine.groups.lock().await.get(&stream)
                && group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
            {
                return Some(*id);
            }
        }
        None
    }

    /// Whether `stream` is currently parked on every keeper in `voters`.
    pub async fn is_parked_on(&self, stream: StreamId, voters: &[Uuid]) -> bool {
        for id in voters {
            let Some(server) = self.running.get(id) else {
                return false;
            };
            if !server.engine.parked.read().contains_key(&stream)
                || server.engine.groups.lock().await.contains_key(&stream)
            {
                return false;
            }
        }
        true
    }

    /// Reads the complete applied state of `stream` directly from `keeper`'s
    /// local `StateMachine` (open, closed-deleted, or parked).
    pub async fn inspect_voter(&self, keeper: Uuid, stream: StreamId) -> Option<VoterSnapshot> {
        let server = self.running.get(&keeper)?;
        if !server.engine.disk.healthy() {
            return None;
        }
        // Once a deleted stream's group closes after DELETED_GROUP_GRACE, its
        // closed_states handle is suspended (`state.healthy() == false`) while
        // `engine.deleted` holds the tombstone.
        if server.engine.deleted.read().contains(&stream) {
            let configuration = server
                .engine
                .closed_states
                .lock()
                .get(&stream)
                .and_then(|s| s.finalized());
            return Some(VoterSnapshot {
                keeper,
                deleted: true,
                floor: Lsn(1),
                head: Lsn(0),
                records: Vec::new(),
                recoveries: Default::default(),
                configuration,
            });
        }
        let open = server
            .engine
            .groups
            .lock()
            .await
            .get(&stream)
            .map(|group| group.state.clone());
        let state = match open {
            Some(state) => state,
            None => server.engine.closed_state(stream).await?,
        };
        if !state.healthy() {
            return None;
        }
        let configuration = state.finalized();
        match state.head() {
            Err(JournalError::Deleted) => Some(VoterSnapshot {
                keeper,
                deleted: true,
                floor: Lsn(1),
                head: Lsn(0),
                records: Vec::new(),
                recoveries: Default::default(),
                configuration,
            }),
            Err(JournalError::NotFound) | Err(_) => None,
            Ok(_head) => {
                // Records below the local floor were offloaded and dropped
                // by retention, deterministically on every voter: compare
                // the local copies from there.
                let start = state.offload_view().map_or(Lsn(1), |view| view.local_floor);
                let first_page = match state.page(start, 512).await {
                    Ok(page) => page,
                    Err(JournalError::Trimmed { floor }) => state.page(floor, 512).await.ok()?,
                    Err(JournalError::Deleted) => {
                        return Some(VoterSnapshot {
                            keeper,
                            deleted: true,
                            floor: Lsn(1),
                            head: Lsn(0),
                            records: Vec::new(),
                            recoveries: Default::default(),
                            configuration,
                        });
                    }
                    Err(_) => return None,
                };
                let floor = first_page.floor;
                let observed_head = first_page.head;
                // Read the dropped part back from the store through this
                // keeper's own store path, so durability covers it too.
                let mut records = Vec::new();
                let mut recoveries = std::collections::BTreeSet::new();
                let mut below = floor;
                while below < start {
                    let remote = state.remote(below)?;
                    let page = server
                        .engine
                        .offload
                        .as_ref()?
                        .read(stream, remote, 512)
                        .await
                        .ok()?;
                    let Some((last, _)) = page.records.last() else {
                        return None;
                    };
                    below = Lsn(last.0 + 1);
                    recoveries.extend(page.recoveries.iter().map(|(lsn, _)| *lsn));
                    records.extend(page.records);
                }
                recoveries.extend(first_page.recoveries.iter().map(|(lsn, _)| *lsn));
                records.extend(first_page.records);
                let mut next = records
                    .last()
                    .map(|(lsn, _)| Lsn(lsn.0 + 1))
                    .unwrap_or(Lsn(observed_head.0 + 1));
                while next <= observed_head {
                    let page = state.page(next, 512).await.ok()?;
                    if page.records.is_empty() {
                        break;
                    }
                    next = Lsn(page.records.last().unwrap().0.0 + 1);
                    recoveries.extend(page.recoveries.iter().map(|(lsn, _)| *lsn));
                    records.extend(page.records);
                }
                Some(VoterSnapshot {
                    keeper,
                    deleted: false,
                    floor,
                    head: observed_head,
                    records,
                    recoveries,
                    configuration,
                })
            }
        }
    }

    /// Waits for every voter in `voters` to converge to the same applied state
    /// for `stream` (open or deleted) after faults have healed.
    pub async fn wait_converged(
        &self,
        stream: StreamId,
        voters: &Voters,
        limit: Duration,
    ) -> Result<Vec<VoterSnapshot>, Vec<Option<VoterSnapshot>>> {
        let probe = self.probe_client();
        let outcome = timeout(limit, async {
            let mut stopped_since = BTreeMap::new();
            loop {
                // Bail out early if any voter's OpenRaft core stays stopped
                // (a panic, or a storage error its keeper does not recover).
                for &v in voters {
                    let stopped =
                        match self.running.get(&v) {
                            Some(server) => {
                                server.engine.groups.lock().await.get(&stream).is_some_and(
                                    |group| {
                                        group.raft.metrics().borrow_watched().running_state.is_err()
                                    },
                                )
                            }
                            None => false,
                        };
                    if !stopped {
                        stopped_since.remove(&v);
                    } else if stopped_since
                        .entry(v)
                        .or_insert_with(tokio::time::Instant::now)
                        .elapsed()
                        > Duration::from_secs(5)
                    {
                        return None;
                    }
                }
                // Issue a fresh head so parked streams reopen and followers
                // receive the latest commit index from the leader.
                let expected_head = probe.head(stream).await;
                let mut snaps = Vec::with_capacity(voters.len());
                for &v in voters {
                    snaps.push(self.inspect_voter(v, stream).await);
                }
                if let Some(all) = snaps.iter().cloned().collect::<Option<Vec<_>>>()
                    && let [a, rest @ ..] = &all[..]
                {
                    let head_matches = match expected_head {
                        Ok(h) => !a.deleted && a.head == h,
                        Err(JournalError::Deleted) => a.deleted,
                        _ => false,
                    };
                    if head_matches
                        && rest.iter().all(|b| {
                            a.deleted == b.deleted
                                && a.floor == b.floor
                                && a.head == b.head
                                && a.records == b.records
                        })
                    {
                        return Some(all);
                    }
                }
                tokio::time::sleep(Duration::from_millis(40)).await;
            }
        })
        .await;
        match outcome {
            Ok(Some(snaps)) => Ok(snaps),
            Ok(None) | Err(_) => {
                let mut snaps = Vec::with_capacity(voters.len());
                for &v in voters {
                    snaps.push(self.inspect_voter(v, stream).await);
                }
                Err(snaps)
            }
        }
    }

    pub async fn stop_all(&mut self) {
        self.faults.heal_all();
        self.clear_disk_faults();
        for (_, server) in std::mem::take(&mut self.running) {
            server.stop_graceful().await;
        }
    }
}

fn provision(config: &Config) {
    let provision = Provision {
        keeper: config.keeper,
        data: config
            .data
            .parent()
            .unwrap()
            .canonicalize()
            .unwrap()
            .join(config.data.file_name().unwrap()),
        domain: config.domains[&config.keeper].clone(),
        certificate_sha256: hex(
            &sha256(std::fs::File::open(&config.tls.certificate).unwrap()).unwrap(),
        ),
    };
    std::fs::write(
        config
            .enrollment
            .join(format!("{}.provision.json", config.keeper)),
        serde_json::to_vec(&provision).unwrap(),
    )
    .unwrap();
}
