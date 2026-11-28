use super::*;
use bytes::Bytes;
use journal_contract::Epoch;
use openraft::{EntryPayload, async_runtime::WatchReceiver, raft::AppendEntriesRequest};
use rcgen::ExtendedKeyUsagePurpose::{ClientAuth, ServerAuth};
use uuid::Uuid;

use crate::stream::consensus::Voters;
use crate::stream::{
    consensus::{
        Client, Entry, Fence, LogId, RaftTypes,
        network::{AppendReply, Frame, PeerRequest},
    },
    transport::tests::{ca, credentials_with_usages},
};
use std::sync::atomic::{AtomicBool, Ordering};

mod authority;
mod catalog;
mod compaction;
mod immutable;
mod incarnation;
mod lifecycle;
mod model_counterexamples;
mod offload;
mod operator;
mod ops;
mod park;
mod recovery;
mod repair;
mod replication;
mod upgrades;

pub(super) type RejectAppend =
    Box<dyn Fn(StreamId, NodeId, &AppendEntriesRequest<RaftTypes>) -> bool + Send + Sync>;

const OWNER: &str = "urn:logkeeper:client:writer";
const OTHER: &str = "urn:logkeeper:client:other";
const WAIT: Duration = Duration::from_secs(12);

struct Running {
    engine: Arc<Engine>,
    task: tokio::task::JoinHandle<io::Result<()>>,
}

impl Running {
    async fn spawn(config: Config, listeners: [TcpListener; 3]) -> Self {
        Self::spawn_with(config, listeners, |_| ()).await
    }

    /// Spawns a keeper after `before` adjusts its engine.
    async fn spawn_with(
        config: Config,
        listeners: [TcpListener; 3],
        before: impl FnOnce(&Engine),
    ) -> Self {
        let admin_listener = match &config.admin {
            Some(admin) => Some((
                super::bind_listener(admin.listen).await.unwrap(),
                admin.mtls,
            )),
            None => None,
        };
        let engine = config.prepare(CancellationToken::new()).await.unwrap();
        before(&engine);
        let task = tokio::spawn(engine.clone().serve(listeners, admin_listener));
        Self { engine, task }
    }

    async fn stop(self) {
        self.engine.stop.cancel();
        self.task.await.unwrap().unwrap();
    }
}

struct Cluster {
    running: BTreeMap<Uuid, Running>,
    configs: BTreeMap<Uuid, Config>,
    keepers: Keepers,
    ids: [Uuid; 4],
    catalog: Uuid,
    catalog_voters: Option<Voters>,
    credentials: Credentials,
    other: Credentials,
    #[cfg(unix)]
    certificate_issuer: rcgen::Issuer<'static, rcgen::KeyPair>,
    _dir: tempfile::TempDir,
}

impl Cluster {
    async fn start() -> Self {
        Self::start_domains(["a", "b", "c", "d"]).await
    }

    async fn start_domains(domains: [&str; 4]) -> Self {
        Self::start_with(domains, None).await
    }

    /// Hosts the catalog as a consensus stream on keepers 5, 6 and 7. The
    /// catalog keeper 5 seeds it.
    async fn start_replicated() -> Self {
        let voters = Voters::from([5, 6, 7].map(Uuid::from_u128));
        Self::start_with(["a", "b", "c", "d"], Some(voters)).await
    }

    async fn start_with(domains: [&str; 4], catalog_voters: Option<Voters>) -> Self {
        Self::start_addressed(domains, catalog_voters, false, 0).await
    }

    /// Adds `extra` keepers 8, 9, ... in their own domains g, h, ..., so
    /// five-voter streams have spare keepers to move to.
    async fn start_wide(extra: u128) -> Self {
        Self::start_addressed(["a", "b", "c", "d"], None, false, extra).await
    }

    /// Lists every keeper in the inventory as `localhost:port`, a DNS name
    /// resolved at each connect, instead of an IP address.
    async fn start_named() -> Self {
        Self::start_addressed(["a", "b", "c", "d"], None, true, 0).await
    }

    async fn start_addressed(
        domains: [&str; 4],
        catalog_voters: Option<Voters>,
        named: bool,
        extra: u128,
    ) -> Self {
        Self::start_configured(domains, catalog_voters, named, None, extra).await
    }

    /// Starts every keeper with `offload`, without the restart that turning
    /// it on later needs.
    async fn start_configured(
        domains: [&str; 4],
        catalog_voters: Option<Voters>,
        named: bool,
        offload: Option<crate::stream::consensus::OffloadConfig>,
        extra: u128,
    ) -> Self {
        let address = |listener: &TcpListener| -> crate::stream::consensus::Address {
            let local = listener.local_addr().unwrap();
            if named {
                format!("localhost:{}", local.port()).parse().unwrap()
            } else {
                local.into()
            }
        };
        crate::stream::consensus::logging::test_warnings::install();
        let dir = tempfile::tempdir().unwrap();
        let roots = dir.path().join("ca.pem");
        let ca = ca(&roots);
        let ids = [1, 2, 3, 4].map(Uuid::from_u128);
        let catalog = Uuid::from_u128(5);
        let roster = ids
            .into_iter()
            .chain([catalog, Uuid::from_u128(6), Uuid::from_u128(7)])
            .chain((8..8 + extra).map(Uuid::from_u128));
        let extra_domains = (0..extra).map(|index| ((b'g' + index as u8) as char).to_string());
        let domains: Domains = roster
            .clone()
            .zip(
                domains
                    .into_iter()
                    .chain(["directory", "e", "f"])
                    .map(str::to_owned)
                    .chain(extra_domains),
            )
            .map(|(id, domain)| (id, domain))
            .collect();
        let enrollment = dir.path().join("registry");
        std::fs::create_dir(&enrollment).unwrap();
        std::fs::write(
            enrollment.join("placement.json"),
            serde_json::to_vec(&Authority {
                catalog,
                domains: domains.clone(),
                retired: Default::default(),
            })
            .unwrap(),
        )
        .unwrap();
        let mut keepers = Keepers::new();
        let mut peers = Keepers::new();
        let mut bulk = Keepers::new();
        let mut listeners = BTreeMap::new();
        for id in roster {
            let app = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let control = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let snapshot = TcpListener::bind("127.0.0.1:0").await.unwrap();
            keepers.insert(id, address(&app));
            peers.insert(id, address(&control));
            bulk.insert(id, address(&snapshot));
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
                listen: listener[0].local_addr().unwrap(),
                data: dir.path().join(format!("data-{id}")),
                tls,
                keepers: keepers.clone(),
                peers: peers.clone(),
                bulk: bulk.clone(),
                domains: domains.clone(),
                retired: Default::default(),
                enrollment: enrollment.clone(),
                catalog,
                catalog_voters,
                allow_single_catalog: true,
                lease_millis: 2_000,
                lease_drift_margin_millis: 200,
                readers: vec![OWNER.into(), OTHER.into()],
                writers: vec![OWNER.into(), OTHER.into()],
                administrators: vec![OWNER.into()],
                max_streams: default_max_streams(),
                repair_after_secs: 2,
                park_after_secs: 3600,
                snapshot_send_bytes_per_second: 0,
                scrub_bytes_per_second: 0,
                async_append: std::env::var("LOGKEEPER_ASYNC_APPEND")
                    .map_or(true, |value| value != "0"),
                timed_original: None,
                authenticated_log: None,
                sync_mode: SyncMode::Fsync,
                timed_authority: None,
                log_format: Default::default(),
                admin: None,
                offload: offload.clone(),
            };
            provision(&config);
            config.initialize().unwrap();
            running.insert(id, Running::spawn(config.clone(), listener).await);
            configs.insert(id, config);
        }
        let credentials =
            credentials_with_usages(dir.path(), "writer", OWNER, vec![ClientAuth], &ca, &roots);
        let other =
            credentials_with_usages(dir.path(), "other", OTHER, vec![ClientAuth], &ca, &roots);
        Self {
            running,
            configs,
            keepers,
            ids,
            catalog,
            catalog_voters,
            credentials,
            other,
            #[cfg(unix)]
            certificate_issuer: ca,
            _dir: dir,
        }
    }

    fn client(&self, credentials: &Credentials) -> Client {
        self.client_within(credentials, WAIT)
    }

    fn client_within(&self, credentials: &Credentials, deadline: Duration) -> Client {
        let client =
            Client::new(credentials, self.keepers.clone(), self.catalog, deadline).unwrap();
        match self.catalog_voters {
            Some(voters) => client.with_catalog_voters(voters),
            None => client,
        }
    }

    fn peer_rpc(&self, sender: Uuid, lane: Lane) -> Rpc {
        let config = &self.configs[&sender];
        let routes = if lane == Lane::Control {
            &config.peers
        } else {
            &config.bulk
        };
        Rpc::new(
            config
                .tls
                .peer_protocol(KeeperId(sender.as_u128()), lane.alpn())
                .unwrap(),
            routes.clone(),
            lane,
        )
    }

    async fn replication_header(
        &self,
        sender: Uuid,
        receiver: Uuid,
        size: u32,
    ) -> transport::Channel {
        use tokio::io::AsyncWriteExt;
        let config = &self.configs[&sender];
        let lane = Lane::Replication;
        let tls = config
            .tls
            .peer_protocol(KeeperId(sender.as_u128()), lane.alpn())
            .unwrap();
        let (_, mut socket) =
            transport::connect_protocol(&tls, &config.bulk[&receiver].to_string(), lane.alpn())
                .await
                .unwrap();
        socket.write_u32(size).await.unwrap();
        socket.flush().await.unwrap();
        socket
    }

    async fn group(&self, id: Uuid, stream: StreamId) -> Arc<Group> {
        let server = &self.running[&id].engine;
        timeout(WAIT, async {
            loop {
                if let Some(group) = server.groups.lock().await.get(&stream).cloned() {
                    return group;
                }
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        })
        .await
        .unwrap()
    }

    async fn leader_after_head(&self, journal: &Client, stream: StreamId) -> Uuid {
        assert!(journal.head(stream).await.is_ok());
        self.leader(stream).await
    }

    async fn leader(&self, stream: StreamId) -> Uuid {
        // A completed call to the fresh head path established a leader.
        for server in self.running.values() {
            if let Some(group) = server.engine.groups.lock().await.get(&stream)
                && group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
            {
                return server.engine.id;
            }
        }
        panic!("no leader for {stream:?}")
    }

    async fn authority(&self, stream: StreamId, roster: Voters, revision: u64) -> Uuid {
        timeout(WAIT, async {
            loop {
                for id in roster {
                    let group = self.group(id, stream).await;
                    if matches!(group.proof().await, Reply::Placement(proof)
                        if proof.configuration.revision == revision && proof.joint.is_none())
                    {
                        return id;
                    }
                }
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .unwrap()
    }

    async fn restart(&mut self, id: Uuid) {
        self.restart_with(id, |_| ()).await;
    }

    async fn restart_with(&mut self, id: Uuid, before: impl FnOnce(&Engine)) {
        let config = &self.configs[&id];
        let listeners = [
            super::bind_listener(config.listen).await.unwrap(),
            super::bind_listener(config.peers[&id].bind_addr())
                .await
                .unwrap(),
            super::bind_listener(config.bulk[&id].bind_addr())
                .await
                .unwrap(),
        ];
        self.running.insert(
            id,
            Running::spawn_with(config.clone(), listeners, before).await,
        );
    }

    /// Finalizes the cluster version through the catalog, as an
    /// administrator would once every keeper runs this build, and waits
    /// until every running keeper allows the formats it gates.
    async fn finalize(&self) {
        self.finalize_to(crate::stream::consensus::CLUSTER_VERSION_CURRENT)
            .await;
    }

    /// Finalizes the cluster version at `version`, below this build's when
    /// a test exercises an earlier level.
    async fn finalize_to(&self, version: u32) {
        let client = self.client(&self.credentials);
        timeout(WAIT, async {
            while client.finalize_version(version).await != Ok(version) {
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
            while !self
                .running
                .values()
                .all(|running| running.engine.disk.write_version_allows(version))
            {
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .await
        .expect("the cluster version finalized");
    }

    async fn stop_all(&mut self) {
        for (_, server) in std::mem::take(&mut self.running) {
            server.stop().await;
        }
        crate::stream::consensus::logging::test_warnings::check();
    }
}

fn provision(config: &Config) {
    let provision = storage::Provision {
        keeper: config.keeper,
        data: config
            .data
            .parent()
            .unwrap()
            .canonicalize()
            .unwrap()
            .join(config.data.file_name().unwrap()),
        domain: config.domains[&config.keeper].clone(),
        certificate_sha256: storage::hex(
            &storage::sha256(std::fs::File::open(&config.tls.certificate).unwrap()).unwrap(),
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

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn failover_snapshot_replacement_and_restart_preserve_the_stream() {
    let mut cluster = Cluster::start().await;
    let ids = cluster.ids;
    let catalog = cluster.catalog;
    let journal = cluster.client(&cluster.credentials);
    let other = cluster.client(&cluster.other);
    let stream = StreamId(7);
    let initial = [ids[0], ids[1], ids[2]];
    assert_eq!(journal.head(stream).await, Err(JournalError::NotFound));
    journal
        .create(stream, Voters::from(initial), 4096)
        .await
        .unwrap();
    let starting = journal.configuration(stream).await.unwrap();
    assert_eq!(starting.voters, initial);
    assert_eq!(
        journal
            .create(stream, Voters::from([ids[1], ids[2], ids[3]]), 4096)
            .await,
        Err(JournalError::Conflict { head: Lsn(0) })
    );
    let writer = Uuid::from_u128(99);
    let first = journal.seal(stream, Epoch(0), writer).await.unwrap();
    assert_eq!(first.head, Lsn(0));
    assert_eq!(
        other.seal(stream, Epoch(0), writer).await,
        Err(JournalError::Fenced { current: Epoch(1) })
    );
    for index in 1..=160 {
        assert_eq!(
            journal
                .append(
                    stream,
                    first.fence,
                    Lsn(index),
                    Bytes::from(index.to_string())
                )
                .await,
            Ok(Lsn(index)),
        );
    }
    let leader = cluster.leader(stream).await;
    let [witness, laggard] = initial
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let source = cluster.group(leader, stream).await;
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |metrics| metrics.purged.is_some_and(|id| id.index > 0),
            "source has durably purged its log prefix",
        )
        .await
        .unwrap();
    assert_eq!(
        journal
            .append(stream, first.fence, Lsn(100), Bytes::from_static(b"100"))
            .await,
        Ok(Lsn(100))
    );
    assert_eq!(
        journal
            .append(
                stream,
                first.fence,
                Lsn(100),
                Bytes::from_static(b"different")
            )
            .await,
        Err(JournalError::Conflict { head: Lsn(160) })
    );
    let through = source.state.applied().unwrap().index + 1;
    for id in [witness, laggard] {
        *cluster.running[&id].engine.reject_append.write() =
            Some(Box::new(move |group, sender, request| {
                group == stream
                    && sender == leader.as_u128()
                    && (request
                        .leader_commit
                        .is_some_and(|log| log.index >= through)
                        || (id == laggard
                            && request
                                .entries
                                .iter()
                                .any(|entry| entry.log_id.index >= through)))
            }));
    }
    assert_eq!(
        journal
            .append(stream, first.fence, Lsn(161), Bytes::from_static(b"last"))
            .await,
        Ok(Lsn(161))
    );
    let surviving = cluster.group(witness, stream).await;
    assert!(
        surviving
            .raft
            .metrics()
            .borrow_watched()
            .last_log_index
            .unwrap()
            >= through
    );
    assert!(surviving.state.applied().unwrap().index < through);
    assert!(
        cluster
            .group(laggard, stream)
            .await
            .raft
            .metrics()
            .borrow_watched()
            .last_log_index
            .unwrap_or(0)
            < through
    );
    cluster.running.remove(&leader).unwrap().stop().await;
    for id in [witness, laggard] {
        *cluster.running[&id].engine.reject_append.write() = None;
    }
    let recovered = journal.head(stream).await;
    if recovered != Ok(Lsn(161)) {
        for id in [witness, laggard] {
            let group = cluster.group(id, stream).await;
            eprintln!(
                "{id} {} healthy={}",
                *group.raft.metrics().borrow_watched(),
                group.state.healthy()
            );
        }
    }
    assert_eq!(recovered, Ok(Lsn(161)));
    assert_eq!(
        journal
            .append(stream, first.fence, Lsn(161), Bytes::from_static(b"last"))
            .await,
        Ok(Lsn(161))
    );
    let source = cluster.group(cluster.leader(stream).await, stream).await;
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |metrics| metrics.purged.is_some_and(|id| id.index > 0),
            "replacement source has durably purged its log prefix",
        )
        .await
        .unwrap();
    let second = other
        .seal(stream, Epoch(1), Uuid::from_u128(100))
        .await
        .unwrap();
    assert_eq!(second.head, Lsn(161));
    assert_eq!(
        journal
            .append(stream, first.fence, Lsn(162), Bytes::from_static(b"stale"))
            .await,
        Err(JournalError::Fenced { current: Epoch(2) })
    );
    let next = [
        ids.into_iter()
            .find(|id| *id != leader && initial.contains(id))
            .unwrap(),
        ids.into_iter()
            .filter(|id| *id != leader && initial.contains(id))
            .nth(1)
            .unwrap(),
        catalog,
    ];
    let replaced = journal
        .replace(stream, starting.revision, Voters::from(next))
        .await
        .unwrap();
    assert_eq!(replaced.voters, next);
    assert!(replaced.revision > starting.revision);
    assert_eq!(
        journal
            .replace(stream, starting.revision, Voters::from(next))
            .await,
        Ok(replaced)
    );
    let learner = cluster
        .group(catalog, stream)
        .await
        .state
        .snapshot_path()
        .unwrap();
    assert!(
        learner.is_file(),
        "the replacement should catch up from a snapshot"
    );
    assert!(std::fs::read(&learner).unwrap().starts_with(b"LKRIMG03"));
    other.trim(stream, second.fence, Lsn(160)).await.unwrap();

    cluster.stop_all().await;
    for orphan in ["building-orphan", "incoming-orphan"] {
        std::fs::write(
            learner.parent().unwrap().join(orphan),
            b"interrupted snapshot",
        )
        .unwrap();
    }
    for id in next {
        cluster.restart(id).await;
    }
    let journal = cluster.client(&cluster.credentials);
    assert_eq!(journal.head(stream).await, Ok(Lsn(161)));
    assert_eq!(journal.configuration(stream).await, Ok(replaced));
    let page = journal
        .read(stream, Lsn(161), 1, Duration::from_secs(1))
        .await
        .unwrap();
    assert_eq!(page.records, [(Lsn(161), Bytes::from_static(b"last"))]);
    // A read is one keeper's applied page and may lag until that keeper
    // applies the committed trim after the restart.
    timeout(WAIT, async {
        while journal.read(stream, Lsn(160), 1, Duration::ZERO).await
            != Err(JournalError::Trimmed { floor: Lsn(161) })
        {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .unwrap();

    cluster.restart(leader).await;
    let restored = journal
        .replace(stream, replaced.revision, Voters::from(initial))
        .await
        .unwrap();
    assert_eq!(restored.voters, initial);
    assert!(restored.revision > replaced.revision);
    assert_eq!(
        journal
            .replace(stream, starting.revision, Voters::from(next))
            .await,
        Err(JournalError::Conflict { head: Lsn(161) })
    );
    cluster.running.remove(&catalog).unwrap().stop().await;
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(cold.head(stream).await, Ok(Lsn(161)));
    cold.delete(stream).await.unwrap();
    assert_eq!(cold.head(stream).await, Err(JournalError::Deleted));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn new_leader_finalizes_joint_membership_without_the_caller() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let stream = StreamId(8);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let initial = journal.configuration(stream).await.unwrap();
    let leader = cluster.leader(stream).await;
    let removed = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    let next: [_; 3] = [a, b, c, d]
        .into_iter()
        .filter(|id| *id != removed)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let source = cluster.group(leader, stream).await;
    let learner_ready = Arc::new(AtomicBool::new(false));
    for (id, server) in &cluster.running {
        if *id == leader {
            continue;
        }
        let id = *id;
        let learner_ready = learner_ready.clone();
        *server.engine.reject_append.write() = Some(Box::new(move |group, sender, request| {
            group == stream
                && sender == leader.as_u128()
                && ((id == d && !learner_ready.load(Ordering::Relaxed))
                    || request.entries.iter().any(|entry| {
                        if let EntryPayload::Membership(membership) = &entry.payload {
                            return membership.get_joint_config().as_slice()
                                == [next.into_iter().map(|id| id.as_u128()).collect()];
                        }
                        false
                    }))
        }));
    }
    let replacement = tokio::spawn({
        let journal = journal.clone();
        async move {
            journal
                .replace(stream, initial.revision, Voters::from(next))
                .await
        }
    });
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| {
                source
                    .state
                    .membership()
                    .membership()
                    .get_node(&d.as_u128())
                    .is_some()
            },
            "learner registered in the committed configuration",
        )
        .await
        .unwrap();
    assert_eq!(
        source
            .state
            .membership()
            .membership()
            .get_joint_config()
            .len(),
        1
    );
    let learner = cluster.group(d, stream).await;
    assert_eq!(learner.raft.metrics().borrow_watched().last_log_index, None);
    assert!(learner.state.generation() > 0);
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    assert_eq!(
        journal
            .append(stream, fence, Lsn(1), Bytes::from_static(b"during copy"))
            .await,
        Ok(Lsn(1))
    );
    let issued = source.state.durable_tip().unwrap();
    learner_ready.store(true, Ordering::Relaxed);
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| {
                source
                    .state
                    .membership()
                    .membership()
                    .get_joint_config()
                    .len()
                    == 2
            },
            "joint configuration applied by the old leader",
        )
        .await
        .unwrap();
    let joint_index = source.state.membership().log_id().unwrap().index;
    assert!(
        source
            .raft
            .metrics()
            .borrow_watched()
            .replication
            .as_ref()
            .unwrap()[&d.as_u128()]
            .is_some_and(|matched| matched.index >= issued.index)
    );
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |metrics| {
                metrics
                    .last_log_index
                    .is_some_and(|index| index > joint_index)
            },
            "the old leader alone persisted the final entry",
        )
        .await
        .unwrap();
    assert!(!replacement.is_finished());
    replacement.abort();
    cluster
        .running
        .remove(&cluster.catalog)
        .unwrap()
        .stop()
        .await;
    cluster.running.remove(&leader).unwrap().stop().await;

    let final_configuration = timeout(WAIT, async {
        loop {
            if let Ok(current) = journal.configuration(stream).await
                && current.voters == next
            {
                break current;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await;
    if final_configuration.is_err() {
        for (id, server) in &cluster.running {
            if let Some(group) = server.engine.groups.lock().await.get(&stream) {
                eprintln!(
                    "{id} {} applied {:?}",
                    *group.raft.metrics().borrow_watched(),
                    group.state.membership()
                );
            }
        }
    }
    let final_configuration = final_configuration.unwrap();
    assert_eq!(journal.head(stream).await, Ok(Lsn(1)));
    assert_eq!(
        journal
            .replace(stream, initial.revision, Voters::from(next))
            .await,
        Ok(final_configuration)
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn rejects_untrusted_media_and_duplicate_failure_domains() {
    let mut cluster = Cluster::start_domains(["a", "b", "c", "a"]).await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let bad = StreamId(20);
    assert!(
        journal
            .create(bad, Voters::from([a, a, b]), 4096)
            .await
            .is_err()
    );
    assert!(
        journal
            .create(bad, Voters::from([a, b, d]), 4096)
            .await
            .is_err()
    );
    assert_eq!(journal.head(bad).await, Err(JournalError::NotFound));
    let good = StreamId(21);
    journal
        .create(good, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let configuration = journal.configuration(good).await.unwrap();
    assert_eq!(
        journal
            .replace(good, configuration.revision, Voters::from([a, b, d]))
            .await,
        Err(JournalError::Conflict { head: Lsn(0) })
    );
    assert_eq!(journal.configuration(good).await, Ok(configuration));

    cluster.running.remove(&d).unwrap().stop().await;
    let config = &cluster.configs[&d];
    let media = config.data.join("KEEPER");
    let installed = std::fs::read(&media).unwrap();
    std::fs::write(
        &media,
        std::fs::read(cluster.configs[&a].data.join("KEEPER")).unwrap(),
    )
    .unwrap();
    assert!(
        config
            .clone()
            .prepare(CancellationToken::new())
            .await
            .is_err()
    );
    std::fs::write(&media, installed).unwrap();
    cluster.restart(d).await;
    cluster.running.remove(&d).unwrap().stop().await;
    let config = &cluster.configs[&d];
    let lost = config.data.with_extension("lost");
    std::fs::rename(&config.data, lost).unwrap();
    std::fs::create_dir(&config.data).unwrap();
    assert!(
        config
            .clone()
            .prepare(CancellationToken::new())
            .await
            .is_err()
    );
    assert!(
        config.initialize().is_err(),
        "the registry remembers the used identity"
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn catalog_outage_requires_a_retained_exact_stage_and_cold_clients_use_inventory() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let catalog = cluster.catalog;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(22);
    cluster.running.remove(&catalog).unwrap().stop().await;
    let quick = |cluster: &Cluster| {
        Client::new(
            &cluster.credentials,
            cluster.keepers.clone(),
            catalog,
            Duration::from_millis(600),
        )
        .unwrap()
    };
    assert_eq!(
        quick(&cluster)
            .create(stream, Voters::from([a, b, c]), 4096)
            .await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(
        quick(&cluster).head(stream).await,
        Err(JournalError::Unavailable)
    );
    cluster.restart(catalog).await;
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let current = journal.configuration(stream).await.unwrap();
    let leader = cluster.leader(stream).await;
    let next: [_; 3] = [a, b, c, d]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let stage = super::super::Stage {
        stream,
        source: current.revision,
        old: current.voters,
        target: Voters::from(next),
    };
    let directory = &cluster.running[&catalog].engine;
    // The durable publication survives loss of its response. Until a leader
    // retains it, the existing hints alone cannot authorize joint consensus.
    let _lost = directory
        .catalog()
        .unwrap()
        .stage(stage.clone(), &directory.placement)
        .await
        .unwrap();
    cluster.running.remove(&catalog).unwrap().stop().await;
    assert_eq!(quick(&cluster).head(stream).await, Ok(Lsn(0)));
    assert_eq!(
        quick(&cluster)
            .replace(stream, current.revision, Voters::from(next))
            .await,
        Err(JournalError::Unavailable)
    );
    let source = cluster.group(leader, stream).await;
    assert!(!source.state.staged(&stage));
    cluster.restart(catalog).await;

    *cluster.running[&d].engine.reject_append.write() = Some(Box::new(move |group, sender, _| {
        group == stream && sender == leader.as_u128()
    }));
    let moving = tokio::spawn({
        let journal = journal.clone();
        async move {
            journal
                .replace(stream, current.revision, Voters::from(next))
                .await
        }
    });
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| {
                source.state.staged(&stage)
                    && source
                        .state
                        .membership()
                        .membership()
                        .get_node(&d.as_u128())
                        .is_some()
            },
            "exact receipt and learner are durable",
        )
        .await
        .unwrap();
    moving.abort();
    cluster.running.remove(&catalog).unwrap().stop().await;
    cluster.running.remove(&leader).unwrap().stop().await;
    *cluster.running[&d].engine.reject_append.write() = None;
    let cold = cluster.client(&cluster.credentials);
    assert_eq!(cold.head(stream).await, Ok(Lsn(0)));
    let placed = cold
        .replace(stream, current.revision, Voters::from(next))
        .await
        .unwrap();
    assert_eq!(placed.voters, next);
    assert_eq!(
        cold.replace(stream, current.revision, Voters::from(next))
            .await,
        Ok(placed)
    );
    let directory = &cluster.configs[&catalog];
    let catalog_log = newest_segment(&directory.data);
    std::fs::OpenOptions::new()
        .write(true)
        .open(catalog_log)
        .unwrap()
        .set_len(0)
        .unwrap();
    assert!(
        directory
            .clone()
            .prepare(CancellationToken::new())
            .await
            .is_err()
    );
    assert_eq!(
        cluster.client(&cluster.credentials).head(stream).await,
        Ok(Lsn(0))
    );
    cluster.stop_all().await;
}

fn newest_segment(data: &std::path::Path) -> std::path::PathBuf {
    std::fs::read_dir(data.join("raft-segments"))
        .unwrap()
        .map(|item| item.unwrap().path())
        .max()
        .unwrap()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn damaged_snapshot_is_scoped_and_only_the_selected_bytes_repair_it() {
    use std::io::{Read, Seek, SeekFrom, Write};

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let damaged = StreamId(23);
    let other = StreamId(24);
    for stream in [damaged, other] {
        journal
            .create(stream, Voters::from([a, b, c]), 4096)
            .await
            .unwrap();
    }
    let sealed = journal
        .seal(damaged, Epoch(0), Uuid::new_v4())
        .await
        .unwrap();
    for at in 1..=145 {
        journal
            .append(
                damaged,
                sealed.fence,
                Lsn(at),
                Bytes::from_static(b"snapshot-record"),
            )
            .await
            .unwrap();
    }
    let leader = cluster.leader(damaged).await;
    let victim = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    let group = cluster.group(victim, damaged).await;
    group
        .raft
        .wait(Some(WAIT))
        .metrics(
            |metrics| metrics.snapshot.is_some(),
            "victim selected a durable snapshot",
        )
        .await
        .unwrap();
    let selected = group.state.snapshot_path().unwrap();
    let backup = cluster._dir.path().join("exact-snapshot");
    std::fs::copy(&selected, &backup).unwrap();
    let (payload_file, last_byte) = group.state.payload_path().unwrap();
    let flip = || {
        let mut file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&payload_file)
            .unwrap();
        file.seek(SeekFrom::Start(last_byte)).unwrap();
        let mut byte = [0];
        file.read_exact(&mut byte).unwrap();
        file.seek(SeekFrom::Start(last_byte)).unwrap();
        file.write_all(&[byte[0] ^ 1]).unwrap();
        file.sync_all().unwrap();
    };
    flip();
    let engine = &cluster.running[&victim].engine;
    let identity = Identity::Client(journal_contract::Identity::from(OWNER));
    let read = |stream| Request::Read {
        stream,
        from: Lsn(1),
        limit: 145,
        wait_ms: 0,
    };
    assert!(matches!(
        engine.request(&identity, read(damaged)).await,
        Ok(Reply::Decision(Outcome::Refused(JournalError::Corrupted)))
    ));
    assert!(group.require_healthy().is_err());
    assert!(matches!(
        engine.request(&identity, read(other)).await,
        Ok(Reply::Decision(Outcome::Page(_)))
    ));
    assert_eq!(journal.head(damaged).await, Ok(Lsn(145)));

    cluster.running.remove(&victim).unwrap().stop().await;
    flip();
    std::fs::write(&selected, b"damaged selected root").unwrap();
    cluster.restart(victim).await;
    let victim_engine = &cluster.running[&victim].engine;
    timeout(WAIT, async {
        while !victim_engine.quarantined.read().contains(&damaged) {
            tokio::task::yield_now().await;
        }
    })
    .await
    .unwrap();
    assert!(victim_engine.group(group.genesis.clone()).await.is_err());
    assert!(cluster.group(victim, other).await.require_healthy().is_ok());
    cluster.running.remove(&victim).unwrap().stop().await;

    let wrong = cluster._dir.path().join("wrong-snapshot");
    std::fs::write(&wrong, b"substitute").unwrap();
    assert!(
        cluster.configs[&victim]
            .repair_snapshot(damaged, &wrong)
            .await
            .is_err()
    );
    cluster.configs[&victim]
        .repair_snapshot(damaged, &backup)
        .await
        .unwrap();
    cluster.restart(victim).await;
    assert!(
        cluster
            .group(victim, damaged)
            .await
            .require_healthy()
            .is_ok()
    );
    cluster.running.remove(&victim).unwrap().stop().await;

    let config = &cluster.configs[&victim];
    let wal = newest_segment(&config.data);
    std::fs::OpenOptions::new()
        .write(true)
        .open(wal)
        .unwrap()
        .set_len(0)
        .unwrap();
    assert!(
        config
            .clone()
            .prepare(CancellationToken::new())
            .await
            .is_err()
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn saturated_application_and_bulk_sockets_leave_a_durable_peer_path() {
    use tokio::io::AsyncWriteExt;

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(25);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap();
    let leader = cluster.leader(stream).await;
    let [follower, away]: [_; 2] = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    cluster.running.remove(&away).unwrap().stop().await;
    let destination = &cluster.configs[&follower];
    let app = cluster
        .credentials
        .client_protocol(Lane::Application.alpn())
        .unwrap()
        .0;
    let bulk = cluster.configs[&leader]
        .tls
        .peer_protocol(KeeperId(leader.as_u128()), Lane::Bulk.alpn())
        .unwrap();
    let mut load = Vec::new();
    for (tls, lane, address, count) in [
        (
            &app,
            Lane::Application,
            destination.listen,
            MAX_CLIENT_CONNECTIONS,
        ),
        (
            &bulk,
            Lane::Bulk,
            destination.bulk[&follower].socket_addr().unwrap(),
            MAX_BULK_CONNECTIONS,
        ),
    ] {
        for _ in 0..count {
            let (_, mut channel) =
                transport::connect_protocol(tls, &address.to_string(), lane.alpn())
                    .await
                    .unwrap();
            // Maintain an authenticated request whose body is waiting on I/O.
            channel.write_u32(100).await.unwrap();
            channel.write_all(&[1]).await.unwrap();
            load.push(channel);
        }
    }
    // The follower is the only peer available to confirm the append and head.
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"durable"))
            .await,
        Ok(Lsn(1))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(1)));
    drop(load);
    let at = cluster.group(follower, stream).await;
    at.raft
        .wait(Some(WAIT))
        .metrics(
            |_| at.state.head() == Ok(Lsn(1)),
            "remaining follower applies its durable prefix",
        )
        .await
        .unwrap();
    let reopened = Rpc::new(app, cluster.keepers.clone(), Lane::Application);
    assert!(matches!(
        reopened
            .call::<Reply>(
                follower,
                Frame::Client(Request::Read {
                    stream,
                    from: Lsn(1),
                    limit: 1,
                    wait_ms: 0,
                }),
                Duration::from_secs(1)
            )
            .await,
        Ok(Reply::Decision(Outcome::Page(_)))
    ));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_vote_survives_a_lost_reply_and_rejects_another_candidate_in_its_term() {
    use openraft::{
        Vote,
        raft::{VoteRequest, VoteResponse},
    };

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(26);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let voter = cluster.group(c, stream).await;
    voter
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| voter.state.head() == Ok(Lsn(0)),
            "voter applied genesis",
        )
        .await
        .unwrap();
    for stopped in [a, b] {
        cluster.running.remove(&stopped).unwrap().stop().await;
    }
    let term = voter.raft.metrics().borrow_watched().current_term + 100;
    let last = voter.state.applied();
    let configs = cluster.configs.clone();
    let vote = |id| {
        let client = Rpc::new(
            configs[&id]
                .tls
                .peer_protocol(KeeperId(id.as_u128()), Lane::Control.alpn())
                .unwrap(),
            configs[&id].peers.clone(),
            Lane::Control,
        );
        let genesis = voter.genesis.clone();
        async move {
            client
                .call::<Result<VoteResponse<RaftTypes>, RaftError<RaftTypes>>>(
                    c,
                    Frame::Peer(
                        genesis,
                        PeerRequest::Vote(VoteRequest::new(Vote::new(term, id.as_u128()), last)),
                    ),
                    Duration::from_millis(300),
                )
                .await
        }
    };
    timeout(WAIT, async {
        loop {
            if vote(a)
                .await
                .is_ok_and(|reply| reply.is_ok_and(|reply| reply.vote_granted))
            {
                // The transport delivered a durable vote, but no candidate will
                // use this reply to construct an election.
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .unwrap();
    cluster.running.remove(&c).unwrap().stop().await;
    cluster.restart(c).await;
    let competing = vote(b).await.unwrap().unwrap();
    assert!(!competing.vote_granted);
    assert_eq!(competing.vote, Vote::new(term, a.as_u128()));
    cluster.stop_all().await;
}

fn follower_append(
    source: Uuid,
    previous: LogId,
    term: u64,
    fence: Fence,
) -> AppendEntriesRequest<RaftTypes> {
    let leader = openraft::vote::leader_id_std::CommittedLeaderId::new(term);
    AppendEntriesRequest {
        vote: Vote::new_committed(term, source.as_u128()),
        prev_log_id: Some(previous),
        leader_commit: None,
        entries: vec![
            Entry {
                log_id: LogId::new(leader, previous.index + 1),
                payload: EntryPayload::Blank,
            },
            Entry {
                log_id: LogId::new(leader, previous.index + 2),
                payload: EntryPayload::Normal(Command::Append {
                    fence,
                    owner: OWNER.into(),
                    at: Lsn(2),
                    payload: Bytes::from_static(b"mixed"),
                }),
            },
        ],
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn saturated_follower_body_and_disk_leave_quorum_control_and_covered_purge() {
    use openraft::raft::{VoteRequest, VoteResponse};
    use tokio::io::AsyncReadExt;

    let mut cluster = Cluster::start().await;
    let [a, b, c, busy] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(49);
    let auxiliary = StreamId(50);
    journal
        .create(stream, Voters::from([a, b, c]), 4 * 1024 * 1024)
        .await
        .unwrap();
    journal
        .create(auxiliary, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    let leader = cluster.leader(stream).await;
    let [follower, away]: [_; 2] = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    cluster.running.remove(&away).unwrap().stop().await;
    let group = cluster.group(follower, stream).await;
    group
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| group.state.head() == Ok(Lsn(1)),
            "follower applied the prefix",
        )
        .await
        .unwrap();
    let engine = cluster.running[&follower].engine.clone();
    let disk = &engine.disk;
    let bulk = group.state.occupy_transfers();
    const MIB: u64 = 1024 * 1024;
    disk.space.set_available(152 * MIB);
    let ordinary = disk.space.reserve(64 * MIB - 4 * 64 * 1024).unwrap();
    let previous = group.state.durable_tip().unwrap();
    let term = group.raft.metrics().borrow_watched().current_term + 50;
    let mixed = follower_append(leader, previous, term, fence);
    assert!(
        cluster
            .peer_rpc(leader, Lane::Control)
            .call::<AppendReply>(
                follower,
                Frame::Peer(group.genesis.clone(), PeerRequest::Append(mixed.clone())),
                Duration::from_secs(2)
            )
            .await
            .is_err()
    );
    assert!(matches!(
        cluster
            .peer_rpc(leader, Lane::Replication)
            .call::<AppendReply>(
                follower,
                Frame::Peer(group.genesis.clone(), PeerRequest::Append(mixed)),
                Duration::from_secs(2)
            )
            .await,
        Ok(AppendReply::Busy)
    ));
    assert_eq!(disk.space.outstanding(stream), (0, 0));
    assert_eq!(group.state.durable_tip(), Some(previous));
    assert!(group.raft.metrics().borrow_watched().current_term < term);

    let inbound = &engine.replication_ingress;
    let donors = [busy, cluster.catalog, Uuid::from_u128(6)];
    let header = Lane::Replication.frame_limit() as u32;
    let mut open = Vec::new();
    for donor in donors {
        open.push(cluster.replication_header(donor, follower, header).await);
        timeout(WAIT, async {
            while inbound.frames(Some(donor.as_u128())) != 1 {
                tokio::task::yield_now().await;
            }
        })
        .await
        .unwrap();
    }
    let voter = cluster.group(follower, auxiliary).await;
    let election = Vote::new(
        voter.raft.metrics().borrow_watched().current_term + 50,
        leader.as_u128(),
    );
    let vote = cluster
        .peer_rpc(leader, Lane::Control)
        .call::<Result<VoteResponse<RaftTypes>, RaftError<RaftTypes>>>(
            follower,
            Frame::Peer(
                voter.genesis.clone(),
                PeerRequest::Vote(VoteRequest::new(election, voter.state.durable_tip())),
            ),
            Duration::from_secs(3),
        )
        .await
        .unwrap()
        .unwrap();
    // The live leader's lease may refuse the ballot. A Raft vote decision on
    // the control lane, rather than backpressure or a transport failure, is
    // the service this cut requires while replication data is saturated.
    assert!(
        vote.vote_granted
            || vote.vote.leader_id().term >= voter.raft.metrics().borrow_watched().current_term
    );

    // Frames past a sender's share or the receiver's budget wait unread.
    let mut exceeds_sender = cluster.replication_header(busy, follower, header).await;
    assert!(
        timeout(Duration::from_millis(500), exceeds_sender.read_u8())
            .await
            .is_err()
    );
    let mut exceeds_receiver = cluster
        .replication_header(Uuid::from_u128(7), follower, header)
        .await;
    assert!(
        timeout(Duration::from_millis(500), exceeds_receiver.read_u8())
            .await
            .is_err()
    );
    assert_eq!(inbound.frames(None), 3);
    assert_eq!(inbound.frames(Some(busy.as_u128())), 1);
    assert_eq!(journal.head(stream).await, Ok(Lsn(1)));
    let cut = group.state.applied().unwrap();
    group.raft.trigger().snapshot().await.unwrap();
    group
        .raft
        .wait(Some(WAIT))
        .metrics(
            |m| m.snapshot.is_some_and(|mark| mark.index >= cut.index),
            "covered snapshot commits with data saturated",
        )
        .await
        .unwrap();
    group.raft.trigger().purge_log(cut.index).await.unwrap();
    group
        .raft
        .wait(Some(WAIT))
        .metrics(
            |m| m.purged.is_some_and(|mark| mark.index >= cut.index),
            "covered purge commits with data saturated",
        )
        .await
        .unwrap();

    drop(ordinary);
    drop((exceeds_sender, exceeds_receiver));
    drop(open.pop());
    let missing = donors[2].as_u128();
    timeout(WAIT, async {
        while inbound.frames(Some(missing)) != 0 {
            tokio::task::yield_now().await;
        }
    })
    .await
    .unwrap();
    assert_eq!(
        journal
            .append(stream, fence, Lsn(2), Bytes::from(vec![42; MIB as usize]))
            .await,
        Ok(Lsn(2))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    drop(open);
    drop(bulk);
    disk.space.set_available(u64::MAX);
    cluster.restart(away).await;
    // The copy may close and reopen while it catches up (a vote refused
    // below the protocol floor stops its core), so look it up each time
    // rather than holding one group.
    timeout(WAIT, async {
        while cluster.group(away, stream).await.state.head() != Ok(Lsn(2)) {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("original member catches up after admission pressure");
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancelled_follower_exchange_retains_charges_until_the_exact_durable_settlement() {
    use super::storage::ReplicaFault;
    use openraft::raft::AppendEntriesResponse;

    let mut cluster = Cluster::start().await;
    let [source, receiver, third, _] = cluster.ids;
    let stream = StreamId(51);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([source, receiver, third]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    let target = cluster.group(receiver, stream).await;
    target
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| target.state.head() == Ok(Lsn(1)),
            "recipient applied the prefix",
        )
        .await
        .unwrap();
    for id in [source, third] {
        cluster.running.remove(&id).unwrap().stop().await;
    }
    let engine = cluster.running[&receiver].engine.clone();
    let disk = &engine.disk;
    let previous = target.state.durable_tip().unwrap();
    let term = target.raft.metrics().borrow_watched().current_term + 100;
    let request = follower_append(source, previous, term, fence);
    let cut = request.entries.last().unwrap().log_id;

    let cancelled = target
        .follower
        .admit(disk, stream, request.vote, &request.entries)
        .unwrap();
    assert_eq!(disk.space.outstanding(stream).0, 1);
    drop(cancelled);
    assert_eq!(disk.space.outstanding(stream), (0, 0));

    let (entered, waiting) = oneshot::channel();
    let (resume, blocked) = std::sync::mpsc::channel();
    disk.fail_replication_at(
        stream,
        ReplicaFault::BeforeSettlement {
            entered,
            resume: blocked,
        },
    );
    let rpc = cluster.peer_rpc(source, Lane::Replication);
    let frame = |batch| Frame::Peer(target.genesis.clone(), PeerRequest::Append(batch));
    let send = {
        let rpc = rpc.clone();
        let message = frame(request.clone());
        tokio::spawn(async move { rpc.call::<AppendReply>(receiver, message, WAIT).await })
    };
    timeout(WAIT, waiting).await.unwrap().unwrap();
    let charge = disk.space.outstanding(stream);
    assert_eq!(charge.0, 1);
    assert_eq!(engine.replication_ingress.frames(Some(source.as_u128())), 1);
    send.abort();
    assert!(send.await.unwrap_err().is_cancelled());
    assert_eq!(disk.space.outstanding(stream), charge);
    assert_eq!(target.state.durable_tip(), Some(previous));
    // A racing retry finds the stream's ordered write still unresolved. It
    // gets retryable backpressure and cannot take or release a second charge.
    assert!(matches!(
        rpc.call::<AppendReply>(receiver, frame(request.clone()), WAIT)
            .await,
        Ok(AppendReply::Busy)
    ));
    assert_eq!(disk.space.outstanding(stream), charge);
    timeout(WAIT, async {
        while engine.replication_ingress.frames(Some(source.as_u128())) != 1 {
            tokio::task::yield_now().await;
        }
    })
    .await
    .unwrap();
    assert_eq!(target.state.durable_tip(), Some(previous));
    resume.send(()).unwrap();
    timeout(WAIT, async {
        while disk.space.outstanding(stream).0 != 0 {
            tokio::task::yield_now().await;
        }
    })
    .await
    .unwrap();
    assert_eq!(target.state.durable_tip(), Some(cut));
    // Settlement can finish just before the dispatched task releases the
    // stream's ordered write, so a retry may still see retryable `Busy`.
    let retried = timeout(WAIT, async {
        loop {
            match rpc
                .call::<AppendReply>(receiver, frame(request.clone()), WAIT)
                .await
            {
                Ok(AppendReply::Busy) => tokio::time::sleep(Duration::from_millis(10)).await,
                reply => return reply,
            }
        }
    })
    .await
    .unwrap();
    assert!(matches!(
        retried,
        Ok(AppendReply::Raft(Ok(AppendEntriesResponse::Success)))
    ));
    assert_eq!(target.state.durable_tip(), Some(cut));
    assert_eq!(disk.space.outstanding(stream), (0, 0));
    assert_eq!(target.state.head(), Ok(Lsn(1)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn joint_replication_survives_each_declared_domain_loss() {
    let mut cluster = Cluster::start_domains(["a", "b", "c", "a"]).await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let target = [b, c, d];
    for (iteration, lost) in [vec![a, d], vec![b], vec![c]].into_iter().enumerate() {
        let stream = StreamId(30 + iteration as u128);
        journal
            .create(stream, Voters::from([a, b, c]), 4096)
            .await
            .unwrap();
        let prior = journal.configuration(stream).await.unwrap();
        let leader = cluster.leader(stream).await;
        let hold = Arc::new(AtomicBool::new(true));
        for server in cluster.running.values() {
            let hold = hold.clone();
            *server.engine.reject_append.write() = Some(Box::new(move |group, _, request| {
                group == stream
                    && hold.load(Ordering::Relaxed)
                    && request.entries.iter().any(|entry| {
                        if let EntryPayload::Membership(membership) = &entry.payload {
                            return membership.get_joint_config().as_slice()
                                == [target.into_iter().map(|id| id.as_u128()).collect()];
                        }
                        false
                    })
            }));
        }
        let change = tokio::spawn({
            let journal = journal.clone();
            async move {
                journal
                    .replace(stream, prior.revision, Voters::from(target))
                    .await
            }
        });
        let source = cluster.group(leader, stream).await;
        source
            .raft
            .wait(Some(WAIT))
            .metrics(
                |_| {
                    source
                        .state
                        .membership()
                        .membership()
                        .get_joint_config()
                        .len()
                        == 2
                },
                "joint placement committed before the domain outage",
            )
            .await
            .unwrap();
        for id in &lost {
            cluster.running.remove(id).unwrap().stop().await;
        }
        hold.store(false, Ordering::Relaxed);
        let settled = journal
            .replace(stream, prior.revision, Voters::from(target))
            .await
            .unwrap();
        assert_eq!(settled.voters, target);
        assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
        change.abort();
        for id in lost {
            cluster.restart(id).await;
        }
    }
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn covered_maintenance_reopens_full_suffix_with_all_bulk_sessions_held() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(40);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 16 * 1024)
        .await
        .unwrap();
    for id in [a, b, c] {
        cluster.group(id, stream).await.state.pause_snapshots(true);
    }
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    let leader = cluster.leader(stream).await;
    let source = cluster.group(leader, stream).await;
    let count = MAX_LOG_SUFFIX - source.state.suffix_slots() as u64;
    for at in 1..=count {
        journal
            .append(stream, fence, Lsn(at), Bytes::from_static(b"x"))
            .await
            .unwrap();
    }
    assert_eq!(source.state.suffix_slots(), MAX_LOG_SUFFIX as usize);
    let bulk = source.state.occupy_transfers();
    let vote = source
        .raft
        .with_raft_state(|state| *state.vote_ref())
        .await
        .unwrap();
    let incoming = super::super::network::SnapshotChunk {
        vote,
        meta: super::super::SnapshotMeta {
            last_log_id: source.state.applied(),
            last_membership: Default::default(),
            snapshot_id: "bulk-capacity-cut".into(),
        },
        offset: 0,
        data: b"LKRIMG03".to_vec(),
        done: false,
    };
    assert_eq!(
        source
            .receive_chunk(incoming.clone(), [0; 32])
            .await
            .unwrap_err()
            .kind(),
        io::ErrorKind::StorageFull
    );
    let failed = source
        .write(Command::Trim {
            fence,
            owner: OWNER.into(),
            through: Lsn(1),
        })
        .await;
    assert!(matches!(
        failed,
        Reply::Decision(Outcome::Refused(JournalError::Unavailable))
    ));
    for id in [a, b, c] {
        cluster.group(id, stream).await.state.pause_snapshots(false);
    }
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| source.state.suffix_slots() < MAX_LOG_SUFFIX as usize,
            "a selected covering image purges a full suffix independently of Trim",
        )
        .await
        .unwrap();
    let page = journal
        .read_at_least(stream, Lsn(1), 1, Duration::from_secs(1), Lsn(count))
        .await
        .unwrap();
    assert_eq!((page.floor, page.records[0].0), (Lsn(1), Lsn(1)));
    assert_eq!(
        journal
            .append(stream, fence, Lsn(count + 1), Bytes::from_static(b"y"))
            .await,
        Ok(Lsn(count + 1))
    );
    drop(bulk);
    assert!(
        source
            .receive_chunk(incoming, [0; 32])
            .await
            .unwrap()
            .is_ok()
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn seekable_transfer_pins_its_exact_old_extents_until_close() {
    use tokio::io::{AsyncReadExt, AsyncSeekExt};

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(41);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 32 * 1024)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    for at in 1..=145 {
        journal
            .append(stream, fence, Lsn(at), Bytes::from_static(b"pinned"))
            .await
            .unwrap();
    }
    let source = cluster.group(cluster.leader(stream).await, stream).await;
    source
        .raft
        .wait(Some(WAIT))
        .metrics(|m| m.snapshot.is_some(), "selected index")
        .await
        .unwrap();
    let (extent, _) = source.state.payload_path().unwrap();
    let path = source.state.snapshot_path().unwrap();
    // An unfinalized cluster keeps the root N-1 can open.
    assert!(std::fs::read(path).unwrap().starts_with(b"LKRIDX01"));
    let mut wire = source.raft.get_snapshot().await.unwrap().unwrap().snapshot;
    let end = wire.seek(std::io::SeekFrom::End(0)).await.unwrap();
    let mut first = [0; 8];
    wire.seek(std::io::SeekFrom::Start(0)).await.unwrap();
    wire.read_exact(&mut first).await.unwrap();
    assert_eq!(&first, b"LKRIMG03");
    let offset = end - 32;
    let mut old = [0; 32];
    wire.seek(std::io::SeekFrom::Start(offset)).await.unwrap();
    wire.read_exact(&mut old).await.unwrap();
    journal.trim(stream, fence, Lsn(145)).await.unwrap();
    let through = source.state.applied().unwrap();
    source.raft.trigger().snapshot().await.unwrap();
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |m| m.snapshot.is_some_and(|cut| cut.index >= through.index),
            "new covering index",
        )
        .await
        .unwrap();
    source
        .raft
        .trigger()
        .purge_log(through.index)
        .await
        .unwrap();
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |m| m.purged.is_some_and(|cut| cut.index >= through.index),
            "covered suffix purged while transfer pins old root",
        )
        .await
        .unwrap();
    assert!(extent.exists());
    let mut retried = [0; 32];
    wire.seek(std::io::SeekFrom::Start(offset)).await.unwrap();
    wire.read_exact(&mut retried).await.unwrap();
    assert_eq!(retried, old);
    drop(wire);
    // The extent shares a WAL segment with other frames. Other traffic rolls
    // the segment and checkpoints past it, so only a pin could keep it.
    let filler = StreamId(141);
    journal
        .create(filler, Voters::from([a, b, c]), 64 << 20)
        .await
        .unwrap();
    let filling = journal
        .seal(filler, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    let mut at = 0;
    timeout(WAIT, async {
        while extent.exists() {
            at += 1;
            journal
                .append(filler, filling, Lsn(at), Bytes::from(vec![7; 64 * 1024]))
                .await
                .unwrap();
            journal.trim(filler, filling, Lsn(at)).await.unwrap();
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn retire_then_restart_then_stage_only_reclaims_the_detached_generation() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let stream = StreamId(42);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let initial = journal.configuration(stream).await.unwrap();
    let pinned = cluster.group(a, stream).await;
    let first = journal.replica_generation(stream, a).await.unwrap();
    let path = super::super::ownership::directory(&cluster.configs[&a].data, stream, first);
    let excluded = journal
        .replace(stream, initial.revision, Voters::from([b, c, d]))
        .await
        .unwrap();
    assert_eq!(excluded.revision, initial.revision + 1);
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    let authority = cluster
        .authority(stream, Voters::from([b, c, d]), excluded.revision)
        .await;
    assert!(
        journal
            .retire_copy(stream, a, cluster.catalog, excluded.revision, first)
            .await
            .is_err()
    );
    assert_eq!(journal.replica_generation(stream, a).await, Ok(first));
    journal
        .retire_copy(stream, a, authority, excluded.revision, first)
        .await
        .unwrap();
    assert!(path.exists());
    assert!(journal.replica_generation(stream, a).await.is_err());
    journal
        .retire_copy(stream, a, authority, excluded.revision, first)
        .await
        .unwrap();
    cluster.running.remove(&a).unwrap().stop().await;
    drop(pinned);
    cluster.restart(a).await;

    let joined = journal
        .replace(stream, excluded.revision, Voters::from([a, b, c]))
        .await
        .unwrap();
    let now = journal.replica_generation(stream, a).await.unwrap();
    assert!(now > first);
    assert_eq!(joined.revision, excluded.revision + 1);
    journal
        .retire_copy(stream, a, authority, excluded.revision, first)
        .await
        .unwrap();
    assert_eq!(journal.replica_generation(stream, a).await, Ok(now));
    let current = super::super::ownership::directory(&cluster.configs[&a].data, stream, now);
    timeout(WAIT, async {
        while path.exists() {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    assert!(current.exists());

    let excluded = journal
        .replace(stream, joined.revision, Voters::from([b, c, d]))
        .await
        .unwrap();
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    let authority = cluster
        .authority(stream, Voters::from([b, c, d]), excluded.revision)
        .await;
    journal
        .replace(stream, excluded.revision, Voters::from([a, b, c]))
        .await
        .unwrap();
    let newer = journal.replica_generation(stream, a).await.unwrap();
    assert!(newer > now);
    assert!(
        journal
            .retire_copy(stream, a, authority, excluded.revision, now)
            .await
            .is_err()
    );
    assert_eq!(journal.replica_generation(stream, a).await, Ok(newer));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn preferred_read_hedges_once_and_discovers_a_disjoint_roster() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let target = [d, Uuid::from_u128(6), Uuid::from_u128(7)];
    let stream = StreamId(43);
    let journal = cluster.client(&cluster.credentials);
    let reader = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    let first = reader
        .read_at_least(stream, Lsn(1), 1, Duration::from_secs(1), Lsn(1))
        .await
        .unwrap();
    let leader = cluster.leader(stream).await;
    let before = [a, b, c].map(|id| {
        cluster.running[&id]
            .engine
            .scoped_reads
            .load(Ordering::Relaxed)
    });
    cluster.running[&leader]
        .engine
        .read_delay
        .store(200, Ordering::Relaxed);
    // A short read hedges once to the next voter after 25 ms.
    assert_eq!(
        reader
            .read_at_least(stream, Lsn(1), 1, Duration::ZERO, Lsn(1))
            .await,
        Ok(first.clone())
    );
    let after = [a, b, c].map(|id| {
        cluster.running[&id]
            .engine
            .scoped_reads
            .load(Ordering::Relaxed)
    });
    assert_eq!(
        after
            .iter()
            .zip(before)
            .map(|(after, before)| after - before)
            .sum::<u64>(),
        2
    );
    cluster.running[&leader]
        .engine
        .read_delay
        .store(0, Ordering::Relaxed);

    let initial = journal.configuration(stream).await.unwrap();
    journal
        .replace(stream, initial.revision, Voters::from(target))
        .await
        .unwrap();
    journal
        .append(stream, fence, Lsn(2), Bytes::from_static(b"second"))
        .await
        .unwrap();
    for id in [a, b, c] {
        cluster.running.remove(&id).unwrap().stop().await;
    }
    let second = reader
        .read_at_least(stream, Lsn(1), 2, Duration::from_secs(1), Lsn(2))
        .await
        .unwrap();
    assert_eq!(
        second.records,
        [
            (Lsn(1), Bytes::from_static(b"first")),
            (Lsn(2), Bytes::from_static(b"second"))
        ]
    );
    cluster.stop_all().await;
    assert_eq!(
        reader
            .read_at_least(stream, Lsn(1), 1, Duration::ZERO, Lsn(3))
            .await,
        Err(JournalError::Unavailable)
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_long_poll_waits_on_one_voter_without_hedging() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(44);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    // Learn the placement so the long poll goes to a preferred voter.
    journal
        .read_at_least(stream, Lsn(1), 1, Duration::ZERO, Lsn(1))
        .await
        .unwrap();
    let reads = || {
        [a, b, c]
            .map(|id| {
                cluster.running[&id]
                    .engine
                    .scoped_reads
                    .load(Ordering::Relaxed)
            })
            .iter()
            .sum::<u64>()
    };
    let before = reads();
    let started = Instant::now();
    let page = journal
        .read(stream, Lsn(2), 1, Duration::from_millis(800))
        .await
        .unwrap();
    assert!(page.records.is_empty());
    assert!(started.elapsed() >= Duration::from_millis(700));
    // The long poll waited on one voter and was not hedged after 25 ms.
    assert_eq!(reads() - before, 1);
    // A record appended during the wait ends it on the same single request.
    let before = reads();
    let (page, appended) = tokio::join!(
        journal.read(stream, Lsn(2), 1, Duration::from_secs(3)),
        async {
            tokio::time::sleep(Duration::from_millis(300)).await;
            journal
                .append(stream, fence, Lsn(2), Bytes::from_static(b"second"))
                .await
        }
    );
    appended.unwrap();
    assert_eq!(
        page.unwrap().records,
        [(Lsn(2), Bytes::from_static(b"second"))]
    );
    assert_eq!(reads() - before, 1);
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_quarantined_replica_supplies_no_quorum_evidence() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(62);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    let leader = cluster.leader(stream).await;
    let [quarantined, away]: [_; 2] = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let damaged = cluster.group(quarantined, stream).await;
    damaged
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| damaged.state.head() == Ok(Lsn(1)),
            "replica applied the prefix",
        )
        .await
        .unwrap();
    cluster.running.remove(&away).unwrap().stop().await;
    cluster.running[&quarantined]
        .engine
        .quarantine(stream, &io::Error::other("injected replica damage"));

    // The leader and a reachable but quarantined replica are a numeric
    // majority. The quarantined replica refuses the exchange, so the append
    // stays uncommitted and a fresh head cannot be confirmed.
    let short = Client::new(
        &cluster.credentials,
        cluster.keepers.clone(),
        cluster.catalog,
        Duration::from_secs(2),
    )
    .unwrap();
    let second = Bytes::from_static(b"second");
    assert_eq!(
        short.append(stream, fence, Lsn(2), second.clone()).await,
        Err(JournalError::Unavailable)
    );
    assert_eq!(short.head(stream).await, Err(JournalError::Unavailable));
    let leading = cluster.group(leader, stream).await;
    assert_eq!(leading.state.head(), Ok(Lsn(1)));
    assert_eq!(damaged.state.head(), Ok(Lsn(1)));

    // An eligible voter restores the ordinary quorum and the retried append
    // resolves its unknown outcome.
    cluster.restart(away).await;
    assert_eq!(
        journal.append(stream, fence, Lsn(2), second).await,
        Ok(Lsn(2))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    assert_eq!(damaged.state.head(), Ok(Lsn(1)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn continuous_control_and_a_busy_stream_leave_unrelated_progress_and_target_backoff() {
    const MIB: u64 = 1024 * 1024;
    let mut cluster = Cluster::start().await;
    let [a, b, c, outsider] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let (hot, quiet) = (StreamId(63), StreamId(64));
    let mut fences = Vec::new();
    for stream in [hot, quiet] {
        journal
            .create(stream, Voters::from([a, b, c]), 64 * MIB)
            .await
            .unwrap();
        fences.push(
            journal
                .seal(stream, Epoch(0), Uuid::new_v4())
                .await
                .unwrap()
                .fence,
        );
    }
    let (hot_fence, quiet_fence) = (fences[0], fences[1]);
    journal
        .append(quiet, quiet_fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    let leader = cluster.leader(quiet).await;
    let refusing = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    let lagging = cluster.group(refusing, quiet).await;
    lagging
        .raft
        .wait(Some(WAIT))
        .metrics(
            |_| lagging.state.head() == Ok(Lsn(1)),
            "target applied the prefix",
        )
        .await
        .unwrap();
    journal.head(hot).await.unwrap();
    let hot_leader = cluster.leader(hot).await;
    // The target keeps its protocol floor but cannot admit follower payload.
    let target = cluster.running[&refusing].engine.clone();
    target.disk.space.set_available(88 * MIB + 256 * 1024);

    // Idle authenticated control connections beyond the idle limit.
    let mut idle = Vec::new();
    let config = &cluster.configs[&outsider];
    let tls = config
        .tls
        .peer_protocol(KeeperId(outsider.as_u128()), Lane::Control.alpn())
        .unwrap();
    for receiver in [a, b, c] {
        for _ in 0..70 {
            let (_, socket) = transport::connect_protocol(
                &tls,
                &config.peers[&receiver].to_string(),
                Lane::Control.alpn(),
            )
            .await
            .unwrap();
            idle.push(socket);
        }
    }

    let stop = Arc::new(AtomicBool::new(false));
    let control = {
        let (journal, stop) = (cluster.client(&cluster.credentials), stop.clone());
        tokio::spawn(async move {
            let mut confirmed = 0;
            while !stop.load(Ordering::Relaxed) {
                if journal.head(quiet).await.is_ok() {
                    confirmed += 1;
                }
            }
            confirmed
        })
    };
    let busy = {
        let (journal, stop) = (cluster.client(&cluster.credentials), stop.clone());
        tokio::spawn(async move {
            let mut at = 1;
            while !stop.load(Ordering::Relaxed) {
                let record = Bytes::from(vec![7; 2 * MIB as usize]);
                if journal
                    .append(hot, hot_fence, Lsn(at), record)
                    .await
                    .is_ok()
                {
                    at += 1;
                }
                tokio::task::yield_now().await;
            }
            at - 1
        })
    };

    for at in 2..=11 {
        let record = Bytes::from(vec![at as u8; 64 * 1024]);
        let written = timeout(
            Duration::from_secs(5),
            journal.append(quiet, quiet_fence, Lsn(at), record),
        )
        .await
        .expect("unrelated payload is served under control and stream load");
        assert_eq!(written, Ok(Lsn(at)));
    }
    stop.store(true, Ordering::Relaxed);
    assert!(
        control.await.unwrap() > 0,
        "fresh head was served throughout"
    );
    let hot_written = busy.await.unwrap();
    if hot_leader != refusing {
        assert!(hot_written > 0, "the busy stream kept committing");
    }

    // The refusing target backed off without holding destination charges,
    // and catches up later with unchanged membership.
    assert_eq!(lagging.state.head(), Ok(Lsn(1)));
    assert_eq!(target.disk.space.outstanding(quiet), (0, 0));
    drop(idle);
    target.disk.space.set_available(u64::MAX);
    lagging
        .raft
        .wait(Some(WAIT))
        .metrics(|_| lagging.state.head() == Ok(Lsn(11)), "target catches up")
        .await
        .unwrap();
    assert_eq!(journal.head(quiet).await, Ok(Lsn(11)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_restarted_leader_reads_only_after_committing_in_a_new_term() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(65);
    journal
        .create(stream, Voters::from([a, b, c]), 1024 * 1024)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    for at in 1..=4 {
        journal
            .append(stream, fence, Lsn(at), Bytes::from_static(b"early"))
            .await
            .unwrap();
    }
    let leader = cluster.leader(stream).await;
    let source = cluster.group(leader, stream).await;
    source.raft.trigger().snapshot().await.unwrap();
    source
        .raft
        .wait(Some(WAIT))
        .metrics(|m| m.snapshot.is_some(), "leader snapshot")
        .await
        .unwrap();
    // These acknowledged appends are newer than the leader's snapshot.
    for at in 5..=8 {
        journal
            .append(stream, fence, Lsn(at), Bytes::from_static(b"late"))
            .await
            .unwrap();
    }
    let term = source.raft.metrics().borrow_watched().current_term;
    drop(source);
    cluster.stop_all().await;
    cluster.restart(leader).await;
    let restored = cluster.group(leader, stream).await;
    assert_ne!(
        restored.raft.metrics().borrow_watched().state,
        openraft::ServerState::Leader,
        "a restarted leader must not resume its old term"
    );
    // No voter heard a leader since it restarted, so they certify their
    // copies against the catalog before they campaign.
    let catalog = cluster.catalog;
    for id in [a, b, c, catalog].into_iter().filter(|id| *id != leader) {
        cluster.restart(id).await;
    }
    assert_eq!(journal.head(stream).await, Ok(Lsn(8)));
    let current = cluster.leader(stream).await;
    let elected = cluster.group(current, stream).await;
    assert!(elected.raft.metrics().borrow_watched().current_term > term);
    assert_eq!(
        journal.configuration(stream).await.map(|c| c.revision),
        Ok(0)
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_newcomer_confirms_persisted_progress_without_completing_a_quorum() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let stream = StreamId(66);
    let journal = cluster.client(&cluster.credentials);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let initial = journal.configuration(stream).await.unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap()
        .fence;
    journal
        .append(stream, fence, Lsn(1), Bytes::from_static(b"first"))
        .await
        .unwrap();
    let leader = cluster.leader(stream).await;
    let voters: Vec<_> = [a, b, c].into_iter().filter(|id| *id != leader).collect();
    let next = [leader, voters[0], d];
    // The old voters refuse the joint configuration, so the change cannot
    // commit. The newcomer still receives every entry.
    for (id, server) in &cluster.running {
        if *id == leader || *id == d {
            continue;
        }
        *server.engine.reject_append.write() = Some(Box::new(move |group, sender, request| {
            group == stream
                && sender == leader.as_u128()
                && request.entries.iter().any(|entry| match &entry.payload {
                    EntryPayload::Membership(membership) => membership.get_joint_config().len() > 1,
                    _ => false,
                })
        }));
    }
    let replacement = tokio::spawn({
        let journal = journal.clone();
        async move {
            journal
                .replace(stream, initial.revision, Voters::from(next))
                .await
        }
    });
    let source = cluster.group(leader, stream).await;
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |metrics| {
                metrics
                    .membership_config
                    .membership()
                    .get_joint_config()
                    .len()
                    > 1
                    && metrics
                        .replication
                        .as_ref()
                        .and_then(|progress| progress.get(&d.as_u128()).copied().flatten())
                        .is_some_and(|matched| Some(matched) == source.state.durable_tip())
            },
            "learner matched the leader's joint configuration",
        )
        .await
        .unwrap();
    // The newcomer is outside the committed (old) voter set.
    assert!(!source.state.membership().membership().get_joint_config()[0].contains(&d.as_u128()));
    for id in &voters {
        cluster.running.remove(id).unwrap().stop().await;
    }

    let short = Client::new(
        &cluster.credentials,
        cluster.keepers.clone(),
        cluster.catalog,
        Duration::from_secs(2),
    )
    .unwrap();
    let second = Bytes::from_static(b"second");
    assert_eq!(
        short.append(stream, fence, Lsn(2), second.clone()).await,
        Err(JournalError::Unavailable)
    );
    // The leader proposed the joint configuration while the old voters still
    // answered heartbeats; without them its lease lapses and it refuses the
    // append. The newcomer durably confirms the pending configuration, but
    // without an old voter majority nothing commits.
    let proposed = source.state.durable_tip().unwrap();
    source
        .raft
        .wait(Some(WAIT))
        .metrics(
            |metrics| {
                metrics
                    .replication
                    .as_ref()
                    .and_then(|progress| progress.get(&d.as_u128()).copied().flatten())
                    .is_some_and(|matched| matched >= proposed)
            },
            "newcomer persisted the uncommitted entry",
        )
        .await
        .unwrap();
    assert!(
        source
            .raft
            .metrics()
            .borrow_watched()
            .last_applied
            .is_some_and(|applied| applied < proposed)
    );
    assert_eq!(source.state.head(), Ok(Lsn(1)));
    assert_eq!(short.head(stream).await, Err(JournalError::Unavailable));

    replacement.abort();
    cluster.restart(voters[0]).await;
    *cluster.running[&voters[0]].engine.reject_append.write() = None;
    assert_eq!(
        journal.append(stream, fence, Lsn(2), second).await,
        Ok(Lsn(2))
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    cluster.stop_all().await;
}

/// Characterizes local consensus append throughput. Run explicitly with
/// `cargo test --features stream --release --lib measure_consensus -- --ignored --nocapture`.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
#[ignore = "measurement, run explicitly"]
async fn measure_consensus_append_throughput() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    // `LK_MEASURE_VOTERS=5` measures five-voter streams on 1, 2, 3, 4 and 6.
    let voters = match std::env::var("LK_MEASURE_VOTERS").as_deref() {
        Ok("5") => {
            cluster.finalize().await;
            Voters::from([a, b, c, d, Uuid::from_u128(6)])
        }
        _ => Voters::from([a, b, c]),
    };
    let seconds = std::env::var("LK_MEASURE_SECONDS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(5u64);
    for (case, (streams, in_flight, size)) in [
        // Each stream appends one record at a time. Concurrency comes from
        // independent streams.
        (1, 1, 256),
        (8, 1, 256),
        (32, 1, 256),
        (8, 1, 64 * 1024),
        (32, 1, 4096),
    ]
    .into_iter()
    .enumerate()
    {
        let refused_before = admission::CONTROL_REFUSED.load(Ordering::Relaxed);
        let busy_before: u64 = cluster
            .running
            .values()
            .map(|server| server.engine.busy_replies.load(Ordering::Relaxed))
            .sum();
        let mut prepared = Vec::new();
        for index in 0..streams {
            let stream = StreamId(10_000 + case as u128 * 1_000 + index as u128);
            journal
                .create(stream, voters, 256 * 1024 * 1024)
                .await
                .unwrap();
            let fence = journal
                .seal(stream, Epoch(0), Uuid::new_v4())
                .await
                .unwrap()
                .fence;
            prepared.push((stream, fence));
        }
        let started = std::time::Instant::now();
        let end = tokio::time::Instant::now() + Duration::from_secs(seconds);
        let mut tasks = Vec::new();
        for (stream, fence) in prepared {
            let journal = journal.clone();
            tasks.push(tokio::spawn(async move {
                let record = Bytes::from(vec![9; size]);
                let mut next = 1u64;
                let mut latencies = Vec::new();
                while tokio::time::Instant::now() < end {
                    let started = std::time::Instant::now();
                    let batch = (0..in_flight)
                        .map(|offset| {
                            journal.append(stream, fence, Lsn(next + offset), record.clone())
                        })
                        .collect::<Vec<_>>();
                    for result in futures::future::join_all(batch).await {
                        result.unwrap();
                    }
                    let elapsed = started.elapsed();
                    latencies.extend(std::iter::repeat_n(elapsed, in_flight as usize));
                    next += in_flight;
                }
                latencies
            }));
        }
        let mut latencies = Vec::new();
        for task in tasks {
            latencies.extend(task.await.unwrap());
        }
        let wall = started.elapsed().as_secs_f64();
        latencies.sort();
        let at =
            |q: f64| latencies[((latencies.len() as f64 * q) as usize).min(latencies.len() - 1)];
        let busy: u64 = cluster
            .running
            .values()
            .map(|server| server.engine.busy_replies.load(Ordering::Relaxed))
            .sum::<u64>()
            - busy_before;
        eprintln!(
            "LKMEASURE voters={} streams={streams} in_flight={in_flight} size={size} records={} records/s={:.0} MiB/s={:.2} p50={:?} p99={:?} busy_replies={busy} control_refused={}",
            voters.len(),
            latencies.len(),
            latencies.len() as f64 / wall,
            latencies.len() as f64 * size as f64 / wall / (1024.0 * 1024.0),
            at(0.5),
            at(0.99),
            admission::CONTROL_REFUSED.load(Ordering::Relaxed) - refused_before,
        );
    }
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn deleted_streams_release_their_keeper_slots() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.max_streams = 3;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    let journal = cluster.client(&cluster.credentials);
    // Eight streams in turn on keepers that hold three at a time.
    for stream in (1..=8).map(StreamId) {
        timeout(WAIT, async {
            loop {
                match journal.create(stream, Voters::from([a, b, c]), 4096).await {
                    Ok(()) => return,
                    Err(_) => tokio::time::sleep(Duration::from_millis(50)).await,
                }
            }
        })
        .await
        .unwrap_or_else(|_| panic!("create {stream:?} past the stream limit"));
        journal.delete(stream).await.unwrap();
        assert_eq!(journal.head(stream).await, Err(JournalError::Deleted));
    }
    // Every voter closes the settled group and still answers Deleted.
    timeout(WAIT, async {
        for id in [a, b, c] {
            while cluster.running[&id]
                .engine
                .groups
                .lock()
                .await
                .contains_key(&StreamId(8))
            {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        }
    })
    .await
    .unwrap();
    assert_eq!(journal.head(StreamId(8)).await, Err(JournalError::Deleted));
    let page = journal.read(StreamId(8), Lsn(1), 1, Duration::ZERO).await;
    assert!(matches!(page, Err(JournalError::Deleted)), "{page:?}");
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_gracefully_stopped_leader_hands_its_streams_to_a_voter() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(51);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    let leader = cluster.leader(stream).await;
    let metrics = cluster.running[&leader].engine.disk.metrics.clone();
    cluster.running.remove(&leader).unwrap().stop().await;
    // The stop handed the stream to a voter and waited until it no longer
    // led, before it shut down: checked as a step, not against a clock, so
    // a loaded machine cannot fail it. Without a handoff the leader would
    // still lead when it stopped, and the followers would wait out its
    // lease before an election.
    assert_eq!(metrics.handoffs.load(Ordering::Relaxed), 1);
    let others = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>();
    timeout(WAIT, async {
        loop {
            for id in &others {
                if let Some(group) = cluster.running[id].engine.groups.lock().await.get(&stream)
                    && group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
                {
                    return;
                }
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    })
    .await
    .expect("leadership moved during the graceful stop");
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_leader_replaces_a_voter_whose_keeper_stays_down() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(52);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let initial = journal.configuration(stream).await.unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let down = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    cluster.running.remove(&down).unwrap().stop().await;
    // The test keepers repair after 2 s of silence. No client asks for it.
    let repaired = timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(configuration) = journal.configuration(stream).await
                && configuration.revision > initial.revision
                && !configuration.voters.contains(&down)
            {
                return configuration;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the leader replaced the down voter");
    assert_eq!(
        repaired
            .voters
            .iter()
            .filter(|voter| initial.voters.contains(voter))
            .count(),
        2
    );
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn idle_streams_park_on_every_voter_and_reopen_on_request() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(53);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), uuid::Uuid::from_u128(9))
        .await
        .unwrap();
    journal
        .append(stream, fence.fence, Lsn(1), Bytes::from_static(b"one"))
        .await
        .unwrap();
    // Every voter closes the idle group.
    timeout(Duration::from_secs(20), async {
        loop {
            let mut open = 0;
            for id in [a, b, c] {
                open += usize::from(
                    cluster.running[&id]
                        .engine
                        .groups
                        .lock()
                        .await
                        .contains_key(&stream),
                );
            }
            if open == 0 {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("every voter parked the idle stream");
    // A request reopens it: the stream elects a leader and keeps its log.
    assert_eq!(journal.head(stream).await, Ok(Lsn(1)));
    journal
        .append(stream, fence.fence, Lsn(2), Bytes::from_static(b"two"))
        .await
        .unwrap();
    let page = journal
        .read(stream, Lsn(1), 2, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 2);
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_replaced_voter_retires_its_copy_when_it_returns() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(54);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let initial = journal.configuration(stream).await.unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let down = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    let generation = journal.replica_generation(stream, down).await.unwrap();
    cluster.running.remove(&down).unwrap().stop().await;
    timeout(Duration::from_secs(30), async {
        loop {
            if let Ok(configuration) = journal.configuration(stream).await
                && configuration.revision > initial.revision
                && !configuration.voters.contains(&down)
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the leader replaced the down voter");
    cluster.restart(down).await;
    // The returning keeper finds no leader, learns it was removed, and
    // retires its copy.
    timeout(Duration::from_secs(30), async {
        while journal.replica_generation(stream, down).await == Ok(generation) {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the returning keeper retired its removed copy");
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.stop_all().await;
}

async fn wait_for_leader(cluster: &Cluster, stream: StreamId, expected: Uuid) -> bool {
    timeout(Duration::from_secs(10), async {
        loop {
            if let Some(group) = cluster.running[&expected]
                .engine
                .groups
                .lock()
                .await
                .get(&stream)
                && group.raft.metrics().borrow_watched().state == openraft::ServerState::Leader
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .is_ok()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_writer_moves_leadership_to_its_domain_once_a_minute() {
    let cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(55);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let target = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    journal.prefer_leader(stream, target).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, target).await);
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    // A second preference within the hold-down leaves the leader in place.
    journal.prefer_leader(stream, leader).await.unwrap();
    tokio::time::sleep(Duration::from_secs(2)).await;
    assert_eq!(cluster.leader(stream).await, target);
    let mut cluster = cluster;
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_leader_without_space_hands_its_streams_to_a_follower() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(56);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    cluster.running[&leader].engine.disk.space.set_available(0);
    let others = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>();
    let mut moved = false;
    for target in others {
        moved |= wait_for_leader(&cluster, stream, target).await;
        if moved {
            break;
        }
    }
    assert!(moved, "the full leader handed its stream away");
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    cluster.running[&leader]
        .engine
        .disk
        .space
        .set_available(u64::MAX);
    cluster.stop_all().await;
}

/// A leader replicates its append before its own WAL write is durable. Its
/// followers' two durable copies commit it, and a leader that crashes
/// before its sync returned loses nothing that was committed.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_leader_that_crashes_before_its_own_sync_keeps_the_replicated_commit() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(58);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let sealed = journal
        .seal(stream, Epoch(0), Uuid::new_v4())
        .await
        .unwrap();
    assert_eq!(
        journal
            .append(stream, sealed.fence, Lsn(1), Bytes::from_static(b"one"))
            .await,
        Ok(Lsn(1))
    );
    let leader = cluster.leader(stream).await;
    let followers = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>();
    let led = cluster.group(leader, stream).await;
    let term = led.raft.metrics().borrow_watched().current_term;
    let (entered, inside) = tokio::sync::oneshot::channel();
    let (resume, held) = std::sync::mpsc::channel();
    cluster.running[&leader].engine.disk.fail_replication_at(
        stream,
        storage::ReplicaFault::Hold {
            entered,
            resume: held,
        },
    );
    let appending = journal.clone();
    let append = tokio::spawn(async move {
        appending
            .append(stream, sealed.fence, Lsn(2), Bytes::from_static(b"two"))
            .await
    });
    timeout(WAIT, inside).await.unwrap().unwrap();
    // With the leader's write held, both followers apply the entry: their
    // two durable copies committed it. A synchronous leader append would
    // hold replication until the slow-media gate moved leadership away.
    for follower in &followers {
        let group = cluster.group(*follower, stream).await;
        timeout(Duration::from_secs(2), async {
            while group.state.head() != Ok(Lsn(2)) {
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        })
        .await
        .expect("a follower applied the entry while the leader's write was held");
    }
    // The same leader committed it, and applies only what its own WAL holds.
    let metrics = led.raft.metrics().borrow_watched().clone();
    assert_eq!(
        (metrics.state, metrics.current_term),
        (openraft::ServerState::Leader, term)
    );
    assert_eq!(led.state.head(), Ok(Lsn(1)));
    assert!(!append.is_finished());
    // The keeper dies before its sync returned.
    resume.send(false).unwrap();
    let crashed = cluster.running.remove(&leader).unwrap();
    timeout(WAIT, async {
        while crashed.engine.disk.healthy() {
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    })
    .await
    .unwrap();
    crashed.engine.stop.cancel();
    let _ = crashed.task.await;
    drop((led, crashed.engine));
    // The writer's retry finds the committed entry under the new leader.
    assert!(matches!(append.await.unwrap(), Ok(Lsn(2)) | Err(_)));
    assert_eq!(journal.head(stream).await, Ok(Lsn(2)));
    cluster.restart(leader).await;
    let returned = cluster.group(leader, stream).await;
    timeout(WAIT, async {
        while returned.state.head() != Ok(Lsn(2)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("the restarted keeper caught up past its lost write");
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_leader_with_slow_media_hands_off_refuses_hand_offs_and_accepts_nothing() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(57);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let slow = cluster.running[&leader].engine.clone();
    assert!(slow.keeper_status().await.accepting);
    slow.disk.mark_slow(Duration::from_secs(60));
    assert!(!slow.disk.responsive());
    assert!(slow.disk.healthy(), "slow media stays in service");
    assert!(!slow.keeper_status().await.accepting);
    let others = [a, b, c]
        .into_iter()
        .filter(|id| *id != leader)
        .collect::<Vec<_>>();
    let mut moved = false;
    for target in &others {
        moved |= wait_for_leader(&cluster, stream, *target).await;
        if moved {
            break;
        }
    }
    assert!(moved, "the slow leader handed its stream away");
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    // The slow keeper refuses to take the stream back by hand-off.
    let group = cluster.group(leader, stream).await;
    let current = group.raft.metrics().borrow_watched().clone();
    let from = current.current_leader.unwrap();
    let refused = slow
        .peer(
            from,
            group.genesis.clone(),
            PeerRequest::TransferLeader(openraft::raft::TransferLeaderRequest::new(
                current.vote,
                leader.as_u128(),
                current.last_log_index.and(group.state.applied()),
            )),
            None,
        )
        .await
        .unwrap_err();
    assert!(refused.to_string().contains("slow"), "{refused}");
    cluster.stop_all().await;
}

/// A leader whose own vote regressed (its campaign at a higher term reached
/// a peer, but its save never landed) and that then won a lower term steps
/// down when that peer answers with the higher vote, and campaigns above
/// it. OpenRaft alone kept leading under the lower vote, tripping its
/// "leader.vote >= state.vote" debug assertion and stopping the core.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_leader_steps_down_when_a_peer_holds_its_own_newer_vote() {
    use openraft::raft::VoteRequest;

    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(59);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let follower = [a, b, c].into_iter().find(|id| *id != leader).unwrap();
    let led = cluster.group(leader, stream).await;
    let term = led.raft.metrics().borrow_watched().current_term;
    // The follower now holds the leader's vote at a term the leader never
    // persisted, as after the leader's failed vote save.
    let lost = term + 50;
    let copy = cluster.group(follower, stream).await;
    cluster.running[&follower]
        .engine
        .peer(
            leader.as_u128(),
            copy.genesis.clone(),
            PeerRequest::Vote(VoteRequest::new(
                openraft::Vote::new(lost, leader.as_u128()),
                copy.raft
                    .metrics()
                    .borrow_watched()
                    .last_log_index
                    .and(copy.state.applied()),
            )),
            None,
        )
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(9))
        .await
        .unwrap()
        .fence;
    timeout(WAIT, async {
        loop {
            if journal
                .append(stream, fence, Lsn(1), Bytes::from_static(b"one"))
                .await
                == Ok(Lsn(1))
                && cluster
                    .group(cluster.leader(stream).await, stream)
                    .await
                    .raft
                    .metrics()
                    .borrow_watched()
                    .current_term
                    > lost
            {
                return;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("the stream is led above the regressed vote");
    assert!(
        led.raft.metrics().borrow_watched().running_state.is_ok(),
        "the former leader's core kept running"
    );
    cluster.stop_all().await;
}

/// Slow keepers still vote. When the media of two of three voters stall
/// together and the third, responsive, leader stops, the two slow voters
/// still elect one of themselves; if they refused each other's votes, the
/// stream would have no leader until their slow hold ended.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn voters_with_slow_media_still_elect_a_leader() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(58);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    journal.prefer_leader(stream, c).await.unwrap();
    assert!(wait_for_leader(&cluster, stream, c).await);
    for id in [a, b] {
        cluster.running[&id]
            .engine
            .disk
            .mark_slow(Duration::from_secs(600));
    }
    cluster.running.remove(&c).unwrap().stop().await;
    assert_eq!(journal.head(stream).await, Ok(Lsn(0)));
    let mut led = false;
    for id in [a, b] {
        led |= cluster
            .group(id, stream)
            .await
            .raft
            .metrics()
            .borrow_watched()
            .state
            == openraft::ServerState::Leader;
    }
    assert!(led, "a slow voter leads while no responsive voter is left");
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_leader_removes_a_learner_left_by_an_aborted_replacement() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, d] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let stream = StreamId(57);
    journal
        .create(stream, Voters::from([a, b, c]), 4096)
        .await
        .unwrap();
    let leader = cluster.leader_after_head(&journal, stream).await;
    let group = cluster.group(leader, stream).await;
    let node = group
        .raft
        .metrics()
        .borrow_watched()
        .membership_config
        .membership()
        .get_node(&a.as_u128())
        .unwrap()
        .clone();
    group
        .raft
        .add_learner(d.as_u128(), node, false)
        .await
        .unwrap();
    timeout(Duration::from_secs(20), async {
        while group
            .raft
            .metrics()
            .borrow_watched()
            .membership_config
            .membership()
            .get_node(&d.as_u128())
            .is_some()
        {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the stale learner was removed");
    assert_eq!(
        journal.configuration(stream).await.unwrap().voters,
        [a, b, c]
    );
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_parked_stream_keeps_its_snapshot_and_retained_extents() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    cluster.stop_all().await;
    for config in cluster.configs.values_mut() {
        config.park_after_secs = 2;
    }
    for id in cluster.configs.keys().copied().collect::<Vec<_>>() {
        cluster.restart(id).await;
    }
    let journal = cluster.client(&cluster.credentials);
    let record = |at: u64| Bytes::from(vec![(at % 251) as u8; 2048]);
    let (parked, busy) = (StreamId(58), StreamId(59));
    let mut fences = Vec::new();
    for stream in [parked, busy] {
        journal
            .create(stream, Voters::from([a, b, c]), 1 << 30)
            .await
            .unwrap();
        let sealed = journal
            .seal(stream, Epoch(0), uuid::Uuid::from_u128(9))
            .await
            .unwrap();
        fences.push(sealed.fence);
    }
    // More than one snapshot interval of entries, so the parked stream's
    // early records live only in its snapshot and applied state.
    for at in 1..=200 {
        journal
            .append(parked, fences[0], Lsn(at), record(at))
            .await
            .unwrap();
    }
    let mut images = Vec::new();
    for id in [a, b, c] {
        images.push(cluster.group(id, parked).await.state.downgrade());
    }
    // The busy stream keeps writing, rolling and checkpointing segments,
    // while the other one parks and the reaper runs.
    let deadline = tokio::time::Instant::now() + Duration::from_secs(8);
    let mut at = 1;
    while tokio::time::Instant::now() < deadline {
        journal
            .append(busy, fences[1], Lsn(at), record(at))
            .await
            .unwrap();
        at += 1;
    }
    for id in [a, b, c] {
        assert!(
            !cluster.running[&id]
                .engine
                .groups
                .lock()
                .await
                .contains_key(&parked),
            "the idle stream parked"
        );
        let engine = &cluster.running[&id].engine;
        let pinned = engine
            .closed_states
            .lock()
            .get(&parked)
            .map(|closed| match closed {
                super::Closed::Pinned(pin) => pin.segments().count(),
                super::Closed::Closing(_) => 0,
            });
        assert!(
            pinned.is_some_and(|segments| segments > 0),
            "the parked copy keeps only pins of its segments"
        );
    }
    // No voter keeps the parked stream's applied image or snapshot copy.
    timeout(WAIT, async {
        while images.iter().any(|image| image.strong_count() != 0) {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await
    .expect("parking dropped every voter's state machine");
    let page = timeout(WAIT, async {
        loop {
            match journal.read(parked, Lsn(1), 1, Duration::ZERO).await {
                Ok(page) => return page,
                Err(_) => tokio::time::sleep(Duration::from_millis(50)).await,
            }
        }
    })
    .await
    .unwrap();
    assert_eq!(page.records, [(Lsn(1), record(1))]);
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn heartbeats_for_many_streams_share_one_frame_and_keep_the_parked_and_deleted_rules() {
    let mut cluster = Cluster::start().await;
    let [a, b, c, _] = cluster.ids;
    let journal = cluster.client(&cluster.credentials);
    let streams = (90..106).map(StreamId).collect::<Vec<_>>();
    let mut genesis = Vec::new();
    for stream in &streams {
        journal
            .create(*stream, Voters::from([a, b, c]), 4096)
            .await
            .unwrap();
        genesis.push(cluster.group(a, *stream).await.genesis.clone());
    }
    let engine = cluster.running[&a].engine.clone();
    let (parked, deleted) = (&streams[..4], streams[4]);
    engine
        .parked
        .write()
        .extend(parked.iter().map(|stream| (*stream, Some(Instant::now()))));
    engine.deleted.write().insert(deleted);
    // A stale heartbeat from `b` reaches Raft, which refuses its old vote.
    let vote = Vote::new_committed(0, b.as_u128());
    let heartbeat = |genesis: Genesis| {
        Frame::Peer(
            genesis,
            PeerRequest::Append(AppendEntriesRequest {
                vote,
                prev_log_id: None,
                leader_commit: None,
                entries: Vec::new(),
            }),
        )
    };
    let rpc = cluster.peer_rpc(b, Lane::Control);
    let (beats, park) = tokio::join!(
        futures::future::join_all(genesis.iter().map(|genesis| rpc.call::<AppendReply>(
            a,
            heartbeat(genesis.clone()),
            WAIT
        )),),
        rpc.call::<bool>(
            a,
            Frame::Peer(genesis[0].clone(), PeerRequest::Park { vote, last: None }),
            WAIT,
        ),
    );
    // Every message was queued while the connection opened.
    assert_eq!(rpc.frames(), 1);
    for (stream, beat) in streams.iter().zip(beats) {
        match beat {
            Ok(AppendReply::Busy) => assert!(parked.contains(stream)),
            Ok(AppendReply::Raft(_)) => assert!(!parked.contains(stream) && *stream != deleted),
            Err(_) => assert_eq!(*stream, deleted),
        }
    }
    // A repeated park of a parked stream is accepted without opening it.
    assert!(park.unwrap());
    assert!(engine.parked.read().contains_key(&streams[0]));
    engine.deleted.write().remove(&deleted);
    engine.parked.write().clear();
    // The connection survived the deleted stream's refusal.
    assert!(matches!(
        rpc.call::<AppendReply>(a, heartbeat(genesis[5].clone()), WAIT)
            .await,
        Ok(AppendReply::Raft(_))
    ));
    assert_eq!(rpc.frames(), 2);
    cluster.stop_all().await;
}
