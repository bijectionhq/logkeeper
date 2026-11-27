//! Real keepers on loopback for consumer tests. Enable the
//! `consensus-testing` feature.
//!
//! [`LocalCluster`] starts three voter keepers in distinct failure domains
//! and a catalog keeper, each with its own enrolled media, TLS identity and
//! data directory. Consumers open [`ConsensusJournal`] handles for named
//! client principals and can stop and restart individual keepers.
//! [`LocalCluster::start_replicated_catalog`] instead hosts the catalog as a
//! consensus stream on two voters and the catalog keeper.
//! [`LocalCluster::start_spared`] adds two spare keepers in the second and
//! third voters' domains, so that a stream that lost two voters can be
//! recovered with [`LocalCluster::recover_stream`].
//!
//! Its keepers flush with plain `fsync` unless the process installed a
//! [`SyncMode`] before starting the cluster, so tests stay fast on macOS.

use std::{
    collections::BTreeMap,
    io,
    net::{SocketAddr, TcpListener as StdListener},
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
    time::Duration,
};

use rcgen::{
    BasicConstraints, CertificateParams, DnType, ExtendedKeyUsagePurpose, IsCa, Issuer, KeyPair,
    SanType,
};
use tokio::{net::TcpListener, task::JoinHandle};
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

use ring::signature::{Ed25519KeyPair, KeyPair as _};
use std::sync::atomic::{AtomicI64, Ordering};

use crate::stream::{
    timed::{TimedOriginal, TimedOriginalClock, TimedOriginalVerifier},
    wire::KeeperId,
};

use super::{
    AdminConfig, Config, ConsensusJournal, Credentials, Domains, JournalConfig, Keepers, Recovery,
    RecoveryReport, SyncMode, TimedAuthority,
    storage::{Authority, Provision, hex, sha256},
};
use crate::stream::consensus::Voters;

struct Running {
    stop: CancellationToken,
    task: JoinHandle<io::Result<()>>,
}

/// Three voters and a catalog keeper serving on loopback, and optionally
/// two spare keepers.
pub struct LocalCluster {
    verifier: Arc<dyn TimedOriginalVerifier>,
    offset: Arc<AtomicI64>,
    dir: tempfile::TempDir,
    issuer: Issuer<'static, KeyPair>,
    roots: PathBuf,
    configs: BTreeMap<Uuid, Config>,
    running: BTreeMap<Uuid, Running>,
    keepers: Keepers,
    voters: Voters,
    spares: Vec<Uuid>,
    catalog: Uuid,
    catalog_voters: Option<Voters>,
    issued: Mutex<BTreeMap<String, Credentials>>,
}

impl LocalCluster {
    /// Starts the keepers. Every listed principal may read, write and
    /// administer streams.
    pub async fn start(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, false, 600, false, false).await
    }

    /// Starts the keepers with a replicated catalog on voters 1 and 2 and
    /// the catalog keeper, which seeds it.
    pub async fn start_replicated_catalog(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, false, 600, true, false).await
    }

    /// Starts the keepers so that a stream idle for `park_after_secs` is
    /// parked on every voter.
    pub async fn start_parking(principals: &[&str], park_after_secs: u64) -> io::Result<Self> {
        Self::start_with(principals, false, park_after_secs, false, false).await
    }

    /// Starts the keepers with timed-original authority: each keeper signs
    /// with its own Ed25519 key and samples a wall clock shifted by
    /// [`LocalCluster::shift_timed_clock`].
    pub async fn start_timed(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, true, 600, false, false).await
    }

    /// Starts the keepers and two spares: keepers 5 and 6, in the domains of
    /// voters 2 and 3. Five keepers in three domains, plus the catalog
    /// keeper, are enough to recover a stream that lost voters 2 and 3 onto
    /// voter 1 and the spares.
    pub async fn start_spared(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, false, 600, false, true).await
    }

    /// Starts the keepers of [`LocalCluster::start_spared`] with streams on
    /// five voters: keepers 1, 2, 3, 5 and 6, two each in zones b and c and
    /// one in zone a, the spread placement allows over three domains. The
    /// cluster version is finalized, which five-voter streams need.
    pub async fn start_five_voters(principals: &[&str]) -> io::Result<Self> {
        let mut cluster = Self::start_with(principals, false, 600, false, true).await?;
        let mut five = cluster.voters.to_vec();
        five.append(&mut cluster.spares);
        cluster.voters = Voters::sorted(&five).expect("five voters");
        cluster
            .finalize_version(principals[0], super::CLUSTER_VERSION_CURRENT)
            .await?;
        Ok(cluster)
    }

    async fn start_with(
        principals: &[&str],
        timed: bool,
        park_after_secs: u64,
        replicated: bool,
        spared: bool,
    ) -> io::Result<Self> {
        let dir = tempfile::tempdir()?;
        let roots = dir.path().join("ca.pem");
        let issuer = authority(&roots)?;
        let voters = [1, 2, 3].map(Uuid::from_u128);
        let catalog = Uuid::from_u128(4);
        let catalog_voters = replicated.then_some(Voters::from([voters[0], voters[1], catalog]));
        let spares = if spared {
            vec![Uuid::from_u128(5), Uuid::from_u128(6)]
        } else {
            Vec::new()
        };
        let roster = voters
            .into_iter()
            .chain([catalog])
            .chain(spares.iter().copied())
            .collect::<Vec<_>>();
        let domains: Domains = roster
            .iter()
            .zip([
                "zone-a",
                "zone-b",
                "zone-c",
                "directory",
                "zone-b",
                "zone-c",
            ])
            .map(|(id, domain)| (*id, domain.into()))
            .collect();
        let enrollment = dir.path().join("registry");
        std::fs::create_dir(&enrollment)?;
        std::fs::write(
            enrollment.join("placement.json"),
            serde_json::to_vec(&Authority {
                catalog,
                domains: domains.clone(),
                retired: Default::default(),
            })?,
        )?;
        let [mut keepers, mut peers, mut bulk] = [(); 3].map(|_| Keepers::new());
        for id in &roster {
            keepers.insert(*id, free_port()?.into());
            peers.insert(*id, free_port()?.into());
            bulk.insert(*id, free_port()?.into());
        }
        let principals = principals
            .iter()
            .map(|uri| uri.to_string())
            .collect::<Vec<_>>();
        let offset = Arc::new(AtomicI64::new(0));
        let keys = if timed {
            roster
                .iter()
                .map(|id| {
                    let random = ring::rand::SystemRandom::new();
                    let pkcs8 = Ed25519KeyPair::generate_pkcs8(&random)
                        .map_err(|_| io::Error::other("keeper key generation failed"))?;
                    let key = Ed25519KeyPair::from_pkcs8(pkcs8.as_ref())
                        .map_err(|_| io::Error::other("keeper key rejected"))?;
                    Ok((*id, Arc::new(key)))
                })
                .collect::<io::Result<BTreeMap<_, _>>>()?
        } else {
            BTreeMap::new()
        };
        let verifier: Arc<dyn TimedOriginalVerifier> = Arc::new(LocalVerifier(
            keys.iter()
                .map(|(id, key)| {
                    let public: [u8; 32] = key.public_key().as_ref().try_into().unwrap();
                    (id.as_u128(), public)
                })
                .collect(),
        ));
        let mut cluster = Self {
            verifier: verifier.clone(),
            offset: offset.clone(),
            issuer,
            roots,
            configs: BTreeMap::new(),
            running: BTreeMap::new(),
            keepers: keepers.clone(),
            voters: Voters::from(voters),
            spares,
            catalog,
            catalog_voters,
            issued: Mutex::default(),
            dir,
        };
        for id in roster {
            let tls = cluster.issue(
                &id.to_string(),
                &format!("urn:logkeeper:keeper:{id}"),
                vec![
                    ExtendedKeyUsagePurpose::ClientAuth,
                    ExtendedKeyUsagePurpose::ServerAuth,
                ],
            )?;
            let config = Config {
                keeper: id,
                listen: keepers[&id].socket_addr().unwrap(),
                data: cluster.dir.path().join(format!("data-{id}")),
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
                // Short, so a recovery's wait for lost leases stays short.
                lease_millis: 4_000,
                lease_drift_margin_millis: 400,
                readers: principals.clone(),
                writers: principals.clone(),
                administrators: principals.clone(),
                max_streams: 128,
                repair_after_secs: 600,
                park_after_secs,
                snapshot_send_bytes_per_second: 0,
                scrub_bytes_per_second: 0,
                // `LOGKEEPER_ASYNC_APPEND=0` measures the synchronous leader append.
                async_append: std::env::var("LOGKEEPER_ASYNC_APPEND")
                    .map_or(true, |value| value != "0"),
                timed_original: None,
                // Test keepers use plain `fsync` unless the process chose a
                // mode: a full flush costs milliseconds on macOS, and many
                // tests share one drive.
                sync_mode: SyncMode::installed().unwrap_or(SyncMode::Fsync),
                timed_authority: keys.get(&id).map(|key| TimedAuthority {
                    verifier: verifier.clone(),
                    clock: Some(Arc::new(LocalClock {
                        key: key.clone(),
                        offset: offset.clone(),
                    }) as Arc<dyn TimedOriginalClock>),
                }),
                log_format: Default::default(),
                // Every local keeper serves the plain loopback admin
                // listener, so tests can follow the operator's probes.
                admin: Some(AdminConfig {
                    listen: free_port()?,
                    mtls: false,
                    cluster: Default::default(),
                    metrics_readers: Vec::new(),
                    probe_listen: None,
                }),
                offload: None,
            };
            provision(&config)?;
            config.initialize()?;
            cluster.configs.insert(id, config);
            cluster.restart(id).await?;
        }
        Ok(cluster)
    }

    /// The installed keeper trust of a timed cluster.
    pub fn timed_verifier(&self) -> Arc<dyn TimedOriginalVerifier> {
        self.verifier.clone()
    }

    /// Shifts every keeper's timed clock, for example past a cutoff.
    pub fn shift_timed_clock(&self, micros: i64) {
        self.offset.store(micros, Ordering::SeqCst);
    }

    pub fn voters(&self) -> Voters {
        self.voters
    }

    /// The spare keepers of a cluster started with
    /// [`LocalCluster::start_spared`]; empty otherwise.
    pub fn spares(&self) -> &[Uuid] {
        &self.spares
    }

    pub fn catalog(&self) -> Uuid {
        self.catalog
    }

    /// The replicated catalog's voters, when the cluster runs one.
    pub fn catalog_voters(&self) -> Option<Voters> {
        self.catalog_voters
    }

    pub fn keepers(&self) -> &Keepers {
        &self.keepers
    }

    /// The plain HTTP admin listener of `keeper`, on loopback.
    pub fn admin(&self, keeper: Uuid) -> SocketAddr {
        self.configs[&keeper]
            .admin
            .as_ref()
            .expect("local keepers serve an admin listener")
            .listen
    }

    /// The directory holding every keeper's data, registry and credentials.
    pub fn directory(&self) -> &Path {
        self.dir.path()
    }

    /// The contract configuration for streams placed on the three voters.
    pub fn journal_config(&self, quota_bytes: u64, max_record_bytes: usize) -> JournalConfig {
        JournalConfig {
            keepers: self.keepers.clone(),
            catalog: self.catalog,
            catalog_voters: self.catalog_voters,
            voters: Some(self.voters),
            replication_factor: self.voters.len(),
            placement: None,
            draining: Default::default(),
            retired: Default::default(),
            quota_bytes,
            max_record_bytes,
            deadline_ms: 10_000,
            domain: None,
        }
    }

    /// A contract configuration that places each stream on three of the
    /// keepers, each in its own failure domain.
    pub fn placement_config(&self, quota_bytes: u64, max_record_bytes: usize) -> JournalConfig {
        let domains = self
            .configs
            .values()
            .map(|config| (config.keeper, config.domains[&config.keeper].clone()))
            .collect();
        JournalConfig {
            voters: None,
            placement: Some(domains),
            ..self.journal_config(quota_bytes, max_record_bytes)
        }
    }

    /// Client credentials for `principal`, issued once per principal.
    pub fn credentials(&self, principal: &str) -> io::Result<Credentials> {
        if let Some(issued) = self.issued.lock().unwrap().get(principal) {
            return Ok(issued.clone());
        }
        let name = format!("client-{}", hex(&sha256(principal.as_bytes())?[..8]));
        let issued = self.issue(&name, principal, vec![ExtendedKeyUsagePurpose::ClientAuth])?;
        self.issued
            .lock()
            .unwrap()
            .insert(principal.to_owned(), issued.clone());
        Ok(issued)
    }

    /// A contract journal acting as `principal`.
    pub fn journal(&self, principal: &str, config: &JournalConfig) -> io::Result<ConsensusJournal> {
        ConsensusJournal::new(&self.credentials(principal)?, config)
    }

    /// Writes a keeper's configuration as the JSON that `logkeeper keeper
    /// --config` reads, so a harness can run the keeper as a process of its
    /// own, for example to kill it. Stop the keeper here first: two
    /// keepers must never share its media. A timed authority is not written.
    pub fn write_config(&self, keeper: Uuid) -> io::Result<PathBuf> {
        let config = self
            .configs
            .get(&keeper)
            .ok_or_else(|| io::Error::other("unknown keeper"))?;
        let json = serde_json::json!({
            "keeper": config.keeper,
            "listen": config.listen,
            "data": config.data,
            "tls": {
                "certificate": config.tls.certificate,
                "private_key": config.tls.private_key,
                "ca": config.tls.ca,
            },
            "keepers": config.keepers,
            "peers": config.peers,
            "bulk": config.bulk,
            "domains": config.domains,
            "enrollment": config.enrollment,
            "catalog": config.catalog,
            "catalog_voters": config.catalog_voters,
            "allow_single_catalog": config.allow_single_catalog,
            "lease_millis": config.lease_millis,
            "lease_drift_margin_millis": config.lease_drift_margin_millis,
            "readers": config.readers,
            "writers": config.writers,
            "administrators": config.administrators,
            "max_streams": config.max_streams,
            "repair_after_secs": config.repair_after_secs,
            "park_after_secs": config.park_after_secs,
            "snapshot_send_bytes_per_second": config.snapshot_send_bytes_per_second,
            "sync_mode": config.sync_mode,
        });
        let path = self.dir.path().join(format!("keeper-{keeper}.json"));
        std::fs::write(&path, serde_json::to_vec_pretty(&json)?)?;
        Ok(path)
    }

    /// Stops one keeper and waits for it to release its media.
    pub async fn stop(&mut self, keeper: Uuid) -> io::Result<()> {
        let running = self
            .running
            .remove(&keeper)
            .ok_or_else(|| io::Error::other("keeper is not running"))?;
        running.stop.cancel();
        running.task.await.map_err(io::Error::other)?
    }

    /// Starts a stopped keeper on its original addresses and media.
    pub async fn restart(&mut self, keeper: Uuid) -> io::Result<()> {
        if self.running.contains_key(&keeper) {
            return Err(io::Error::other("keeper is already running"));
        }
        let config = self
            .configs
            .get(&keeper)
            .ok_or_else(|| io::Error::other("unknown keeper"))?
            .clone();
        let listener = super::keeper::bind_listener(config.listen).await?;
        let stop = CancellationToken::new();
        let task = tokio::spawn(config.serve(listener, stop.clone()));
        self.running.insert(keeper, Running { stop, task });
        Ok(())
    }

    /// Retires the two stopped keepers `lost` with `logkeeper keeper
    /// fence-recovery`, then runs `logkeeper keeper recover-stream
    /// --acknowledge-data-loss --lost LOST --fence-proof ...` with their
    /// retirement proofs on the stopped keeper `survivor`, which then has to
    /// be restarted. The retired keepers refuse to start again. The two
    /// replacements are chosen among the live keepers in free domains, such
    /// as the spares of [`LocalCluster::start_spared`].
    #[allow(clippy::field_reassign_with_default)]
    pub async fn recover_stream(
        &self,
        survivor: Uuid,
        stream: journal_contract::StreamId,
        mut lost: [Uuid; 2],
    ) -> io::Result<RecoveryReport> {
        if [survivor, lost[0], lost[1]]
            .iter()
            .any(|keeper| self.running.contains_key(keeper))
        {
            return Err(io::Error::other(
                "stop the surviving keeper and both lost keepers first",
            ));
        }
        lost.sort_unstable();
        let fence_proofs = lost
            .iter()
            .map(|keeper| {
                self.configs
                    .get(keeper)
                    .ok_or_else(|| io::Error::other("unknown keeper"))?
                    .fence_recovery(*keeper)
            })
            .collect::<io::Result<Vec<_>>>()?;
        // Built by assignment: the struct has a field private to unit tests.
        let mut recovery = Recovery::default();
        recovery.acknowledge_data_loss = true;
        recovery.lost = Some(lost.to_vec());
        recovery.fence_proofs = fence_proofs;
        self.configs
            .get(&survivor)
            .ok_or_else(|| io::Error::other("unknown keeper"))?
            .recover_stream(stream, recovery)
            .await
    }

    /// Restarts every keeper with continuous offload to `offload` and
    /// finalizes the cluster version, which offload needs.
    pub async fn enable_offload(
        &mut self,
        principal: &str,
        offload: super::OffloadConfig,
    ) -> io::Result<()> {
        for keeper in self.configs.keys().copied().collect::<Vec<_>>() {
            if self.running.contains_key(&keeper) {
                self.stop(keeper).await?;
            }
            if let Some(config) = self.configs.get_mut(&keeper) {
                config.offload = Some(offload.clone());
            }
            self.restart(keeper).await?;
        }
        self.finalize_version(principal, super::CLUSTER_VERSION_CURRENT)
            .await
            .map(|_| ())
    }

    /// Finalizes the cluster feature level `version` through the catalog, as
    /// an administrator would, retrying while keepers start, and waits until
    /// every running keeper has learned it. A keeper learns the level from
    /// the catalog on its own schedule (every 10 s); until then it writes
    /// none of the formats the level gates, such as its commit indexes,
    /// which an exact recovery from it needs.
    pub async fn finalize_version(&self, principal: &str, version: u32) -> io::Result<u32> {
        let journal = self.journal(principal, &self.journal_config(1 << 20, 1024))?;
        let deadline = std::time::Instant::now() + Duration::from_secs(60);
        let finalized = loop {
            match journal.finalize_version(version).await {
                Ok(finalized) => break finalized,
                Err(_) if std::time::Instant::now() < deadline => {
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }
                Err(error) => return Err(io::Error::other(format!("{error:?}"))),
            }
        };
        for keeper in self.running.keys().copied() {
            loop {
                match journal
                    .client()
                    .keeper_status(keeper, journal_contract::StreamId(0))
                    .await
                {
                    Ok(status) if status.cluster_version >= finalized => break,
                    _ if std::time::Instant::now() < deadline => {
                        tokio::time::sleep(Duration::from_millis(100)).await;
                    }
                    _ => {
                        return Err(io::Error::other(format!(
                            "keeper {keeper} did not learn cluster version {finalized}"
                        )));
                    }
                }
            }
        }
        Ok(finalized)
    }

    /// Stops every keeper.
    pub async fn shutdown(&mut self) -> io::Result<()> {
        for keeper in self.running.keys().copied().collect::<Vec<_>>() {
            self.stop(keeper).await?;
        }
        Ok(())
    }

    fn issue(
        &self,
        name: &str,
        uri: &str,
        purposes: Vec<ExtendedKeyUsagePurpose>,
    ) -> io::Result<Credentials> {
        let key = KeyPair::generate().map_err(io::Error::other)?;
        let mut params = CertificateParams::default();
        params.subject_alt_names = vec![SanType::URI(uri.try_into().map_err(io::Error::other)?)];
        params.extended_key_usages = purposes;
        let cert = params
            .signed_by(&key, &self.issuer)
            .map_err(io::Error::other)?;
        let certificate = self.dir.path().join(format!("{name}.pem"));
        let private_key = self.dir.path().join(format!("{name}.key"));
        std::fs::write(&certificate, cert.pem())?;
        std::fs::write(&private_key, key.serialize_pem())?;
        Ok(Credentials {
            certificate,
            private_key,
            ca: self.roots.clone(),
        })
    }
}

/// Installed trust: each keeper's Ed25519 verification key.
struct LocalVerifier(BTreeMap<u128, [u8; 32]>);

impl TimedOriginalVerifier for LocalVerifier {
    fn verify(&self, keeper: KeeperId, statement: &[u8], signature: &[u8; 64]) -> bool {
        self.0.get(&keeper.0).is_some_and(|key| {
            ring::signature::UnparsedPublicKey::new(&ring::signature::ED25519, key)
                .verify(statement, signature)
                .is_ok()
        })
    }
}

/// A commissioned clock for tests: wall time plus a shared offset.
struct LocalClock {
    key: Arc<Ed25519KeyPair>,
    offset: Arc<AtomicI64>,
}

impl TimedOriginalClock for LocalClock {
    fn authorize(&self, _: &TimedOriginal) -> bool {
        true
    }

    fn sync_upper_micros(&self, _: &TimedOriginal) -> Option<i64> {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .ok()?
            .as_micros();
        i64::try_from(now)
            .ok()?
            .checked_add(self.offset.load(Ordering::SeqCst))
    }

    fn sign(&self, statement: &[u8]) -> Option<[u8; 64]> {
        self.key.sign(statement).as_ref().try_into().ok()
    }
}

fn authority(path: &Path) -> io::Result<Issuer<'static, KeyPair>> {
    let mut params = CertificateParams::default();
    params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    params
        .distinguished_name
        .push(DnType::CommonName, "logkeeper local cluster");
    let key = KeyPair::generate().map_err(io::Error::other)?;
    std::fs::write(
        path,
        params.self_signed(&key).map_err(io::Error::other)?.pem(),
    )?;
    Ok(Issuer::new(params, key))
}

fn free_port() -> io::Result<SocketAddr> {
    StdListener::bind("127.0.0.1:0")?.local_addr()
}

fn provision(config: &Config) -> io::Result<()> {
    let parent = config
        .data
        .parent()
        .ok_or_else(|| io::Error::other("keeper data directory has no parent"))?;
    let name = config
        .data
        .file_name()
        .ok_or_else(|| io::Error::other("keeper data directory has no name"))?;
    let data = parent.canonicalize()?.join(name);
    let provision = Provision {
        keeper: config.keeper,
        data,
        domain: config.domains[&config.keeper].clone(),
        certificate_sha256: hex(&sha256(std::fs::File::open(&config.tls.certificate)?)?),
    };
    std::fs::write(
        config
            .enrollment
            .join(format!("{}.provision.json", config.keeper)),
        serde_json::to_vec(&provision)?,
    )
}
