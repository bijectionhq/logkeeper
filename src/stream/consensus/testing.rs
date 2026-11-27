//! Real keepers on loopback for consumer tests. Enable the
//! `consensus-testing` feature.
//!
//! [`LocalCluster`] starts three voter keepers in distinct failure domains
//! and a catalog keeper, each with its own enrolled media, TLS identity and
//! data directory. Consumers open [`ConsensusJournal`] handles for named
//! client principals and can stop and restart individual keepers.
//! [`LocalCluster::start_replicated_catalog`] instead hosts the catalog as a
//! consensus stream on two voters and the catalog keeper.
//!
//! Its keepers flush with plain `fsync` unless the process installed a
//! [`SyncMode`] before starting the cluster, so tests stay fast on macOS.

use std::{
    collections::BTreeMap,
    io,
    net::{SocketAddr, TcpListener as StdListener},
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
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
    Config, ConsensusJournal, Credentials, Domains, JournalConfig, Keepers, SyncMode,
    TimedAuthority,
    storage::{Authority, Provision, hex, sha256},
};

struct Running {
    stop: CancellationToken,
    task: JoinHandle<io::Result<()>>,
}

/// Three voters and a catalog keeper serving on loopback.
pub struct LocalCluster {
    verifier: Arc<dyn TimedOriginalVerifier>,
    offset: Arc<AtomicI64>,
    dir: tempfile::TempDir,
    issuer: Issuer<'static, KeyPair>,
    roots: PathBuf,
    configs: BTreeMap<Uuid, Config>,
    running: BTreeMap<Uuid, Running>,
    keepers: Keepers,
    voters: [Uuid; 3],
    catalog: Uuid,
    catalog_voters: Option<[Uuid; 3]>,
    issued: Mutex<BTreeMap<String, Credentials>>,
}

impl LocalCluster {
    /// Starts the keepers. Every listed principal may read, write and
    /// administer streams.
    pub async fn start(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, false, 600, false).await
    }

    /// Starts the keepers with a replicated catalog on voters 1 and 2 and
    /// the catalog keeper, which seeds it.
    pub async fn start_replicated_catalog(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, false, 600, true).await
    }

    /// Starts the keepers so that a stream idle for `park_after_secs` is
    /// parked on every voter.
    pub async fn start_parking(principals: &[&str], park_after_secs: u64) -> io::Result<Self> {
        Self::start_with(principals, false, park_after_secs, false).await
    }

    /// Starts the keepers with timed-original authority: each keeper signs
    /// with its own Ed25519 key and samples a wall clock shifted by
    /// [`LocalCluster::shift_timed_clock`].
    pub async fn start_timed(principals: &[&str]) -> io::Result<Self> {
        Self::start_with(principals, true, 600, false).await
    }

    async fn start_with(
        principals: &[&str],
        timed: bool,
        park_after_secs: u64,
        replicated: bool,
    ) -> io::Result<Self> {
        let dir = tempfile::tempdir()?;
        let roots = dir.path().join("ca.pem");
        let issuer = authority(&roots)?;
        let voters = [1, 2, 3].map(Uuid::from_u128);
        let catalog = Uuid::from_u128(4);
        let catalog_voters = replicated.then_some([voters[0], voters[1], catalog]);
        let roster = voters.into_iter().chain([catalog]).collect::<Vec<_>>();
        let domains: Domains = roster
            .iter()
            .zip(["zone-a", "zone-b", "zone-c", "directory"])
            .map(|(id, domain)| (*id, domain.into()))
            .collect();
        let enrollment = dir.path().join("registry");
        std::fs::create_dir(&enrollment)?;
        std::fs::write(
            enrollment.join("placement.json"),
            serde_json::to_vec(&Authority {
                catalog,
                domains: domains.clone(),
            })?,
        )?;
        let [mut keepers, mut peers, mut bulk] = [(); 3].map(|_| Keepers::new());
        for id in &roster {
            keepers.insert(*id, free_port()?);
            peers.insert(*id, free_port()?);
            bulk.insert(*id, free_port()?);
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
            voters,
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
                listen: keepers[&id],
                data: cluster.dir.path().join(format!("data-{id}")),
                tls,
                keepers: keepers.clone(),
                peers: peers.clone(),
                bulk: bulk.clone(),
                domains: domains.clone(),
                enrollment: enrollment.clone(),
                catalog,
                catalog_voters,
                readers: principals.clone(),
                writers: principals.clone(),
                administrators: principals.clone(),
                max_streams: 128,
                repair_after_secs: 600,
                park_after_secs,
                snapshot_send_bytes_per_second: 0,
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

    pub fn voters(&self) -> [Uuid; 3] {
        self.voters
    }

    pub fn catalog(&self) -> Uuid {
        self.catalog
    }

    /// The replicated catalog's voters, when the cluster runs one.
    pub fn catalog_voters(&self) -> Option<[Uuid; 3]> {
        self.catalog_voters
    }

    pub fn keepers(&self) -> &Keepers {
        &self.keepers
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
            placement: None,
            draining: Default::default(),
            quota_bytes,
            max_record_bytes,
            deadline_ms: 10_000,
            domain: None,
        }
    }

    /// A contract configuration that places each stream on three of the
    /// four keepers, each in its own failure domain.
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
        let listener = TcpListener::bind(config.listen).await?;
        let stop = CancellationToken::new();
        let task = tokio::spawn(config.serve(listener, stop.clone()));
        self.running.insert(keeper, Running { stop, task });
        Ok(())
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
