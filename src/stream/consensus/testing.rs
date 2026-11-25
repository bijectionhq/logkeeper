//! Real keepers on loopback for consumer tests. Enable the
//! `consensus-testing` feature.
//!
//! [`LocalCluster`] starts three voter keepers in distinct failure domains
//! and a catalog keeper, each with its own enrolled media, TLS identity and
//! data directory. Consumers open [`ConsensusJournal`] handles for named
//! client principals and can stop and restart individual keepers.

use std::{
    collections::BTreeMap,
    io,
    net::{SocketAddr, TcpListener as StdListener},
    path::{Path, PathBuf},
    sync::Mutex,
};

use rcgen::{
    BasicConstraints, CertificateParams, DnType, ExtendedKeyUsagePurpose, IsCa, Issuer, KeyPair,
    SanType,
};
use tokio::{net::TcpListener, task::JoinHandle};
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

use super::{
    Config, ConsensusJournal, Credentials, Domains, JournalConfig, Keepers,
    storage::{Authority, Provision, hex, sha256},
};

struct Running {
    stop: CancellationToken,
    task: JoinHandle<io::Result<()>>,
}

/// Three voters and a catalog keeper serving on loopback.
pub struct LocalCluster {
    dir: tempfile::TempDir,
    issuer: Issuer<'static, KeyPair>,
    roots: PathBuf,
    configs: BTreeMap<Uuid, Config>,
    running: BTreeMap<Uuid, Running>,
    keepers: Keepers,
    voters: [Uuid; 3],
    catalog: Uuid,
    issued: Mutex<BTreeMap<String, Credentials>>,
}

impl LocalCluster {
    /// Starts the keepers. Every listed principal may read, write and
    /// administer streams.
    pub async fn start(principals: &[&str]) -> io::Result<Self> {
        let dir = tempfile::tempdir()?;
        let roots = dir.path().join("ca.pem");
        let issuer = authority(&roots)?;
        let voters = [1, 2, 3].map(Uuid::from_u128);
        let catalog = Uuid::from_u128(4);
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
        let mut cluster = Self {
            issuer,
            roots,
            configs: BTreeMap::new(),
            running: BTreeMap::new(),
            keepers: keepers.clone(),
            voters,
            catalog,
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
                readers: principals.clone(),
                writers: principals.clone(),
                administrators: principals.clone(),
                max_streams: 128,
            };
            provision(&config)?;
            config.initialize()?;
            cluster.configs.insert(id, config);
            cluster.restart(id).await?;
        }
        Ok(cluster)
    }

    pub fn voters(&self) -> [Uuid; 3] {
        self.voters
    }

    pub fn catalog(&self) -> Uuid {
        self.catalog
    }

    pub fn keepers(&self) -> &Keepers {
        &self.keepers
    }

    /// The contract configuration for streams placed on the three voters.
    pub fn journal_config(&self, quota_bytes: u64, max_record_bytes: usize) -> JournalConfig {
        JournalConfig {
            keepers: self.keepers.clone(),
            catalog: self.catalog,
            voters: self.voters,
            quota_bytes,
            max_record_bytes,
            deadline_ms: 10_000,
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
