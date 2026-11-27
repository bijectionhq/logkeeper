//! Real previous-binary compatibility and rolling-upgrade tests.
//!
//! N-1 is pinned to `PREV_SHA`, Logkeeper main just before the first change
//! of wire or disk format this release gates: durable park marks and
//! segment relocation, then version negotiation itself.
//! The test builds it once from `git archive` of that exact commit, with
//! `--locked` and an isolated temporary target directory, and caches the
//! binary outside the repository: in `$LOGKEEPER_COMPAT_CACHE`, else
//! `$XDG_CACHE_HOME/logkeeper-compat`, else `~/.cache/logkeeper-compat`,
//! keyed by the commit and the `rustc -V` that built it.
//! `LOGKEEPER_PREV_BIN` names a prebuilt binary instead. It then runs real
//! `old` and `new` `logkeeper` processes side by side.
#![cfg(feature = "consensus-testing")]

use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::Read,
    net::{SocketAddr, TcpListener as StdListener},
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    sync::{Arc, OnceLock},
    time::{Duration, Instant},
};

use bytes::Bytes;
use fs2::FileExt;
use journal_contract::{Epoch, JournalError, Lsn, StreamId};
use logkeeper::stream::consensus::{
    BUILD_VERSION, CLUSTER_VERSION_CURRENT, CLUSTER_VERSION_V1, Client, Credentials, Domains,
    Keepers, features,
};
use rcgen::{
    BasicConstraints, CertificateParams, DnType, ExtendedKeyUsagePurpose, IsCa, Issuer, KeyPair,
    SanType,
};
use sha2::{Digest, Sha256};
use tempfile::TempDir;
use tokio::time::timeout;
use uuid::Uuid;

const PREV_SHA: &str = "44d3f2aadbb3da274c2a8e6b0b6a1edf49ac736c";
const CLIENT_URI: &str = "urn:logkeeper:client:compat";
const WAIT: Duration = Duration::from_secs(30);

static PREV_BIN: OnceLock<PathBuf> = OnceLock::new();

fn new_binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_logkeeper"))
}

/// Where N-1 binaries are cached, outside the repository so `cargo clean`
/// and fresh worktrees reuse them.
fn compat_cache() -> PathBuf {
    if let Some(path) = std::env::var_os("LOGKEEPER_COMPAT_CACHE") {
        return PathBuf::from(path);
    }
    let base = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cache")))
        .expect("HOME or XDG_CACHE_HOME names a cache directory");
    base.join("logkeeper-compat")
}

/// The toolchain that builds the N-1 binary, part of its cache key.
fn toolchain() -> String {
    let output = Command::new("rustc")
        .arg("-V")
        .output()
        .expect("run rustc -V");
    let version = String::from_utf8_lossy(&output.stdout);
    let digest = Sha256::digest(version.trim().as_bytes());
    digest[..6]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Returns a path to the compiled N-1 (`PREV_SHA`) `logkeeper` binary,
/// building and caching it once per commit and toolchain.
fn prev_binary() -> PathBuf {
    PREV_BIN
        .get_or_init(|| {
            if let Some(path) = std::env::var_os("LOGKEEPER_PREV_BIN") {
                let path = PathBuf::from(path);
                assert!(
                    path.exists(),
                    "LOGKEEPER_PREV_BIN does not exist: {}",
                    path.display()
                );
                return path;
            }
            let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let compat_dir = compat_cache().join(format!("{PREV_SHA}-{}", toolchain()));
            fs::create_dir_all(&compat_dir).expect("create target/compat dir");
            let lock_file = OpenOptions::new()
                .create(true)
                .read(true)
                .write(true)
                .open(compat_dir.join("build.lock"))
                .expect("open compat build lock");
            lock_file.lock_exclusive().expect("lock compat build");

            let cached = compat_dir.join("logkeeper");
            if cached.exists() {
                return cached;
            }

            // Export N-1 source with `git archive` into a tempdir and build
            // with an isolated temporary target dir so disk space is reclaimed
            // immediately after caching the single binary.
            let scratch = tempfile::tempdir().expect("create compat build tempdir");
            let src_dir = scratch.path().join("src");
            let target_dir = scratch.path().join("target");
            fs::create_dir_all(&src_dir).expect("create src dir");

            let archive = Command::new("git")
                .current_dir(&manifest_dir)
                .args(["archive", "--format=tar", PREV_SHA])
                .stdout(Stdio::piped())
                .spawn()
                .expect("spawn git archive");
            let archive_out = archive.stdout.expect("git archive stdout");
            let tar_status = Command::new("tar")
                .current_dir(&src_dir)
                .args(["-xf", "-"])
                .stdin(Stdio::from(archive_out))
                .status()
                .expect("extract git archive");
            assert!(
                tar_status.success(),
                "git archive | tar failed for {PREV_SHA}"
            );

            let status = Command::new("cargo")
                .current_dir(&src_dir)
                .env("CARGO_TARGET_DIR", &target_dir)
                .env("CARGO_PROFILE_DEV_DEBUG", "0")
                .env("CARGO_INCREMENTAL", "0")
                .args([
                    "build",
                    "--locked",
                    "--features",
                    "stream",
                    "--bin",
                    "logkeeper",
                ])
                .status()
                .expect("spawn cargo build for N-1 binary");
            assert!(
                status.success(),
                "cargo build failed for N-1 commit {PREV_SHA}"
            );

            let built = target_dir.join("debug").join("logkeeper");
            let tmp = compat_dir.join(format!("logkeeper.tmp.{}", std::process::id()));
            fs::copy(&built, &tmp).expect("copy N-1 binary to cache");
            fs::rename(&tmp, &cached).expect("atomically publish cached N-1 binary");
            cached
        })
        .clone()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binary {
    Old,
    New,
}

impl Binary {
    fn path(self) -> PathBuf {
        match self {
            Self::Old => prev_binary(),
            Self::New => new_binary(),
        }
    }
}

struct ProcessCluster {
    _dir: TempDir,
    voters: [Uuid; 3],
    catalog: Uuid,
    catalog_voters: Option<[Uuid; 3]>,
    keepers: Keepers,
    config_paths: BTreeMap<Uuid, PathBuf>,
    /// Each keeper's configuration without an admin listener, which N-1
    /// refuses as an unknown field.
    configs: BTreeMap<Uuid, serde_json::Value>,
    /// The loopback admin listener each keeper serves on the N binary.
    admin: BTreeMap<Uuid, SocketAddr>,
    client_credentials: Credentials,
    children: BTreeMap<Uuid, Child>,
}

impl Drop for ProcessCluster {
    fn drop(&mut self) {
        for (_, mut child) in std::mem::take(&mut self.children) {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

impl ProcessCluster {
    async fn start(initial: Binary, replicated_catalog: bool) -> Self {
        let dir = tempfile::tempdir().expect("tempdir");
        let roots = dir.path().join("ca.pem");
        let issuer = create_ca(&roots);

        // Use realistic high bits so peer dispatch cannot mistake UUID
        // bytes for a request variant tag.
        let keeper_id =
            |suffix: u128| Uuid::from_u128(0xc421_f8b2_3655_4841_846a_4ab8_02ab_f000 | suffix);
        let voters = [1, 2, 3].map(keeper_id);
        let catalog = keeper_id(4);
        let catalog_voters = replicated_catalog.then_some([voters[0], voters[1], catalog]);
        let roster = [voters[0], voters[1], voters[2], catalog];
        let domains: Domains = roster
            .into_iter()
            .zip(["zone-a", "zone-b", "zone-c", "directory"])
            .map(|(id, domain)| (id, domain.to_owned()))
            .collect();

        let enrollment = dir.path().join("registry");
        fs::create_dir(&enrollment).unwrap();
        // Write N-1-compatible placement.json (no `retired` field when empty).
        fs::write(
            enrollment.join("placement.json"),
            serde_json::to_vec(&serde_json::json!({
                "catalog": catalog,
                "domains": domains,
            }))
            .unwrap(),
        )
        .unwrap();

        let mut keepers = Keepers::new();
        let mut peers = Keepers::new();
        let mut bulk = Keepers::new();
        for id in roster {
            keepers.insert(id, free_port().into());
            peers.insert(id, free_port().into());
            bulk.insert(id, free_port().into());
        }

        let client_credentials = issue_cert(
            dir.path(),
            "client",
            CLIENT_URI,
            vec![ExtendedKeyUsagePurpose::ClientAuth],
            &issuer,
            &roots,
        );

        let mut config_paths = BTreeMap::new();
        let mut configs = BTreeMap::new();
        for id in roster {
            let tls = issue_cert(
                dir.path(),
                &format!("keeper-{id}"),
                &format!("urn:logkeeper:keeper:{id}"),
                vec![
                    ExtendedKeyUsagePurpose::ClientAuth,
                    ExtendedKeyUsagePurpose::ServerAuth,
                ],
                &issuer,
                &roots,
            );
            let data = dir.path().join(format!("data-{id}"));
            let canonical_data = dir
                .path()
                .canonicalize()
                .unwrap()
                .join(format!("data-{id}"));
            let provision = serde_json::json!({
                "keeper": id,
                "data": canonical_data,
                "domain": domains[&id],
                "certificate_sha256": sha256_hex(&tls.certificate),
            });
            fs::write(
                enrollment.join(format!("{id}.provision.json")),
                serde_json::to_vec(&provision).unwrap(),
            )
            .unwrap();

            let mut cfg = serde_json::json!({
                "keeper": id,
                "listen": keepers[&id],
                "data": data,
                "tls": {
                    "certificate": tls.certificate,
                    "private_key": tls.private_key,
                    "ca": tls.ca,
                },
                "keepers": keepers,
                "peers": peers,
                "bulk": bulk,
                "domains": domains,
                "enrollment": enrollment,
                "catalog": catalog,
                "readers": [CLIENT_URI],
                "writers": [CLIENT_URI],
                "administrators": [CLIENT_URI],
                "max_streams": 128,
                "repair_after_secs": 30,
                "park_after_secs": 3600,
                "snapshot_send_bytes_per_second": 0,
                "sync_mode": "fsync",
            });
            if let Some(cv) = catalog_voters {
                cfg.as_object_mut()
                    .unwrap()
                    .insert("catalog_voters".into(), serde_json::json!(cv));
            }
            let cfg_path = dir.path().join(format!("config-{id}.json"));
            let mut written = cfg.clone();
            if initial == Binary::New {
                written
                    .as_object_mut()
                    .unwrap()
                    .insert("allow_single_catalog".into(), serde_json::json!(true));
            }
            fs::write(&cfg_path, serde_json::to_vec_pretty(&written).unwrap()).unwrap();
            configs.insert(id, cfg.clone());

            let init = Command::new(initial.path())
                .args(["keeper", "initialize", "--config"])
                .arg(&cfg_path)
                .status()
                .expect("run keeper initialize");
            assert!(init.success(), "keeper initialize failed for {id}");
            config_paths.insert(id, cfg_path);
        }

        let mut cluster = Self {
            _dir: dir,
            voters,
            catalog,
            catalog_voters,
            keepers,
            config_paths,
            configs,
            admin: roster.into_iter().map(|id| (id, free_port())).collect(),
            client_credentials,
            children: BTreeMap::new(),
        };
        for id in roster {
            cluster.start_keeper(id, initial).await;
        }
        cluster
    }

    fn client(&self) -> Client {
        let client = Client::new(
            &self.client_credentials,
            self.keepers.clone(),
            self.catalog,
            Duration::from_secs(10),
        )
        .expect("build consensus client");
        match self.catalog_voters {
            Some(voters) => client.with_catalog_voters(voters),
            None => client,
        }
    }

    /// The HTTP status of `GET path` on `id`'s admin listener.
    async fn probe(&self, id: Uuid, path: &str) -> Option<u16> {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let mut socket = timeout(
            Duration::from_secs(2),
            tokio::net::TcpStream::connect(self.admin[&id]),
        )
        .await
        .ok()?
        .ok()?;
        socket
            .write_all(
                format!("GET {path} HTTP/1.1\r\nHost: keeper\r\nConnection: close\r\n\r\n")
                    .as_bytes(),
            )
            .await
            .ok()?;
        let mut response = Vec::new();
        timeout(Duration::from_secs(5), socket.read_to_end(&mut response))
            .await
            .ok()?
            .ok()?;
        std::str::from_utf8(&response)
            .ok()?
            .split_whitespace()
            .nth(1)?
            .parse()
            .ok()
    }

    /// Waits until `path` answers 200, as the runbook's `until probe` loops.
    async fn wait_for(&self, id: Uuid, path: &str) -> Duration {
        let started = Instant::now();
        while self.probe(id, path).await != Some(200) {
            assert!(
                started.elapsed() < Duration::from_secs(120),
                "{path} on keeper {id} did not answer 200: abort the rollout"
            );
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
        started.elapsed()
    }

    /// Writes an operator configuration for `logkeeper admin`.
    fn operator_config(&self) -> PathBuf {
        let path = self._dir.path().join("operator.json");
        let mut config = serde_json::json!({
            "tls": {
                "certificate": self.client_credentials.certificate,
                "private_key": self.client_credentials.private_key,
                "ca": self.client_credentials.ca,
            },
            "keepers": self.keepers,
            "catalog": self.catalog,
            "admin": self.admin,
            "admin_mtls": false,
        });
        if let Some(voters) = self.catalog_voters {
            config
                .as_object_mut()
                .unwrap()
                .insert("catalog_voters".into(), serde_json::json!(voters));
        }
        fs::write(&path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
        path
    }

    async fn start_keeper(&mut self, id: Uuid, binary: Binary) {
        assert!(
            !self.children.contains_key(&id),
            "keeper {id} already running"
        );
        // The admin listener is added with the N binary and removed on a
        // rollback, since N-1 refuses an unknown configuration field.
        let mut config = self.configs[&id].clone();
        if binary == Binary::New {
            config.as_object_mut().unwrap().insert(
                "admin".into(),
                serde_json::json!({"listen": self.admin[&id], "mtls": false}),
            );
            // N refuses a single catalog unless told it is a development
            // cluster.
            config
                .as_object_mut()
                .unwrap()
                .insert("allow_single_catalog".into(), serde_json::json!(true));
        }
        fs::write(
            &self.config_paths[&id],
            serde_json::to_vec_pretty(&config).unwrap(),
        )
        .unwrap();
        let child = Command::new(binary.path())
            .args(["keeper", "--config"])
            .arg(&self.config_paths[&id])
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("spawn keeper process");
        self.children.insert(id, child);
        let addr = self.keepers[&id].clone();
        timeout(Duration::from_secs(15), async {
            loop {
                if let Some(child) = self.children.get_mut(&id)
                    && let Ok(Some(status)) = child.try_wait()
                {
                    panic!("keeper {id} ({binary:?}) exited early with {status}");
                }
                if tokio::net::TcpStream::connect(addr.as_str()).await.is_ok() {
                    return;
                }
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .await
        .expect("keeper started listening");
    }

    fn data_dir(&self, id: Uuid) -> PathBuf {
        self._dir.path().join(format!("data-{id}"))
    }

    /// Starts `id` on `binary` and expects it to refuse its media: it must
    /// exit unsuccessfully within the deadline. Returns its standard error.
    fn refused_start(&self, id: Uuid, binary: Binary) -> String {
        let mut child = Command::new(binary.path())
            .args(["keeper", "--config"])
            .arg(&self.config_paths[&id])
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn keeper process");
        let started = Instant::now();
        let status = loop {
            if let Some(status) = child.try_wait().expect("try_wait keeper") {
                break status;
            }
            if started.elapsed() > Duration::from_secs(30) {
                let _ = child.kill();
                let _ = child.wait();
                panic!("keeper {id} ({binary:?}) started on media it should refuse");
            }
            std::thread::sleep(Duration::from_millis(50));
        };
        assert!(!status.success(), "keeper {id} ({binary:?}) exited cleanly");
        let mut stderr = String::new();
        child
            .stderr
            .take()
            .expect("piped stderr")
            .read_to_string(&mut stderr)
            .expect("read keeper stderr");
        stderr
    }

    async fn stop_keeper(&mut self, id: Uuid) {
        let mut child = self.children.remove(&id).expect("keeper not running");
        let pid = child.id().to_string();
        let _ = Command::new("kill").args(["-TERM", &pid]).status();
        let exited = timeout(Duration::from_secs(15), async {
            loop {
                match child.try_wait().expect("try_wait keeper") {
                    Some(status) => return status,
                    None => tokio::time::sleep(Duration::from_millis(25)).await,
                }
            }
        })
        .await;
        match exited {
            Ok(status) => {
                assert!(
                    status.success(),
                    "keeper {id} did not exit cleanly on SIGTERM: {status}"
                );
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                panic!("keeper {id} timed out shutting down on SIGTERM");
            }
        }
    }

    async fn stop_all(&mut self) {
        let ids: Vec<Uuid> = self.children.keys().copied().collect();
        for id in ids {
            self.stop_keeper(id).await;
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn old_keeper_writes_new_keeper_opens_the_data() {
    let mut cluster = ProcessCluster::start(Binary::Old, false).await;
    let client = cluster.client();
    let stream = StreamId(1001);
    client
        .create(
            stream,
            logkeeper::stream::consensus::Voters::from(cluster.voters),
            4 * 1024 * 1024,
        )
        .await
        .unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(101))
        .await
        .unwrap()
        .fence;
    for i in 1..=20u64 {
        client
            .append(
                stream,
                fence,
                Lsn(i),
                Bytes::from(format!("old-record-{i}")),
            )
            .await
            .unwrap();
    }
    assert_eq!(client.head(stream).await, Ok(Lsn(20)));

    // Stop all old keepers and restart all of them on the new binary.
    cluster.stop_all().await;
    let roster: Vec<Uuid> = cluster.config_paths.keys().copied().collect();
    for id in roster {
        cluster.start_keeper(id, Binary::New).await;
    }

    // Verify every record written by the old binary is readable on the new
    // binary, and new writes continue seamlessly.
    let fresh_client = cluster.client();
    assert_eq!(fresh_client.head(stream).await, Ok(Lsn(20)));
    let page = fresh_client
        .read(stream, Lsn(1), 20, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 20);
    for (idx, (lsn, payload)) in page.records.iter().enumerate() {
        let expected_lsn = (idx + 1) as u64;
        assert_eq!(*lsn, Lsn(expected_lsn));
        assert_eq!(
            payload.as_ref(),
            format!("old-record-{expected_lsn}").as_bytes()
        );
    }
    for i in 21..=30u64 {
        fresh_client
            .append(
                stream,
                fence,
                Lsn(i),
                Bytes::from(format!("new-record-{i}")),
            )
            .await
            .unwrap();
    }
    assert_eq!(fresh_client.head(stream).await, Ok(Lsn(30)));
    assert_eq!(fresh_client.cluster_version().await, Ok(CLUSTER_VERSION_V1));

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn mixed_two_old_one_new_cluster_keeps_serving() {
    let mut cluster = ProcessCluster::start(Binary::Old, false).await;
    let client = cluster.client();
    let stream = StreamId(1002);
    client
        .create(
            stream,
            logkeeper::stream::consensus::Voters::from(cluster.voters),
            4 * 1024 * 1024,
        )
        .await
        .unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(102))
        .await
        .unwrap()
        .fence;
    for i in 1..=5u64 {
        client
            .append(stream, fence, Lsn(i), Bytes::from(format!("mixed-{i}")))
            .await
            .unwrap();
    }

    // Upgrade 1 of the 3 voters -> mixed 2-old / 1-new voter cluster.
    let upgraded = cluster.voters[0];
    cluster.stop_keeper(upgraded).await;
    cluster.start_keeper(upgraded, Binary::New).await;

    let status_new = client.keeper_status(upgraded, stream).await.unwrap();
    assert_eq!(status_new.build_version, BUILD_VERSION);
    assert_eq!(status_new.features, features::SUPPORTED);
    assert_eq!(status_new.cluster_version, CLUSTER_VERSION_V1);

    let status_old = client
        .keeper_status(cluster.voters[1], stream)
        .await
        .unwrap();
    assert_eq!(status_old.features, 0);
    assert_eq!(status_old.cluster_version, CLUSTER_VERSION_V1);

    for i in 6..=15u64 {
        client
            .append(stream, fence, Lsn(i), Bytes::from(format!("mixed-{i}")))
            .await
            .unwrap();
    }
    assert_eq!(client.head(stream).await, Ok(Lsn(15)));
    let page = client
        .read(stream, Lsn(1), 15, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 15);
    assert_eq!(
        client.configuration(stream).await.unwrap().voters,
        cluster.voters,
        "mixed cluster must not trigger spurious repair"
    );

    // Upgrade a second voter -> 1-old / 2-new voter cluster.
    let second = cluster.voters[1];
    cluster.stop_keeper(second).await;
    cluster.start_keeper(second, Binary::New).await;
    for i in 16..=20u64 {
        client
            .append(stream, fence, Lsn(i), Bytes::from(format!("mixed-{i}")))
            .await
            .unwrap();
    }
    assert_eq!(client.head(stream).await, Ok(Lsn(20)));
    let page = client
        .read(stream, Lsn(1), 20, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 20);

    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn rolling_restart_one_at_a_time_under_load() {
    let mut cluster = ProcessCluster::start(Binary::Old, true).await;
    let client = cluster.client();
    let stream = StreamId(1003);
    client
        .create(
            stream,
            logkeeper::stream::consensus::Voters::from(cluster.voters),
            8 * 1024 * 1024,
        )
        .await
        .unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(103))
        .await
        .unwrap()
        .fence;

    // Run continuous writes in the background while upgrading every keeper one
    // at a time from N-1 to N.
    let stop_writer = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let acked = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let writer_handle = {
        let client = cluster.client();
        let stop = stop_writer.clone();
        let acked = acked.clone();
        tokio::spawn(async move {
            let mut next = 1u64;
            let mut recorded = Vec::new();
            while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                let payload = Bytes::from(format!("rolling-load-{next:06}"));
                match client
                    .append(stream, fence, Lsn(next), payload.clone())
                    .await
                {
                    Ok(_) => {
                        recorded.push((Lsn(next), payload));
                        acked.store(next, std::sync::atomic::Ordering::Release);
                        next += 1;
                    }
                    Err(JournalError::Unavailable) => {
                        // Re-check head in case the write committed right before
                        // a leader step-down during restart.
                        if let Ok(head) = client.head(stream).await
                            && head.0 >= next
                        {
                            recorded.push((Lsn(next), payload));
                            acked.store(next, std::sync::atomic::Ordering::Release);
                            next += 1;
                        }
                        tokio::time::sleep(Duration::from_millis(50)).await;
                    }
                    Err(other) => panic!("unexpected error during rolling upgrade: {other:?}"),
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
            recorded
        })
    };

    // Wait for initial progress on all-OLD.
    timeout(WAIT, async {
        while acked.load(std::sync::atomic::Ordering::Acquire) < 8 {
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .expect("initial writes on old cluster");

    let started = Instant::now();
    // The runbook (docs/runbooks/rolling-upgrade.md), one keeper at a time,
    // the catalog keeper and catalog voters first (step 2).
    let upgrade_order = [
        cluster.catalog,
        cluster.voters[0],
        cluster.voters[1],
        cluster.voters[2],
    ];
    for id in upgrade_order {
        let before = acked.load(std::sync::atomic::Ordering::Acquire);
        // Step 6. N-1 has no admin listener, so instead of `/safe-to-stop`
        // the stream's other voters must report healthy replicas.
        timeout(WAIT, async {
            loop {
                let mut healthy = true;
                for voter in cluster.voters.into_iter().filter(|voter| *voter != id) {
                    healthy &= client
                        .keeper_status(voter, stream)
                        .await
                        .is_ok_and(|status| status.replica == Some(true));
                }
                if healthy {
                    return;
                }
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .await
        .expect("the other voters are healthy before a keeper stops");
        // Step 7: SIGTERM hands off leadership; start the new binary with its
        // admin listener.
        cluster.stop_keeper(id).await;
        cluster.start_keeper(id, Binary::New).await;
        // Step 8: wait until it is ready.
        cluster.wait_for(id, "/ready").await;
        assert_eq!(cluster.probe(id, "/live").await, Some(200));
        assert_eq!(
            client.keeper_status(id, stream).await.unwrap().features,
            features::SUPPORTED
        );
        // Step 9: writes go on before the next keeper.
        timeout(WAIT, async {
            while acked.load(std::sync::atomic::Ordering::Acquire) < before + 5 {
                tokio::time::sleep(Duration::from_millis(25)).await;
            }
        })
        .await
        .expect("writes progressed after rolling restart");
    }
    // Every keeper now answers `/safe-to-stop`, as a later upgrade asks.
    for id in upgrade_order {
        cluster.wait_for(id, "/safe-to-stop").await;
    }
    let elapsed = started.elapsed();

    stop_writer.store(true, std::sync::atomic::Ordering::Relaxed);
    let recorded = writer_handle.await.unwrap();
    let total = recorded.len();
    assert!(
        total >= 28,
        "expected continuous writes during upgrade, got {total}"
    );
    eprintln!(
        "rolling upgrade of 4 keepers under load completed in {:.2}s ({total} records acknowledged)",
        elapsed.as_secs_f64()
    );

    // Every acknowledged record must read back intact.
    assert_eq!(client.head(stream).await, Ok(Lsn(total as u64)));
    let page = client
        .read(stream, Lsn(1), total, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records, recorded);

    // Step 11: finalize with the operator CLI, as the runbook does.
    assert_eq!(client.cluster_version().await, Ok(CLUSTER_VERSION_V1));
    let operator = cluster.operator_config();
    let finalized = timeout(WAIT, async {
        loop {
            let output = Command::new(new_binary())
                .args(["admin", "finalize-version", "--config"])
                .arg(&operator)
                .output()
                .expect("run logkeeper admin finalize-version");
            let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
            if output.status.success() {
                return stdout;
            }
            // Unavailable while a keeper is still settling: retry.
            tokio::time::sleep(Duration::from_millis(250)).await;
        }
    })
    .await
    .expect("lk admin finalize-version succeeded");
    assert!(
        finalized.contains(&format!("cluster_version: {CLUSTER_VERSION_CURRENT}")),
        "{finalized}"
    );
    assert_eq!(client.cluster_version().await, Ok(CLUSTER_VERSION_CURRENT));

    // Once finalized, keepers write N formats, here the checkpoint of the
    // finalized level: LKRWAL06, which also carries each stream's commit
    // index from CLUSTER_VERSION_LEASES on. An N-1 binary refuses the media
    // rather than misreading it.
    let victim = cluster.voters[0];
    let checkpoints = cluster.data_dir(victim).join("raft-checkpoints");
    let n_checkpoint = || {
        fs::read_dir(&checkpoints)
            .into_iter()
            .flatten()
            .flatten()
            .any(|entry| fs::read(entry.path()).is_ok_and(|bytes| bytes.starts_with(b"LKRWAL06")))
    };
    let mut next = client.head(stream).await.unwrap().0 + 1;
    timeout(Duration::from_secs(150), async {
        while !n_checkpoint() {
            match client
                .append(stream, fence, Lsn(next), Bytes::from_static(b"finalized"))
                .await
            {
                Ok(_) => next += 1,
                Err(JournalError::Unavailable) => {
                    next = client.head(stream).await.map_or(next, |head| head.0 + 1);
                }
                Err(error) => panic!("append after finalization failed: {error:?}"),
            }
            tokio::time::sleep(Duration::from_millis(250)).await;
        }
    })
    .await
    .expect("a finalized keeper wrote an N checkpoint");
    cluster.stop_keeper(victim).await;
    let stderr = cluster.refused_start(victim, Binary::Old);
    assert!(!stderr.trim().is_empty(), "N-1 refused without a message");
    eprintln!("N-1 refused finalized media: {}", stderr.trim());

    cluster.stop_all().await;
}

/// An N keeper certifies a copy that opened without hearing a leader by
/// asking the catalog (`Request::Staging`), which an N-1 catalog cannot
/// answer. Such copies must stay uncertified, neither campaigning nor
/// serving, until a leader's append certifies them, never be taken as
/// certified.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn copies_under_an_n1_catalog_wait_for_a_leader_to_certify_them() {
    let mut cluster = ProcessCluster::start(Binary::Old, false).await;
    let client = cluster.client();
    let stream = StreamId(1005);
    client
        .create(
            stream,
            logkeeper::stream::consensus::Voters::from(cluster.voters),
            4 * 1024 * 1024,
        )
        .await
        .unwrap();
    let fence = client
        .seal(stream, Epoch(0), Uuid::from_u128(105))
        .await
        .unwrap()
        .fence;
    for at in 1..=3u64 {
        client
            .append(
                stream,
                fence,
                Lsn(at),
                Bytes::from(format!("n1-catalog-{at}")),
            )
            .await
            .unwrap();
    }
    // Every voter stops; two come back on N while the catalog stays N-1.
    let [a, b, c] = cluster.voters;
    for voter in [a, b, c] {
        cluster.stop_keeper(voter).await;
    }
    for voter in [a, b] {
        cluster.start_keeper(voter, Binary::New).await;
    }
    // Two N copies are a quorum, but neither is certified, so neither
    // campaigns: the stream has no leader.
    tokio::time::sleep(Duration::from_secs(5)).await;
    assert_eq!(
        cluster.client().head(stream).await,
        Err(JournalError::Unavailable)
    );

    // An N-1 voter campaigns, as N-1 does, and its appends certify the N
    // copies, so they keep the stream once it stops again.
    cluster.start_keeper(c, Binary::Old).await;
    timeout(WAIT, async {
        while cluster.client().head(stream).await != Ok(Lsn(3)) {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the N-1 voter leads and certifies the N copies");
    let client = cluster.client();
    client
        .append(stream, fence, Lsn(4), Bytes::from_static(b"certified"))
        .await
        .unwrap();
    cluster.stop_keeper(c).await;
    timeout(WAIT, async {
        loop {
            match client
                .append(stream, fence, Lsn(5), Bytes::from_static(b"on n"))
                .await
            {
                Ok(_) => break,
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(100)).await
                }
                Err(error) => panic!("append on the certified N copies failed: {error:?}"),
            }
        }
    })
    .await
    .expect("the certified N copies elect a leader");
    let page = client
        .read(stream, Lsn(1), 5, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(page.records.len(), 5);
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn downgrade_before_finalize_works() {
    let mut cluster = ProcessCluster::start(Binary::Old, false).await;
    let client = cluster.client();
    let s1 = StreamId(1004);
    client
        .create(
            s1,
            logkeeper::stream::consensus::Voters::from(cluster.voters),
            4 * 1024 * 1024,
        )
        .await
        .unwrap();
    let fence1 = client
        .seal(s1, Epoch(0), Uuid::from_u128(104))
        .await
        .unwrap()
        .fence;
    for i in 1..=5u64 {
        client
            .append(s1, fence1, Lsn(i), Bytes::from(format!("pre-upgrade-{i}")))
            .await
            .unwrap();
    }

    // Upgrade all keepers to NEW without finalizing cluster version.
    let roster: Vec<Uuid> = cluster.config_paths.keys().copied().collect();
    for &id in &roster {
        cluster.stop_keeper(id).await;
        cluster.start_keeper(id, Binary::New).await;
    }
    assert_eq!(client.cluster_version().await, Ok(CLUSTER_VERSION_V1));

    // Write additional records and create a new stream on NEW while unfinalized.
    for i in 6..=15u64 {
        client
            .append(
                s1,
                fence1,
                Lsn(i),
                Bytes::from(format!("unfinalized-new-{i}")),
            )
            .await
            .unwrap();
    }
    let s2 = StreamId(1005);
    client
        .create(
            s2,
            logkeeper::stream::consensus::Voters::from(cluster.voters),
            4 * 1024 * 1024,
        )
        .await
        .unwrap();
    let fence2 = client
        .seal(s2, Epoch(0), Uuid::from_u128(105))
        .await
        .unwrap()
        .fence;
    for i in 1..=5u64 {
        client
            .append(s2, fence2, Lsn(i), Bytes::from(format!("s2-new-{i}")))
            .await
            .unwrap();
    }

    // Downgrade one keeper first and verify finalize is refused while an old
    // keeper is still in the cluster.
    let first_down = cluster.voters[0];
    cluster.stop_keeper(first_down).await;
    cluster.start_keeper(first_down, Binary::Old).await;
    assert_eq!(
        client.finalize_version(CLUSTER_VERSION_CURRENT).await,
        Err(JournalError::Unsupported),
        "finalize must be refused while any keeper runs N-1"
    );

    // Downgrade the remaining keepers back to OLD.
    for &id in &roster {
        if id != first_down {
            cluster.stop_keeper(id).await;
            cluster.start_keeper(id, Binary::Old).await;
        }
    }

    // Old keepers open and serve everything written by the new binary before
    // finalize, and continue accepting writes.
    let after_client = cluster.client();
    assert_eq!(after_client.head(s1).await, Ok(Lsn(15)));
    assert_eq!(after_client.head(s2).await, Ok(Lsn(5)));
    let p1 = after_client
        .read(s1, Lsn(1), 15, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(p1.records.len(), 15);
    assert_eq!(p1.records[0].1.as_ref(), b"pre-upgrade-1");
    assert_eq!(p1.records[14].1.as_ref(), b"unfinalized-new-15");
    let p2 = after_client
        .read(s2, Lsn(1), 5, Duration::ZERO)
        .await
        .unwrap();
    assert_eq!(p2.records.len(), 5);
    assert_eq!(p2.records[4].1.as_ref(), b"s2-new-5");

    for i in 16..=20u64 {
        after_client
            .append(
                s1,
                fence1,
                Lsn(i),
                Bytes::from(format!("post-downgrade-{i}")),
            )
            .await
            .unwrap();
    }
    assert_eq!(after_client.head(s1).await, Ok(Lsn(20)));

    cluster.stop_all().await;
}

fn create_ca(path: &Path) -> Issuer<'static, KeyPair> {
    let mut params = CertificateParams::default();
    params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    params
        .distinguished_name
        .push(DnType::CommonName, "logkeeper compat ca");
    let key = KeyPair::generate().unwrap();
    fs::write(path, params.self_signed(&key).unwrap().pem()).unwrap();
    Issuer::new(params, key)
}

fn issue_cert(
    dir: &Path,
    name: &str,
    uri: &str,
    purposes: Vec<ExtendedKeyUsagePurpose>,
    issuer: &Issuer<'static, KeyPair>,
    ca: &Path,
) -> Credentials {
    let key = KeyPair::generate().unwrap();
    let mut params = CertificateParams::default();
    params.subject_alt_names = vec![SanType::URI(uri.try_into().unwrap())];
    params.extended_key_usages = purposes;
    let cert = params.signed_by(&key, issuer).unwrap();
    let certificate = dir.join(format!("{name}.pem"));
    let private_key = dir.join(format!("{name}.key"));
    fs::write(&certificate, cert.pem()).unwrap();
    fs::write(&private_key, key.serialize_pem()).unwrap();
    Credentials {
        certificate,
        private_key,
        ca: ca.to_owned(),
    }
}

fn free_port() -> SocketAddr {
    StdListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
}

fn sha256_hex(path: &Path) -> String {
    let mut file = File::open(path).unwrap();
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 8192];
    loop {
        let n = file.read(&mut buf).unwrap();
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let digest: [u8; 32] = hasher.finalize().into();
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}
