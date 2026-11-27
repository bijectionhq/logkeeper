//! Continuous offload to object storage (`keeper/offload.rs`).

use super::*;
use crate::stream::consensus::{
    OffloadConfig,
    offload::{Record, Store},
};

/// An offload configuration for a directory store with small batches.
pub(super) fn offload_config(directory: &std::path::Path) -> OffloadConfig {
    serde_json::from_value(serde_json::json!({
        "url": format!("file://{}", directory.display()),
        "batch_bytes": 2048,
        "batch_interval_ms": 200,
        "max_lag_bytes": 1 << 30,
    }))
    .unwrap()
}

impl Cluster {
    /// Starts a cluster whose keepers offload to `offload`, and finalizes
    /// the cluster version, which offload needs.
    pub(super) async fn start_offloaded(offload: &OffloadConfig) -> Self {
        let cluster =
            Self::start_configured(["a", "b", "c", "d"], None, false, Some(offload.clone())).await;
        cluster.finalize().await;
        cluster
    }
}

fn payload(lsn: u64) -> Bytes {
    Bytes::from(format!("record {lsn:06} {}", "x".repeat(100)))
}

async fn append_range(journal: &Client, stream: StreamId, fence: Fence, from: u64, to: u64) {
    for lsn in from..=to {
        timeout(WAIT, async {
            loop {
                match journal.append(stream, fence, Lsn(lsn), payload(lsn)).await {
                    Ok(at) => break assert_eq!(at, Lsn(lsn)),
                    Err(JournalError::Unavailable) => {
                        tokio::time::sleep(Duration::from_millis(20)).await
                    }
                    Err(error) => panic!("append {lsn}: {error:?}"),
                }
            }
        })
        .await
        .unwrap();
    }
}

async fn flushed(
    journal: &Client,
    stream: StreamId,
    through: u64,
) -> crate::stream::consensus::OffloadStatus {
    timeout(WAIT * 2, async {
        loop {
            if let Ok(status) = journal.offload_status(stream, true).await
                && status.offloaded_through >= Lsn(through)
            {
                return status;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("offload caught up")
}

async fn read_all(journal: &Client, stream: StreamId, from: u64, to: u64) -> Vec<(Lsn, Bytes)> {
    let mut records = Vec::new();
    let mut next = Lsn(from);
    while next.0 <= to {
        let page = journal
            .read(stream, next, 64, Duration::ZERO)
            .await
            .unwrap_or_else(|error| panic!("read from {}: {error:?}", next.0));
        assert!(!page.records.is_empty(), "empty page at {}", next.0);
        next = Lsn(page.records.last().unwrap().0.0 + 1);
        records.extend(page.records);
    }
    records
}

fn check(records: &[(Lsn, Bytes)], from: u64, to: u64) {
    let expected = (from..=to)
        .map(|lsn| (Lsn(lsn), payload(lsn)))
        .collect::<Vec<_>>();
    assert_eq!(records, expected);
}

fn objects(directory: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut found = Vec::new();
    let mut stack = vec![directory.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "seg") {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn offload_survives_leader_changes_and_serves_reads_below_the_local_floor() {
    let store = tempfile::tempdir().unwrap();
    let mut config = offload_config(store.path());
    config.retain_local_bytes = Some(1500);
    let mut cluster = Cluster::start_offloaded(&config).await;
    let journal = cluster.client(&cluster.credentials);
    let ids = cluster.ids;
    let stream = StreamId(41);
    journal
        .create(stream, [ids[0], ids[1], ids[2]], 1 << 24)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap()
        .fence;
    append_range(&journal, stream, fence, 1, 60).await;
    let status = flushed(&journal, stream, 60).await;
    assert_eq!(status.floor, Lsn(1));
    assert_eq!(status.lineage, 0);
    assert!(!objects(store.path()).is_empty());
    // Retention keeps about 1500 bytes locally once the records are offloaded.
    let status = timeout(WAIT, async {
        loop {
            let status = journal.offload_status(stream, false).await.unwrap();
            if status.local_floor > Lsn(40) {
                return status;
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("retention dropped offloaded records");
    assert!(status.local_floor <= Lsn(61));
    check(&read_all(&journal, stream, 1, 60).await, 1, 60);

    // A new leader continues from the replicated offloaded_through.
    let leader = cluster.leader_after_head(&journal, stream).await;
    cluster.running.remove(&leader).unwrap().stop().await;
    append_range(&journal, stream, fence, 61, 120).await;
    let status = flushed(&journal, stream, 120).await;
    assert_eq!(status.offloaded_through, Lsn(120));
    cluster.restart(leader).await;
    check(&read_all(&journal, stream, 1, 120).await, 1, 120);
    // Every keeper serves reads below its local floor from the store.
    for id in [ids[0], ids[1], ids[2]] {
        let group = cluster.group(id, stream).await;
        let applied = timeout(WAIT, async {
            loop {
                if let Some(view) = group.state.offload_view()
                    && view.offload.through >= Lsn(100)
                {
                    return view;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        })
        .await
        .expect("every voter applied offloaded_through");
        assert!(applied.local_floor > Lsn(1), "{id}: {applied:?}");
        let remote = group.state.remote(Lsn(1)).expect("Lsn 1 is remote");
        let offloader = cluster.running[&id].engine.offload.clone().unwrap();
        let page = offloader.read(stream, remote, 10).await.unwrap();
        check(&page.records, 1, 10);
    }
    // The writer's trim moves the logical floor below the local one.
    journal.trim(stream, fence, Lsn(30)).await.unwrap();
    assert_eq!(
        journal.read(stream, Lsn(5), 10, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(31) })
    );
    check(&read_all(&journal, stream, 31, 120).await, 31, 120);
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_object_store_outage_backpressures_writers_until_offload_catches_up() {
    let root = tempfile::tempdir().unwrap();
    let directory = root.path().join("store");
    let mut config = offload_config(&directory);
    config.max_lag_bytes = 3000;
    let mut cluster = Cluster::start_offloaded(&config).await;
    let journal = cluster.client_within(&cluster.credentials, Duration::from_secs(2));
    let ids = cluster.ids;
    let stream = StreamId(42);
    journal
        .create(stream, [ids[0], ids[1], ids[2]], 1 << 24)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap()
        .fence;
    append_range(&journal, stream, fence, 1, 10).await;
    flushed(&journal, stream, 10).await;
    // The store goes away: the directory becomes a file.
    std::fs::rename(&directory, root.path().join("away")).unwrap();
    std::fs::write(&directory, b"not a directory").unwrap();
    let mut refused = false;
    let mut next = 11;
    let started = Instant::now();
    while started.elapsed() < WAIT && !refused {
        match journal
            .append(stream, fence, Lsn(next), payload(next))
            .await
        {
            Ok(_) => next += 1,
            Err(JournalError::Unavailable) => refused = true,
            Err(error) => panic!("{error:?}"),
        }
    }
    assert!(refused, "appends continued without offload");
    let lag = journal.offload_status(stream, false).await.unwrap();
    assert_eq!(lag.offloaded_through, Lsn(10));
    let leader = cluster.leader(stream).await;
    let metrics = &cluster.running[&leader]
        .engine
        .offload
        .as_ref()
        .unwrap()
        .store
        .metrics;
    assert!(metrics.upload_failures.load(Ordering::Relaxed) > 0);
    assert!(metrics.backpressured_appends.load(Ordering::Relaxed) > 0);
    // The store returns; offload catches up and writers resume.
    std::fs::remove_file(&directory).unwrap();
    std::fs::rename(root.path().join("away"), &directory).unwrap();
    let journal = cluster.client(&cluster.credentials);
    append_range(&journal, stream, fence, next, next + 5).await;
    flushed(&journal, stream, next + 5).await;
    check(&read_all(&journal, stream, 1, next + 5).await, 1, next + 5);
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn uploads_after_a_crash_mid_upload_are_idempotent_and_corruption_is_detected() {
    let directory = tempfile::tempdir().unwrap();
    let mut config = offload_config(directory.path());
    // Upload only on flush, so the test controls what is in the store.
    config.batch_interval_ms = 3_600_000;
    config.batch_bytes = 1 << 30;
    config.max_lag_bytes = 1 << 40;
    config.retain_local_bytes = Some(0);
    let mut cluster = Cluster::start_offloaded(&config).await;
    let journal = cluster.client(&cluster.credentials);
    let ids = cluster.ids;
    let stream = StreamId(43);
    journal
        .create(stream, [ids[0], ids[1], ids[2]], 1 << 24)
        .await
        .unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap()
        .fence;
    append_range(&journal, stream, fence, 1, 20).await;
    // A leader that crashed mid-upload left its object of 1..=20 in the
    // store without committing offloaded_through, and a torn object from
    // another attempt (an S3 PUT is atomic, but a directory store or an
    // operator's copy may leave one) that claims 1..=30.
    let side = Store::open(&config).unwrap();
    let records = (1..=20)
        .map(|lsn| Record {
            lsn: Lsn(lsn),
            timed: false,
            bytes: payload(lsn),
        })
        .collect::<Vec<_>>();
    assert!(
        side.upload(stream, 0, &records, Vec::new())
            .await
            .unwrap()
            .0
    );
    let torn = side.segment_path(stream, 0, Lsn(1), Lsn(30));
    std::fs::create_dir_all(directory.path().join(torn.to_string()).parent().unwrap()).unwrap();
    std::fs::write(directory.path().join(torn.to_string()), b"LKOFF001 torn").unwrap();
    let status = flushed(&journal, stream, 20).await;
    assert_eq!(status.offloaded_through, Lsn(20));
    let leader = cluster.leader(stream).await;
    let metrics = &cluster.running[&leader]
        .engine
        .offload
        .as_ref()
        .unwrap()
        .store
        .metrics;
    assert_eq!(metrics.existing_objects.load(Ordering::Relaxed), 1);
    assert_eq!(metrics.uploaded_objects.load(Ordering::Relaxed), 0);
    // Retention drops everything offloaded; reads skip the torn object.
    timeout(WAIT, async {
        while journal
            .offload_status(stream, false)
            .await
            .unwrap()
            .local_floor
            <= Lsn(20)
        {
            let _ = journal.offload_status(stream, true).await;
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("retention dropped the local copies");
    check(&read_all(&journal, stream, 1, 20).await, 1, 20);
    assert!(metrics.corrupt_objects.load(Ordering::Relaxed) >= 1);
    // Damage the only good object: reads refuse it as corrupt.
    let good = directory
        .path()
        .join(side.segment_path(stream, 0, Lsn(1), Lsn(20)).to_string());
    let mut bytes = std::fs::read(&good).unwrap();
    let middle = bytes.len() / 2;
    bytes[middle] ^= 0xff;
    std::fs::write(&good, bytes).unwrap();
    // Each keeper caches what it fetched, so restart them to fetch again.
    for id in [ids[0], ids[1], ids[2]] {
        cluster.running.remove(&id).unwrap().stop().await;
        cluster.restart(id).await;
    }
    let journal = cluster.client(&cluster.credentials);
    cluster.leader_after_head(&journal, stream).await;
    // Every keeper refuses the damaged object; none serves wrong bytes.
    let result = timeout(WAIT, async {
        loop {
            match journal.read(stream, Lsn(8), 10, Duration::ZERO).await {
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(50)).await
                }
                result => return result,
            }
        }
    })
    .await
    .expect("the read settled");
    assert_eq!(result, Err(JournalError::Corrupted));
    cluster.stop_all().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn recovery_from_one_survivor_restores_the_longer_object_store_history() {
    let store = tempfile::tempdir().unwrap();
    let mut cluster = Cluster::start_offloaded(&offload_config(store.path())).await;
    let journal = cluster.client(&cluster.credentials);
    let [a, b, c, _] = cluster.ids;
    let stream = StreamId(44);
    journal.create(stream, [a, b, c], 1 << 24).await.unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap()
        .fence;
    append_range(&journal, stream, fence, 1, 20).await;
    flushed(&journal, stream, 20).await;
    let survivor = cluster.group(a, stream).await;
    timeout(WAIT, async {
        while survivor.state.head() != Ok(Lsn(20)) {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap();
    drop(survivor);
    super::recovery::remember_peers(&cluster, a, [b, c]).await;
    // The survivor falls behind: b and c commit and offload 21..=50.
    cluster.running.remove(&a).unwrap().stop().await;
    append_range(&journal, stream, fence, 21, 50).await;
    flushed(&journal, stream, 50).await;
    for lost in [b, c] {
        cluster.running.remove(&lost).unwrap().stop().await;
    }
    let fence_proofs = [b, c]
        .into_iter()
        .map(|lost| cluster.configs[&lost].fence_recovery(lost).unwrap())
        .collect();
    let report = cluster.configs[&a]
        .recover_stream(
            stream,
            Recovery {
                acknowledge_data_loss: true,
                lost: Some([b, c]),
                fence_proofs,
                ..Recovery::default()
            },
        )
        .await
        .unwrap();
    assert!(report.written);
    let offload = report
        .offload
        .clone()
        .expect("the report names the loss point");
    assert_eq!(offload.survivor_head, Lsn(20));
    assert_eq!(offload.store_end, Some(Lsn(50)));
    assert_eq!(offload.kept_through, Lsn(50));
    assert_eq!(offload.floor, Lsn(1));
    assert!(offload.restored);
    assert_eq!(offload.lineage, 1);
    assert!(
        report.to_string().contains("records 1..=50 are kept"),
        "{report}"
    );
    assert_eq!(report.epoch, Epoch(2));

    cluster.restart(a).await;
    let journal = cluster.client(&cluster.credentials);
    timeout(Duration::from_secs(30), async {
        while journal.head(stream).await != Ok(Lsn(50)) {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("the recovered stream serves the restored head");
    check(&read_all(&journal, stream, 1, 50).await, 1, 50);
    assert_eq!(
        journal.seal(stream, Epoch(2), Uuid::from_u128(99)).await,
        Err(JournalError::Recovered { head: Lsn(50) })
    );
    assert_eq!(journal.acknowledge_recovery(stream).await, Ok(Lsn(50)));
    let fence = journal
        .seal(stream, Epoch(2), Uuid::from_u128(100))
        .await
        .unwrap()
        .fence;
    append_range(&journal, stream, fence, 51, 60).await;
    let status = flushed(&journal, stream, 60).await;
    assert_eq!(status.lineage, 1);
    assert_eq!(status.lineages, vec![(0, Lsn(1)), (1, Lsn(51))]);
    check(&read_all(&journal, stream, 1, 60).await, 1, 60);
    cluster.stop_all().await;
}

/// An operator configuration file that names the offload store.
fn operator_file(cluster: &Cluster, store: &std::path::Path, dir: &std::path::Path) -> String {
    let tls = &cluster.credentials;
    let config = serde_json::json!({
        "tls": {
            "certificate": tls.certificate,
            "private_key": tls.private_key,
            "ca": tls.ca,
        },
        "keepers": cluster.keepers,
        "catalog": cluster.catalog,
        "offload": { "url": format!("file://{}", store.display()) },
    });
    let path = dir.join("operator.json");
    std::fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
    path.to_str().unwrap().to_owned()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn export_import_round_trips_and_a_stream_restores_with_no_survivor() {
    let store = tempfile::tempdir().unwrap();
    let mut config = offload_config(store.path());
    config.retain_local_bytes = Some(1000);
    let mut cluster = Cluster::start_offloaded(&config).await;
    let journal = cluster.client(&cluster.credentials);
    let [a, b, c, d] = cluster.ids;
    let source = StreamId(45);
    journal.create(source, [a, b, c], 1 << 24).await.unwrap();
    let fence = journal
        .seal(source, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap()
        .fence;
    append_range(&journal, source, fence, 1, 40).await;
    journal.trim(source, fence, Lsn(5)).await.unwrap();
    let work = tempfile::tempdir().unwrap();
    let operator = operator_file(&cluster, store.path(), work.path());
    let export = work.path().join("export");
    let source_id = Uuid::from_u128(source.0).to_string();
    let exported = super::operator::admin(&[
        "export-stream",
        "--config",
        &operator,
        "--stream",
        &source_id,
        "--to",
        export.to_str().unwrap(),
    ])
    .await
    .unwrap();
    assert!(exported.ok);
    assert_eq!(exported.report["floor"], 6);
    assert_eq!(exported.report["head"], 40);

    // Import into a new stream: the history is served from the store and
    // writers continue above the exported epoch.
    let imported = StreamId(46);
    let imported_id = Uuid::from_u128(imported.0).to_string();
    let voters = format!("{b},{c},{d}");
    let outcome = super::operator::admin(&[
        "import-stream",
        "--config",
        &operator,
        "--from",
        export.to_str().unwrap(),
        "--stream",
        &imported_id,
        "--quota-bytes",
        "16777216",
        "--voters",
        &voters,
    ])
    .await
    .unwrap();
    assert!(outcome.ok, "{:?}", outcome.report);
    assert_eq!(journal.head(imported).await, Ok(Lsn(40)));
    assert_eq!(
        journal.read(imported, Lsn(2), 10, Duration::ZERO).await,
        Err(JournalError::Trimmed { floor: Lsn(6) })
    );
    check(&read_all(&journal, imported, 6, 40).await, 6, 40);
    let sealed = journal.seal(imported, Epoch(0), Uuid::from_u128(98)).await;
    assert_eq!(sealed, Err(JournalError::Fenced { current: Epoch(1) }));
    let fence2 = journal
        .seal(imported, Epoch(1), Uuid::from_u128(98))
        .await
        .unwrap();
    assert_eq!(fence2.head, Lsn(40));
    append_range(&journal, imported, fence2.fence, 41, 45).await;
    flushed(&journal, imported, 45).await;
    check(&read_all(&journal, imported, 6, 45).await, 6, 45);

    // Every voter of the source is lost; restore it from the store alone.
    append_range(&journal, source, fence, 41, 50).await;
    flushed(&journal, source, 50).await;
    for voter in [a, b, c] {
        cluster.running.remove(&voter).unwrap().stop().await;
    }
    let restored = StreamId(47);
    let restored_id = Uuid::from_u128(restored.0).to_string();
    cluster.restart(b).await;
    cluster.restart(c).await;
    let refused = super::operator::admin(&[
        "restore-stream",
        "--config",
        &operator,
        "--from-stream",
        &source_id,
        "--stream",
        &restored_id,
        "--quota-bytes",
        "16777216",
        "--voters",
        &voters,
    ])
    .await
    .err()
    .expect("refused without the acknowledgement");
    assert!(
        refused.to_string().contains("--acknowledge-data-loss"),
        "{refused}"
    );
    let outcome = super::operator::admin(&[
        "restore-stream",
        "--config",
        &operator,
        "--from-stream",
        &source_id,
        "--stream",
        &restored_id,
        "--quota-bytes",
        "16777216",
        "--voters",
        &voters,
        "--floor",
        "6",
        "--acknowledge-data-loss",
    ])
    .await
    .unwrap();
    assert!(outcome.ok, "{:?}", outcome.report);
    // The loss point is the end of the store's run: everything uploaded.
    assert_eq!(outcome.report["head"], 50);
    assert_eq!(outcome.report["kept"], "records 6..=50");
    let journal = cluster.client(&cluster.credentials);
    check(&read_all(&journal, restored, 6, 50).await, 6, 50);
    cluster.stop_all().await;
}

/// A MinIO server on loopback with its own port and data directory, from
/// `LOGKEEPER_MINIO` or the co-design machine's install. `None` skips.
struct Minio {
    child: std::process::Child,
    port: u16,
    _dir: tempfile::TempDir,
}

impl Minio {
    fn start(bucket: &str) -> Option<Self> {
        let binary = std::env::var_os("LOGKEEPER_MINIO")
            .map(std::path::PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    std::path::PathBuf::from(home)
                        .join(".local/share/mise/installs/go/1.26.8/bin/minio")
                })
            })
            .filter(|path| path.exists())?;
        let dir = tempfile::tempdir().unwrap();
        // A directory in the data root is a bucket on a fresh single drive.
        std::fs::create_dir_all(dir.path().join("data").join(bucket)).unwrap();
        let port = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let console = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let child = std::process::Command::new(binary)
            .arg("server")
            .arg(dir.path().join("data"))
            .args(["--address", &format!("127.0.0.1:{port}")])
            .args(["--console-address", &format!("127.0.0.1:{console}")])
            .env("MINIO_ROOT_USER", "logkeeper")
            .env("MINIO_ROOT_PASSWORD", "logkeeper-secret")
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .ok()?;
        Some(Self {
            child,
            port,
            _dir: dir,
        })
    }

    fn config(&self, bucket: &str) -> OffloadConfig {
        serde_json::from_value(serde_json::json!({
            "url": format!("s3://{bucket}/cluster"),
            "endpoint": format!("http://127.0.0.1:{}", self.port),
            "allow_http": true,
            "access_key_id": "logkeeper",
            "secret_access_key": "logkeeper-secret",
            "batch_bytes": 2048,
            "batch_interval_ms": 200,
        }))
        .unwrap()
    }
}

impl Drop for Minio {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn offload_to_minio_is_idempotent_and_serves_reads_below_the_local_floor() {
    let bucket = "logkeeper";
    let Some(minio) = Minio::start(bucket) else {
        eprintln!("skipped: no MinIO binary (set LOGKEEPER_MINIO)");
        return;
    };
    let mut config = minio.config(bucket);
    let store = Store::open(&config).unwrap();
    // Wait for MinIO, and check its conditional put: a key is written once.
    let stream = StreamId(48);
    let records = (1..=3)
        .map(|lsn| Record {
            lsn: Lsn(lsn),
            timed: false,
            bytes: payload(lsn),
        })
        .collect::<Vec<_>>();
    let created = timeout(WAIT, async {
        loop {
            match store.upload(StreamId(99), 0, &records, Vec::new()).await {
                Ok((created, _)) => return created,
                Err(_) => tokio::time::sleep(Duration::from_millis(100)).await,
            }
        }
    })
    .await
    .expect("MinIO answered");
    assert!(created);
    assert!(
        !store
            .upload(StreamId(99), 0, &records, Vec::new())
            .await
            .unwrap()
            .0
    );

    config.retain_local_bytes = Some(500);
    let mut cluster = Cluster::start_offloaded(&config).await;
    let journal = cluster.client(&cluster.credentials);
    let [a, b, c, _] = cluster.ids;
    journal.create(stream, [a, b, c], 1 << 24).await.unwrap();
    let fence = journal
        .seal(stream, Epoch(0), Uuid::from_u128(99))
        .await
        .unwrap()
        .fence;
    append_range(&journal, stream, fence, 1, 40).await;
    flushed(&journal, stream, 40).await;
    timeout(WAIT, async {
        while journal
            .offload_status(stream, false)
            .await
            .unwrap()
            .local_floor
            <= Lsn(20)
        {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    })
    .await
    .expect("retention dropped offloaded records");
    check(&read_all(&journal, stream, 1, 40).await, 1, 40);
    let plan = store.plan(stream, &[(0, Lsn(1))], Lsn(1)).await.unwrap();
    assert_eq!(plan.run, Some((Lsn(1), Lsn(40))));
    cluster.stop_all().await;
}
