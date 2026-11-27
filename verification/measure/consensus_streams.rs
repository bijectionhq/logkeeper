//! Measures consensus keepers hosting many streams.
//!
//! Starts a local cluster of three voters and a catalog keeper in one process,
//! creates `--streams` streams, and keeps `--active` of them writing
//! `--batch`-record batches for `--seconds`. Prints one JSON line with commits
//! per second, batch latency percentiles, process CPU time, peak resident
//! memory and the bytes the keepers hold on disk, so runs with more idle
//! streams show the per-stream cost. `--sync-mode fsync` measures the
//! keepers with plain `fsync` instead of the default `full`.
//! `LOGKEEPER_ASYNC_APPEND=0` measures leaders that sync their own append
//! before replicating it, and `LOGKEEPER_PEER_DELAY_MS` delays every
//! replication request to emulate a slower link.
//!
//! ```sh
//! cargo run --release --features consensus-testing --example consensus-streams -- \
//!     --streams 100 --active 8 --seconds 10
//! ```
//!
//! `--cold N` makes the active writers trim each batch once written, and
//! after every N batches across them writes one record to the next idle
//! stream, which keeps it: the disk then holds mostly dead segments that
//! cold records pin unless they are compacted.
//!
//! `--offload URL` turns on continuous offload to `URL` (`file:///dir`, or
//! `s3://bucket/prefix` with `LOGKEEPER_OFFLOAD_ENDPOINT`, `AWS_ACCESS_KEY_ID`
//! and `AWS_SECRET_ACCESS_KEY` for MinIO) with `--offload-interval-ms`
//! batching, and reports the largest offload lag seen during the run and how
//! long the leaders took to upload everything once the writers stopped.
//!
//! `--fill N` first writes N 64-byte records to stream 1 in 256-record
//! batches and reports the process's resident memory with that stream open
//! and, with `--park-after`, once it parked.

use std::time::{Duration, Instant};

use bytes::Bytes;
use journal_contract::{Epoch, Journal as _, Lsn, StreamId};
use logkeeper::stream::consensus::{SyncMode, testing::LocalCluster};

const PRINCIPAL: &str = "urn:logkeeper:client:measure";

struct Args {
    streams: u64,
    active: u64,
    batch: u64,
    record: usize,
    seconds: f64,
    park: Option<u64>,
    sync_mode: SyncMode,
    fill: u64,
    cold: u64,
    offload: Option<String>,
    offload_interval_ms: u64,
}

fn args() -> Args {
    let mut args = Args {
        streams: 16,
        active: 4,
        batch: 16,
        record: 256,
        seconds: 10.0,
        park: None,
        sync_mode: SyncMode::Full,
        fill: 0,
        cold: 0,
        offload: None,
        offload_interval_ms: 1000,
    };
    let mut input = std::env::args().skip(1);
    while let Some(flag) = input.next() {
        let value = input
            .next()
            .unwrap_or_else(|| panic!("{flag} needs a value"));
        match flag.as_str() {
            "--streams" => args.streams = value.parse().unwrap(),
            "--active" => args.active = value.parse().unwrap(),
            "--batch" => args.batch = value.parse().unwrap(),
            "--record" => args.record = value.parse().unwrap(),
            "--seconds" => args.seconds = value.parse().unwrap(),
            "--park-after" => args.park = Some(value.parse().unwrap()),
            "--sync-mode" => {
                args.sync_mode = serde_json::from_value(value.into()).unwrap();
            }
            "--fill" => args.fill = value.parse().unwrap(),
            "--cold" => args.cold = value.parse().unwrap(),
            "--offload" => args.offload = Some(value),
            "--offload-interval-ms" => args.offload_interval_ms = value.parse().unwrap(),
            other => panic!("unknown flag {other}"),
        }
    }
    assert!(args.active <= args.streams && args.batch > 0);
    args
}

fn usage() -> libc::rusage {
    // SAFETY: getrusage writes into the zeroed struct it is given.
    let mut usage = unsafe { std::mem::zeroed::<libc::rusage>() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
    usage
}

/// Peak resident memory of the whole process, in MiB.
fn peak_rss_mib() -> f64 {
    let peak = usage().ru_maxrss as f64;
    // macOS reports bytes, Linux KiB.
    if cfg!(target_vendor = "apple") {
        peak / (1024.0 * 1024.0)
    } else {
        peak / 1024.0
    }
}

/// Bytes of every regular file under `path`.
fn disk_bytes(path: &std::path::Path) -> u64 {
    std::fs::read_dir(path).map_or(0, |entries| {
        entries
            .flatten()
            .map(|entry| match entry.file_type() {
                Ok(kind) if kind.is_dir() => disk_bytes(&entry.path()),
                Ok(_) => entry.metadata().map_or(0, |metadata| metadata.len()),
                Err(_) => 0,
            })
            .sum()
    })
}

fn cpu_seconds() -> f64 {
    let usage = usage();
    let seconds = |time: libc::timeval| time.tv_sec as f64 + time.tv_usec as f64 / 1e6;
    seconds(usage.ru_utime) + seconds(usage.ru_stime)
}

/// Counts live heap bytes, which the allocator may not return to the system.
struct Counting;

static HEAP: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

// SAFETY: forwards every call to the system allocator unchanged.
unsafe impl std::alloc::GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        HEAP.fetch_add(layout.size(), std::sync::atomic::Ordering::Relaxed);
        unsafe { std::alloc::System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        HEAP.fetch_sub(layout.size(), std::sync::atomic::Ordering::Relaxed);
        unsafe { std::alloc::System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn heap_mib() -> f64 {
    HEAP.load(std::sync::atomic::Ordering::Relaxed) as f64 / (1024.0 * 1024.0)
}

/// Resident memory of this process in MiB.
fn resident_mib() -> f64 {
    let output = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .unwrap();
    String::from_utf8_lossy(&output.stdout)
        .trim()
        .parse::<f64>()
        .unwrap()
        / 1024.0
}

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let args = args();
    // The local cluster's keepers take the process's mode.
    args.sync_mode.install();
    let mut cluster = match args.park {
        Some(seconds) => LocalCluster::start_parking(&[PRINCIPAL], seconds).await,
        None => LocalCluster::start(&[PRINCIPAL]).await,
    }
    .unwrap();
    if let Some(url) = &args.offload {
        let offload = serde_json::from_value(serde_json::json!({
            "url": url,
            "endpoint": std::env::var("LOGKEEPER_OFFLOAD_ENDPOINT").ok(),
            "allow_http": true,
            "batch_interval_ms": args.offload_interval_ms,
            "max_lag_bytes": 1u64 << 40,
        }))
        .unwrap();
        cluster.enable_offload(PRINCIPAL, offload).await.unwrap();
    }
    let config = cluster.journal_config(1 << 30, args.record.max(4096));
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    for id in 1..=args.streams {
        journal.create(StreamId(u128::from(id))).await.unwrap();
        journal
            .seal(StreamId(u128::from(id)), Epoch(1))
            .await
            .unwrap();
    }
    let mut memory = String::new();
    if args.fill > 0 {
        let record = Bytes::from(vec![5; 64]);
        let mut next = 1u64;
        while next <= args.fill {
            let batch = (next..(next + 256).min(args.fill + 1))
                .map(|at| (Lsn(at), record.clone()))
                .collect::<Vec<_>>();
            next += batch.len() as u64;
            journal
                .append_batch(StreamId(1), Epoch(1), batch)
                .await
                .unwrap();
        }
        tokio::time::sleep(Duration::from_secs(1)).await;
        memory = format!(
            ", \"filled\": {}, \"heap_open_mib\": {:.1}, \"rss_open_mib\": {:.1}",
            args.fill,
            heap_mib(),
            resident_mib()
        );
    }
    // Let idle streams settle, and park when asked, before measuring their
    // steady cost.
    // A filled stream changed its log after the first leader pass, so it
    // parks one 30 s pass later than the others.
    let settle = args
        .park
        .map_or(2, |park| park + 35 + if args.fill > 0 { 30 } else { 0 });
    tokio::time::sleep(Duration::from_secs(settle)).await;
    if args.fill > 0 {
        memory += &format!(
            ", \"heap_settled_mib\": {:.1}, \"rss_settled_mib\": {:.1}",
            heap_mib(),
            resident_mib()
        );
    }
    let cpu = cpu_seconds();
    let started = Instant::now();
    let deadline = started + Duration::from_secs_f64(args.seconds);
    let record = Bytes::from(vec![7; args.record]);
    let mut writers = tokio::task::JoinSet::new();
    let written = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0));
    let idle = (args.active + 1..=args.streams).collect::<Vec<_>>();
    let cold_next = std::sync::Arc::new(parking_lot::Mutex::new(
        idle.iter()
            .map(|id| (*id, 1u64))
            .collect::<std::collections::BTreeMap<_, _>>(),
    ));
    for id in 1..=args.active {
        let journal = journal.clone();
        let record = record.clone();
        let batch = args.batch;
        let (cold, written, cold_next, idle) =
            (args.cold, written.clone(), cold_next.clone(), idle.clone());
        writers.spawn(async move {
            let stream = StreamId(u128::from(id));
            let mut next = 1u64;
            let mut latencies = Vec::new();
            while Instant::now() < deadline {
                let group = (next..next + batch)
                    .map(|at| (Lsn(at), record.clone()))
                    .collect::<Vec<_>>();
                let sent = Instant::now();
                journal.append_batch(stream, Epoch(1), group).await.unwrap();
                latencies.push(sent.elapsed());
                next += batch;
                if cold > 0 {
                    journal.trim(stream, Epoch(1), Lsn(next - 1)).await.unwrap();
                    let count = written.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                    if count % cold == 0 && !idle.is_empty() {
                        let target = idle[(count / cold) as usize % idle.len()];
                        let at = {
                            let mut next = cold_next.lock();
                            let at = next[&target];
                            next.insert(target, at + 1);
                            at
                        };
                        journal
                            .append(
                                StreamId(u128::from(target)),
                                Epoch(1),
                                Lsn(at),
                                record.clone(),
                            )
                            .await
                            .unwrap();
                    }
                }
            }
            latencies
        });
    }
    let lag = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0));
    if args.offload.is_some() {
        let (journal, lag, active) = (journal.clone(), lag.clone(), args.active);
        tokio::spawn(async move {
            while Instant::now() < deadline {
                for id in 1..=active {
                    if let Ok(status) = journal
                        .client()
                        .offload_status(StreamId(u128::from(id)), false)
                        .await
                    {
                        let behind = status.head.0.saturating_sub(status.offloaded_through.0);
                        lag.fetch_max(behind, std::sync::atomic::Ordering::Relaxed);
                    }
                }
                tokio::time::sleep(Duration::from_millis(250)).await;
            }
        });
    }
    tokio::time::sleep_until(deadline.into()).await;
    let mut latencies = Vec::new();
    while let Some(result) = writers.join_next().await {
        latencies.extend(result.unwrap());
    }
    let elapsed = started.elapsed().as_secs_f64();
    let cpu = cpu_seconds() - cpu;
    if args.offload.is_some() {
        let stopped = Instant::now();
        for id in 1..=args.active {
            loop {
                let status = journal
                    .client()
                    .offload_status(StreamId(u128::from(id)), false)
                    .await;
                if status.is_ok_and(|status| status.offloaded_through >= status.head) {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
        }
        memory += &format!(
            ", \"offload_max_lag_records\": {}, \"offload_drain_ms\": {}",
            lag.load(std::sync::atomic::Ordering::Relaxed),
            stopped.elapsed().as_millis()
        );
    }
    latencies.sort();
    let percentile = |p: f64| {
        latencies
            .get(((latencies.len() as f64 - 1.0) * p) as usize)
            .map_or(0.0, |latency| latency.as_secs_f64() * 1e3)
    };
    println!(
        "{{\"sync_mode\": \"{}\", \"streams\": {}, \"active\": {}, \"batch\": {}, \
         \"record\": {}, \"seconds\": {:.2}, \
         \"batches_per_second\": {:.1}, \"records_per_second\": {:.1}, \"p50_ms\": {:.2}, \
         \"p99_ms\": {:.2}, \"cpu_cores\": {:.2}, \"peak_rss_mib\": {:.1}, \
         \"disk_mib\": {:.1}{memory}}}",
        serde_json::to_value(args.sync_mode)
            .unwrap()
            .as_str()
            .unwrap(),
        args.streams,
        args.active,
        args.batch,
        args.record,
        elapsed,
        latencies.len() as f64 / elapsed,
        latencies.len() as f64 * args.batch as f64 / elapsed,
        percentile(0.5),
        percentile(0.99),
        cpu / elapsed,
        peak_rss_mib(),
        disk_bytes(cluster.directory()) as f64 / (1024.0 * 1024.0),
    );
    cluster.shutdown().await.unwrap();
}
