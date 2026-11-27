//! Measures consensus keepers hosting many streams.
//!
//! Starts a local cluster of three voters and a catalog keeper in one process,
//! creates `--streams` streams, and keeps `--active` of them writing
//! `--batch`-record batches for `--seconds`. Prints one JSON line with commits
//! per second, batch latency percentiles, process CPU time, peak resident
//! memory and the bytes the keepers hold on disk, so runs with more idle
//! streams show the per-stream cost.
//!
//! ```sh
//! cargo run --release --features consensus-testing --example consensus-streams -- \
//!     --streams 100 --active 8 --seconds 10
//! ```

use std::time::{Duration, Instant};

use bytes::Bytes;
use journal_contract::{Epoch, Journal as _, Lsn, StreamId};
use logkeeper::stream::consensus::testing::LocalCluster;

const PRINCIPAL: &str = "urn:logkeeper:client:measure";

struct Args {
    streams: u64,
    active: u64,
    batch: u64,
    record: usize,
    seconds: f64,
    park: Option<u64>,
}

fn args() -> Args {
    let mut args = Args {
        streams: 16,
        active: 4,
        batch: 16,
        record: 256,
        seconds: 10.0,
        park: None,
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

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let args = args();
    let mut cluster = match args.park {
        Some(seconds) => LocalCluster::start_parking(&[PRINCIPAL], seconds).await,
        None => LocalCluster::start(&[PRINCIPAL]).await,
    }
    .unwrap();
    let config = cluster.journal_config(1 << 30, args.record.max(4096));
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    for id in 1..=args.streams {
        journal.create(StreamId(u128::from(id))).await.unwrap();
        journal
            .seal(StreamId(u128::from(id)), Epoch(1))
            .await
            .unwrap();
    }
    // Let idle streams settle, and park when asked, before measuring their
    // steady cost.
    tokio::time::sleep(Duration::from_secs(args.park.map_or(2, |park| park + 35))).await;
    let cpu = cpu_seconds();
    let started = Instant::now();
    let deadline = started + Duration::from_secs_f64(args.seconds);
    let record = Bytes::from(vec![7; args.record]);
    let mut writers = tokio::task::JoinSet::new();
    for id in 1..=args.active {
        let journal = journal.clone();
        let record = record.clone();
        let batch = args.batch;
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
            }
            latencies
        });
    }
    tokio::time::sleep_until(deadline.into()).await;
    let mut latencies = Vec::new();
    while let Some(result) = writers.join_next().await {
        latencies.extend(result.unwrap());
    }
    let elapsed = started.elapsed().as_secs_f64();
    let cpu = cpu_seconds() - cpu;
    latencies.sort();
    let percentile = |p: f64| {
        latencies
            .get(((latencies.len() as f64 - 1.0) * p) as usize)
            .map_or(0.0, |latency| latency.as_secs_f64() * 1e3)
    };
    println!(
        "{{\"streams\": {}, \"active\": {}, \"batch\": {}, \"record\": {}, \"seconds\": {:.2}, \
         \"batches_per_second\": {:.1}, \"records_per_second\": {:.1}, \"p50_ms\": {:.2}, \
         \"p99_ms\": {:.2}, \"cpu_cores\": {:.2}, \"peak_rss_mib\": {:.1}, \
         \"disk_mib\": {:.1}}}",
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
