//! The rolling-upgrade runbook (docs/runbooks/rolling-upgrade.md) on an
//! in-process cluster under write load.
//!
//! Writers append to several streams the whole time. Each keeper in turn is
//! stopped once its admin listener answers `/safe-to-stop` with 200, then
//! restarted on the same media, and the next keeper waits until this one
//! answers `/ready` with 200. Every acknowledged record must still be there
//! afterwards, and no append may stall for more than `MAX_STALL` during a
//! restart. The test prints the measured stall per restart.
#![cfg(feature = "consensus-testing")]

use std::{
    collections::BTreeMap,
    net::SocketAddr,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, Instant},
};

use bytes::Bytes;
use journal_contract::{Epoch, Journal as _, JournalError, Lsn, StreamId};
use logkeeper::stream::consensus::{ConsensusJournal, testing::LocalCluster};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::TcpStream,
    sync::Mutex,
};

const PRINCIPAL: &str = "urn:logkeeper:client:rolling-upgrade";
const STREAMS: u128 = 4;
/// The longest an append may wait while one keeper restarts: a leader that
/// could not hand off leaves its lease (1.8 s) plus an election (up to
/// 0.9 s), with room for a loaded test host.
const MAX_STALL: Duration = Duration::from_secs(8);
/// How long the runbook waits for a probe before aborting.
const PROBE_DEADLINE: Duration = Duration::from_secs(120);

/// The HTTP status of `GET path` on a keeper's admin listener.
async fn probe(admin: SocketAddr, path: &str) -> Option<u16> {
    let mut socket = tokio::time::timeout(Duration::from_secs(2), TcpStream::connect(admin))
        .await
        .ok()?
        .ok()?;
    socket
        .write_all(
            format!("GET {path} HTTP/1.1\r\nHost: keeper\r\nConnection: close\r\n\r\n").as_bytes(),
        )
        .await
        .ok()?;
    let mut response = Vec::new();
    tokio::time::timeout(Duration::from_secs(5), socket.read_to_end(&mut response))
        .await
        .ok()?
        .ok()?;
    std::str::from_utf8(&response)
        .ok()?
        .split(' ')
        .nth(1)?
        .parse()
        .ok()
}

/// Waits until `path` answers 200, as the runbook's `until probe ...` loops.
async fn wait_for(admin: SocketAddr, path: &str) -> Duration {
    let started = Instant::now();
    while probe(admin, path).await != Some(200) {
        assert!(
            started.elapsed() < PROBE_DEADLINE,
            "{path} on {admin} did not answer 200 within {PROBE_DEADLINE:?}: abort the rollout"
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    started.elapsed()
}

/// Retries a setup call while the journal answers `Unavailable`.
async fn retry<T, F: std::future::Future<Output = Result<T, JournalError>>>(
    call: impl Fn() -> F,
) -> T {
    let started = Instant::now();
    loop {
        match call().await {
            Ok(value) => return value,
            Err(JournalError::Unavailable) if started.elapsed() < PROBE_DEADLINE => {
                tokio::time::sleep(Duration::from_millis(100)).await
            }
            Err(error) => panic!("setup failed: {error:?}"),
        }
    }
}

fn payload(stream: u128, at: u64) -> Bytes {
    Bytes::from(format!("stream {stream} record {at}").into_bytes())
}

/// One writer's acknowledged records and the latency of every append.
#[derive(Default)]
struct Written {
    acknowledged: u64,
    /// (when the append was sent, how long it took to be acknowledged)
    appends: Vec<(Instant, Duration)>,
}

/// Appends one record at a time, retrying the same LSN and bytes after an
/// unknown outcome, as the README asks of a writer.
async fn write(
    journal: ConsensusJournal,
    stream: u128,
    stop: Arc<AtomicBool>,
    written: Arc<Mutex<Written>>,
) {
    let id = StreamId(stream);
    let mut at = 1;
    while !stop.load(Ordering::Relaxed) {
        let sent = Instant::now();
        loop {
            match journal
                .append_batch(id, Epoch(1), vec![(Lsn(at), payload(stream, at))])
                .await
            {
                Ok(_) => break,
                Err(JournalError::Unavailable) => {
                    tokio::time::sleep(Duration::from_millis(10)).await
                }
                Err(error) => panic!("append {at} to stream {stream} failed: {error:?}"),
            }
        }
        let mut written = written.lock().await;
        written.acknowledged = at;
        written.appends.push((sent, sent.elapsed()));
        drop(written);
        at += 1;
        tokio::time::sleep(Duration::from_millis(2)).await;
    }
}

/// The longest append that was in flight at any time during `[from, to]`.
fn stall(written: &Written, from: Instant, to: Instant) -> Duration {
    written
        .appends
        .iter()
        .filter(|(sent, took)| *sent <= to && *sent + *took >= from)
        .map(|(_, took)| *took)
        .max()
        .unwrap_or_default()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn rolling_restart_under_load_keeps_every_acknowledged_write() {
    let mut cluster = LocalCluster::start_replicated_catalog(&[PRINCIPAL])
        .await
        .unwrap();
    let config = cluster.placement_config(1 << 30, 4096);
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    // First bring-up: every keeper ready before the first stream.
    let keepers = cluster.keepers().keys().copied().collect::<Vec<_>>();
    for keeper in &keepers {
        wait_for(cluster.admin(*keeper), "/ready").await;
    }
    for stream in 1..=STREAMS {
        // The replicated catalog refuses claims until its seed commits.
        retry(|| journal.create(StreamId(stream))).await;
        retry(|| journal.seal(StreamId(stream), Epoch(1))).await;
    }
    for keeper in &keepers {
        wait_for(cluster.admin(*keeper), "/ready").await;
    }

    let stop = Arc::new(AtomicBool::new(false));
    let written = (1..=STREAMS)
        .map(|stream| (stream, Arc::new(Mutex::new(Written::default()))))
        .collect::<BTreeMap<_, _>>();
    let writers = written
        .iter()
        .map(|(stream, written)| {
            tokio::spawn(write(
                journal.clone(),
                *stream,
                stop.clone(),
                written.clone(),
            ))
        })
        .collect::<Vec<_>>();
    // Steady load before the first restart.
    tokio::time::sleep(Duration::from_secs(3)).await;

    let mut steps = Vec::new();
    for keeper in &keepers {
        let admin = cluster.admin(*keeper);
        let waited = wait_for(admin, "/safe-to-stop").await;
        let started = Instant::now();
        // SIGTERM in production: leaders hand off, then the keeper stops.
        cluster.stop(*keeper).await.unwrap();
        let stopped = started.elapsed();
        // The upgrade itself: the same binary restarts on the same media.
        cluster.restart(*keeper).await.unwrap();
        let ready = wait_for(admin, "/ready").await;
        let finished = Instant::now();
        // Let every writer complete an append after the step.
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut worst = Duration::ZERO;
        for written in written.values() {
            worst = worst.max(stall(&*written.lock().await, started, finished));
        }
        steps.push((*keeper, waited, stopped, ready, worst));
    }

    stop.store(true, Ordering::Relaxed);
    for writer in writers {
        writer.await.unwrap();
    }

    println!(
        "keeper                                safe-to-stop wait  stop    ready   max write stall"
    );
    for (keeper, waited, stopped, ready, worst) in &steps {
        println!(
            "{keeper}  {:>8.2} s  {:>6.2} s  {:>6.2} s  {:>8.3} s",
            waited.as_secs_f64(),
            stopped.as_secs_f64(),
            ready.as_secs_f64(),
            worst.as_secs_f64(),
        );
    }
    let mut total = 0;
    for (stream, written) in &written {
        let written = written.lock().await;
        total += written.acknowledged;
        let id = StreamId(*stream);
        let head = journal.head(id).await.unwrap();
        assert!(
            head.0 >= written.acknowledged,
            "stream {stream} head {head:?} is below its acknowledged {}",
            written.acknowledged
        );
        let mut next = 1;
        while next <= written.acknowledged {
            let page = journal
                .read(id, Lsn(next), 1024, Duration::ZERO)
                .await
                .unwrap();
            assert!(
                !page.records.is_empty(),
                "stream {stream} lost records from {next}"
            );
            for (at, bytes) in page.records {
                assert_eq!(at, Lsn(next));
                assert_eq!(
                    bytes,
                    payload(*stream, next),
                    "stream {stream} record {next}"
                );
                next += 1;
            }
        }
    }
    println!("{total} acknowledged records checked across {STREAMS} streams");
    for (keeper, _, _, _, worst) in &steps {
        assert!(
            *worst <= MAX_STALL,
            "restarting {keeper} stalled writes for {worst:?}, above {MAX_STALL:?}"
        );
    }
    cluster.shutdown().await.unwrap();
}
