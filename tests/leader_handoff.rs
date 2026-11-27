//! Write stalls while each keeper in turn stops gracefully and restarts,
//! under constant appends: a stopping keeper hands each stream it leads to
//! a follower, so its writers wait for a transfer, not for a lease and an
//! election. The test prints the worst append stall per restart and fails
//! when one exceeds `MAX_STALL`.
#![cfg(feature = "consensus-testing")]

use std::{
    collections::BTreeMap,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, Instant},
};

use bytes::Bytes;
use journal_contract::{Epoch, Journal as _, JournalError, Lsn, StreamId};
use logkeeper::stream::consensus::{ConsensusJournal, testing::LocalCluster};
use tokio::sync::Mutex;

const PRINCIPAL: &str = "urn:logkeeper:client:leader-handoff";
const STREAMS: u128 = 4;
/// A stall a hand-off avoids: the leader's lease (1.8 s) plus an election.
/// A restart that hands every stream off stalls writes well below it.
const HANDED_OFF: Duration = Duration::from_millis(1200);
/// The longest an append may wait while one keeper restarts, with room for
/// a loaded test host.
const MAX_STALL: Duration = Duration::from_secs(8);
const DEADLINE: Duration = Duration::from_secs(120);

async fn retry<T, F: std::future::Future<Output = Result<T, JournalError>>>(
    call: impl Fn() -> F,
) -> T {
    let started = Instant::now();
    loop {
        match call().await {
            Ok(value) => return value,
            Err(JournalError::Unavailable) if started.elapsed() < DEADLINE => {
                tokio::time::sleep(Duration::from_millis(100)).await
            }
            Err(error) => panic!("setup failed: {error:?}"),
        }
    }
}

fn payload(stream: u128, at: u64) -> Bytes {
    Bytes::from(format!("stream {stream} record {at}").into_bytes())
}

#[derive(Default)]
struct Written {
    acknowledged: u64,
    /// When each append was sent and how long it took to be acknowledged.
    appends: Vec<(Instant, Duration)>,
}

/// Appends one record at a time, retrying the same LSN and bytes after an
/// unknown outcome.
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

/// The longest append in flight at any time during `[from, to]`.
fn stall(written: &Written, from: Instant, to: Instant) -> Duration {
    written
        .appends
        .iter()
        .filter(|(sent, took)| *sent <= to && *sent + *took >= from)
        .map(|(_, took)| *took)
        .max()
        .unwrap_or_default()
}

/// Waits until every writer acknowledged an append sent after `since`.
async fn progressed(written: &BTreeMap<u128, Arc<Mutex<Written>>>, since: Instant) {
    let started = Instant::now();
    for written in written.values() {
        loop {
            if written
                .lock()
                .await
                .appends
                .last()
                .is_some_and(|(sent, _)| *sent >= since)
            {
                break;
            }
            assert!(started.elapsed() < DEADLINE, "writes did not resume");
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn graceful_restarts_hand_leadership_off_under_writes() {
    let mut cluster = LocalCluster::start_replicated_catalog(&[PRINCIPAL])
        .await
        .unwrap();
    let config = cluster.placement_config(1 << 30, 4096);
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    for stream in 1..=STREAMS {
        retry(|| journal.create(StreamId(stream))).await;
        retry(|| journal.seal(StreamId(stream), Epoch(1))).await;
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
    tokio::time::sleep(Duration::from_secs(3)).await;

    let keepers = cluster.keepers().keys().copied().collect::<Vec<_>>();
    let mut steps = Vec::new();
    for round in 0..2 {
        for keeper in &keepers {
            let started = Instant::now();
            cluster.stop(*keeper).await.unwrap();
            let stopped = started.elapsed();
            // Writes must resume while the keeper is down.
            progressed(&written, Instant::now()).await;
            let finished = Instant::now();
            cluster.restart(*keeper).await.unwrap();
            // Let the restarted keeper catch up before the next stops.
            tokio::time::sleep(Duration::from_secs(2)).await;
            progressed(&written, Instant::now()).await;
            let mut worst = Duration::ZERO;
            for written in written.values() {
                worst = worst.max(stall(&*written.lock().await, started, finished));
            }
            steps.push((round, *keeper, stopped, worst));
        }
    }
    stop.store(true, Ordering::Relaxed);
    for writer in writers {
        writer.await.unwrap();
    }

    println!("round keeper                                stop     max write stall");
    for (round, keeper, stopped, worst) in &steps {
        println!(
            "{round:>5} {keeper}  {:>6.2} s  {:>8.3} s",
            stopped.as_secs_f64(),
            worst.as_secs_f64(),
        );
    }
    let stalls = steps.iter().map(|step| step.3).collect::<Vec<_>>();
    let mean = stalls.iter().sum::<Duration>() / stalls.len() as u32;
    let max = stalls.iter().max().copied().unwrap_or_default();
    let handed = stalls.iter().filter(|stall| **stall < HANDED_OFF).count();
    println!(
        "restarts {}  max stall {:.3} s  mean stall {:.3} s  below {:?}: {handed}",
        stalls.len(),
        max.as_secs_f64(),
        mean.as_secs_f64(),
        HANDED_OFF,
    );
    let mut total = 0;
    for (stream, written) in &written {
        let written = written.lock().await;
        total += written.acknowledged;
        let id = StreamId(*stream);
        let mut next = 1;
        while next <= written.acknowledged {
            let page = journal
                .read(id, Lsn(next), 1024, Duration::ZERO)
                .await
                .unwrap();
            assert!(!page.records.is_empty(), "stream {stream} lost {next}");
            for (at, bytes) in page.records {
                assert_eq!(at, Lsn(next));
                assert_eq!(bytes, payload(*stream, next));
                next += 1;
            }
        }
    }
    println!("{total} acknowledged records checked");
    assert!(max <= MAX_STALL, "a restart stalled writes for {max:?}");
    cluster.shutdown().await.unwrap();
}
