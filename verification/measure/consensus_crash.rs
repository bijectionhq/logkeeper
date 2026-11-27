//! Kills consensus keeper processes at random points during heavy writes and
//! checks that no acknowledged record is lost.
//!
//! Provisions a local cluster of three voters and a catalog keeper, then runs
//! each keeper as its own `logkeeper keeper` process. `--writers` streams take
//! `--batch`-record batches as fast as the keepers acknowledge them. Each of
//! `--rounds` rounds waits a random time, sends SIGKILL to a random set of
//! keepers (one voter, two voters, every voter, or every keeper), restarts
//! them after a random pause, and then reads every stream back from its first
//! record: each acknowledged record must be there, in order, with its exact
//! payload. Prints one JSON line per round and a summary.
//!
//! SIGKILL loses what a process had not yet written to the kernel, not what
//! the kernel had not yet written to the drive, so this run checks that a
//! keeper acknowledges only written records and recovers torn tails; it does
//! not prove the drive flush that power loss needs.
//!
//! ```sh
//! cargo build --release --features stream --bin logkeeper
//! cargo run --release --features consensus-testing --example consensus-crash -- \
//!     --logkeeper target/release/logkeeper --rounds 50
//! ```

use std::{
    path::PathBuf,
    process::{Child, Command, Stdio},
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::{Duration, Instant},
};

use bytes::Bytes;
use journal_contract::{Epoch, Journal as _, JournalError, Lsn, StreamId};
use logkeeper::stream::consensus::{ConsensusJournal, SyncMode, testing::LocalCluster};
use uuid::Uuid;

const PRINCIPAL: &str = "urn:logkeeper:client:crash";
/// Checked records a stream holds before the run trims it, well below the
/// 262,144-record retention ceiling.
const TRIM_AFTER: u64 = 150_000;
/// Checked records a trim keeps, so later rounds still reread them.
const TRIM_KEEPS: u64 = 50_000;

struct Args {
    logkeeper: PathBuf,
    rounds: u64,
    writers: u64,
    batch: u64,
    record: usize,
    seed: u64,
    sync_mode: SyncMode,
}

fn args() -> Args {
    let mut args = Args {
        logkeeper: PathBuf::from("target/release/logkeeper"),
        rounds: 20,
        writers: 4,
        batch: 16,
        record: 256,
        seed: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64,
        sync_mode: SyncMode::Full,
    };
    let mut input = std::env::args().skip(1);
    while let Some(flag) = input.next() {
        let value = input
            .next()
            .unwrap_or_else(|| panic!("{flag} needs a value"));
        match flag.as_str() {
            "--logkeeper" => args.logkeeper = value.into(),
            "--rounds" => args.rounds = value.parse().unwrap(),
            "--writers" => args.writers = value.parse().unwrap(),
            "--batch" => args.batch = value.parse().unwrap(),
            "--record" => args.record = value.parse().unwrap(),
            "--seed" => args.seed = value.parse().unwrap(),
            "--sync-mode" => args.sync_mode = serde_json::from_value(value.into()).unwrap(),
            other => panic!("unknown flag {other}"),
        }
    }
    assert!(args.writers > 0 && args.batch > 0 && args.record >= 16);
    args
}

/// xorshift64*: enough to pick kill points reproducibly from a seed.
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn millis(&mut self, low: u64, high: u64) -> Duration {
        Duration::from_millis(low + self.next() % (high - low + 1))
    }
}

/// The payload of record `at` on `stream`: its coordinates, then filler.
fn payload(stream: u64, at: u64, size: usize) -> Bytes {
    let mut bytes = Vec::with_capacity(size);
    bytes.extend_from_slice(&stream.to_be_bytes());
    bytes.extend_from_slice(&at.to_be_bytes());
    bytes.resize(size, (stream ^ at) as u8);
    Bytes::from(bytes)
}

struct Keepers {
    binary: PathBuf,
    configs: Vec<(Uuid, PathBuf)>,
    logs: PathBuf,
    running: Vec<Option<Child>>,
}

impl Keepers {
    fn start(&mut self, index: usize) {
        let (keeper, config) = &self.configs[index];
        let log = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(self.logs.join(format!("keeper-{keeper}.log")))
            .unwrap();
        let child = Command::new(&self.binary)
            .args(["keeper", "--config"])
            .arg(config)
            .stdin(Stdio::null())
            .stdout(log.try_clone().unwrap())
            .stderr(log)
            .spawn()
            .unwrap();
        self.running[index] = Some(child);
    }

    fn kill(&mut self, index: usize) {
        let mut child = self.running[index].take().expect("keeper is running");
        child.kill().unwrap();
        child.wait().unwrap();
    }

    /// Fails when a keeper exited on its own, which a kill never causes.
    fn check(&mut self) {
        for (index, child) in self.running.iter_mut().enumerate() {
            if let Some(status) = child.as_mut().and_then(|child| child.try_wait().unwrap()) {
                panic!(
                    "keeper {} exited by itself with {status}; see {}",
                    self.configs[index].0,
                    self.logs.display()
                );
            }
        }
    }
}

impl Drop for Keepers {
    fn drop(&mut self) {
        for child in self.running.iter_mut().flatten() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

/// Appends batches to `stream` until `stop`, retrying a batch until it is
/// acknowledged, and publishes the highest acknowledged LSN.
async fn write(
    journal: ConsensusJournal,
    stream: u64,
    batch: u64,
    size: usize,
    acknowledged: Arc<AtomicU64>,
    stop: Arc<AtomicBool>,
) -> u64 {
    let mut retries = 0;
    let mut next = 1;
    while !stop.load(Ordering::Relaxed) {
        let records = (next..next + batch)
            .map(|at| (Lsn(at), payload(stream, at, size)))
            .collect::<Vec<_>>();
        loop {
            match journal
                .append_batch(StreamId(u128::from(stream)), Epoch(1), records.clone())
                .await
            {
                Ok(last) => {
                    assert_eq!(last, Lsn(next + batch - 1));
                    break;
                }
                Err(JournalError::Unavailable) => {
                    retries += 1;
                    tokio::time::sleep(Duration::from_millis(20)).await;
                }
                Err(error) => panic!("stream {stream} append at {next} failed: {error:?}"),
            }
        }
        next += batch;
        acknowledged.store(next - 1, Ordering::Release);
    }
    retries
}

/// Reads `stream` from `from` and checks every record through `through`,
/// retrying while keepers come back.
async fn verify(journal: &ConsensusJournal, stream: u64, from: u64, through: u64, size: usize) {
    let id = StreamId(u128::from(stream));
    let deadline = Instant::now() + Duration::from_secs(120);
    let mut from = from;
    while from <= through {
        let page = match journal.read(id, Lsn(from), 4096, Duration::ZERO).await {
            Ok(page) => page,
            Err(error) if Instant::now() < deadline => {
                let _ = error;
                tokio::time::sleep(Duration::from_millis(50)).await;
                continue;
            }
            Err(error) => panic!("stream {stream} read at {from} failed: {error:?}"),
        };
        if page.records.is_empty() {
            assert!(
                Instant::now() < deadline,
                "stream {stream} lost acknowledged records from {from} through {through}"
            );
            tokio::time::sleep(Duration::from_millis(50)).await;
            continue;
        }
        for (at, bytes) in page.records {
            assert_eq!(at, Lsn(from), "stream {stream} skipped a record");
            assert_eq!(
                bytes,
                payload(stream, from, size),
                "stream {stream} record {from} changed"
            );
            from += 1;
        }
    }
}

async fn trim(journal: &ConsensusJournal, stream: u64, through: u64) {
    let deadline = Instant::now() + Duration::from_secs(120);
    loop {
        match journal
            .trim(StreamId(u128::from(stream)), Epoch(1), Lsn(through))
            .await
        {
            Ok(()) => return,
            Err(JournalError::Unavailable) if Instant::now() < deadline => {
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
            Err(error) => panic!("stream {stream} trim through {through} failed: {error:?}"),
        }
    }
}

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let args = args();
    let logkeeper = std::fs::canonicalize(&args.logkeeper).expect("--logkeeper binary");
    let mut random = Random(args.seed | 1);
    // Provision with the in-process keepers, then hand their media to
    // processes that can be killed.
    args.sync_mode.install();
    let mut cluster = LocalCluster::start(&[PRINCIPAL]).await.unwrap();
    let config = cluster.journal_config(1 << 40, args.record.max(4096));
    let journal = cluster.journal(PRINCIPAL, &config).unwrap();
    for stream in 1..=args.writers {
        journal.create(StreamId(u128::from(stream))).await.unwrap();
        journal
            .seal(StreamId(u128::from(stream)), Epoch(1))
            .await
            .unwrap();
    }
    let roster = cluster
        .voters()
        .into_iter()
        .chain([cluster.catalog()])
        .collect::<Vec<_>>();
    cluster.shutdown().await.unwrap();
    let logs = std::env::temp_dir().join(format!("consensus-crash-{}", std::process::id()));
    std::fs::create_dir_all(&logs).unwrap();
    let mut keepers = Keepers {
        binary: logkeeper,
        configs: roster
            .iter()
            .map(|keeper| (*keeper, cluster.write_config(*keeper).unwrap()))
            .collect(),
        logs,
        running: roster.iter().map(|_| None).collect(),
    };
    for index in 0..roster.len() {
        keepers.start(index);
    }

    let stop = Arc::new(AtomicBool::new(false));
    let acknowledged = (0..args.writers)
        .map(|_| Arc::new(AtomicU64::new(0)))
        .collect::<Vec<_>>();
    let writers = (1..=args.writers)
        .map(|stream| {
            tokio::spawn(write(
                journal.clone(),
                stream,
                args.batch,
                args.record,
                acknowledged[stream as usize - 1].clone(),
                stop.clone(),
            ))
        })
        .collect::<Vec<_>>();
    let started = Instant::now();
    let mut killed = 0;
    let mut floors = vec![1; args.writers as usize];
    for round in 1..=args.rounds {
        tokio::time::sleep(random.millis(200, 2000)).await;
        keepers.check();
        let victims: Vec<usize> = match random.next() % 4 {
            0 => vec![(random.next() % 3) as usize],
            1 => {
                let spared = (random.next() % 3) as usize;
                (0..3).filter(|index| *index != spared).collect()
            }
            2 => (0..3).collect(),
            _ => (0..4).collect(),
        };
        let before = acknowledged
            .iter()
            .map(|at| at.load(Ordering::Acquire))
            .collect::<Vec<_>>();
        for index in &victims {
            keepers.kill(*index);
        }
        killed += victims.len();
        tokio::time::sleep(random.millis(0, 1000)).await;
        for index in &victims {
            keepers.start(*index);
        }
        // Everything acknowledged before the kill must have survived it.
        // Once a stream nears its retained-record ceiling, trim a prefix
        // that earlier rounds already checked.
        let checked = Instant::now();
        for (stream, through) in (1..=args.writers).zip(&before) {
            let floor = &mut floors[stream as usize - 1];
            verify(&journal, stream, *floor, *through, args.record).await;
            if through.saturating_sub(*floor) > TRIM_AFTER {
                let kept = through - TRIM_KEEPS;
                trim(&journal, stream, kept - 1).await;
                *floor = kept;
            }
        }
        println!(
            "{{\"round\": {round}, \"killed\": {}, \"acknowledged_before_kill\": {}, \
             \"verify_ms\": {}}}",
            victims.len(),
            before.iter().sum::<u64>(),
            checked.elapsed().as_millis(),
        );
    }
    stop.store(true, Ordering::Relaxed);
    let mut retries = 0;
    for writer in writers {
        retries += writer.await.unwrap();
    }
    keepers.check();
    let total = acknowledged
        .iter()
        .map(|at| at.load(Ordering::Acquire))
        .collect::<Vec<_>>();
    for ((stream, through), floor) in (1..=args.writers).zip(&total).zip(&floors) {
        verify(&journal, stream, *floor, *through, args.record).await;
    }
    println!(
        "{{\"seed\": {}, \"sync_mode\": \"{}\", \"rounds\": {}, \"keepers_killed\": {killed}, \
         \"acknowledged\": {}, \"retries\": {retries}, \"seconds\": {:.1}, \"lost\": 0}}",
        args.seed,
        serde_json::to_value(args.sync_mode)
            .unwrap()
            .as_str()
            .unwrap(),
        args.rounds,
        total.iter().sum::<u64>(),
        started.elapsed().as_secs_f64(),
    );
}
