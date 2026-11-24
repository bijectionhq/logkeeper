mod guards;
mod network;

use std::{
    env,
    fs::File,
    io::{BufWriter, Write},
    sync::Arc,
    time::Duration,
};

use bytes::Bytes;
use journal_contract::{
    JournalError,
    conformance::history::{Call, Op, Value, linearizable},
    reference::Limits as ContractLimits,
};
use parking_lot::Mutex;
use tokio::sync::Notify;

use super::{Limits, Sweep, sweep_idle};
use crate::stream::{wire::*, writer::Writer};
use network::{Coverage, ENSEMBLE, Fault, LEARNER, Network, random, sleep};

const STREAM: StreamId = StreamId(1);
static OLD: Identity = Identity::from_static("urn:logkeeper:client:1");
static NEW: Identity = Identity::from_static("urn:logkeeper:client:2");
static READER: Identity = Identity::from_static("urn:logkeeper:client:3");
const E1: Epoch = Epoch(1);
const E2: Epoch = Epoch(2);
const E3: Epoch = Epoch(3);
const LIMITS: ContractLimits = ContractLimits {
    max_record_bytes: 96,
    stream_quota_bytes: 512,
};
const FAULTS: [Fault; 9] = [
    Fault::RequestLoss,
    Fault::ReplyLoss,
    Fault::Duplicate,
    Fault::Delay(35),
    Fault::Partition,
    Fault::CrashBefore,
    Fault::LoseUnsynced,
    Fault::Tear,
    Fault::CrashAfterSync,
];

type Outcome = journal_contract::Result<Value>;

struct SplitInstall<'a> {
    transport: &'a dyn Transport,
    survivors: [KeeperId; 2],
    installed: Notify,
}

impl Transport for SplitInstall<'_> {
    fn identity(&self) -> &Identity {
        self.transport.identity()
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> journal_contract::BoxFuture<'_, Result<Reply, TransportError>> {
        Box::pin(async move {
            if !matches!(request, Request::Replace { .. }) {
                return self.transport.call(keeper, request).await;
            }
            if keeper == self.survivors[1] {
                self.installed.notified().await;
                return Err(TransportError::Unreachable);
            }
            assert_eq!(keeper, self.survivors[0], "learner installed before both survivors");
            let reply = self.transport.call(keeper, request).await;
            assert_eq!(reply, Ok(Reply::Replaced));
            self.installed.notify_one();
            reply
        })
    }
}

struct History<'a> {
    network: &'a Network,
    inner: Mutex<(usize, Vec<Call>)>,
}

impl<'a> History<'a> {
    fn new(network: &'a Network) -> Self {
        Self {
            network,
            inner: Mutex::default(),
        }
    }
    async fn call(&self, writer: &Writer, caller: &Identity, op: Op) -> Outcome {
        let invocation = self.tick();
        let result = op.call(writer, STREAM).await;
        if let (Op::Append(_, at, payload), Ok(Value::Position(_))) = (&op, &result) {
            assert!(
                self.network.copies(
                    &[ENSEMBLE[0], ENSEMBLE[1], ENSEMBLE[2], LEARNER],
                    STREAM,
                    *at,
                    payload,
                    true
                ) >= 2,
                "durability: successful append must cover two disks at {at:?}"
            );
        }
        let mut inner = self.inner.lock();
        let response = inner.0;
        inner.0 += 1;
        inner.1.push(Call {
            identity: caller.clone(),
            op,
            invocation,
            response,
            result: result.clone(),
        });
        result
    }

    fn tick(&self) -> usize {
        let mut inner = self.inner.lock();
        let tick = inner.0;
        inner.0 += 1;
        tick
    }

    fn check(&self, seed: u64) {
        let inner = self.inner.lock();
        assert!(
            linearizable(&inner.1, LIMITS),
            "journal contract violated in seed {seed}: {:#?}",
            inner.1
        );
    }

    fn acknowledged(&self) -> Vec<(Lsn, Bytes)> {
        self.inner
            .lock()
            .1
            .iter()
            .filter_map(|call| match (&call.op, &call.result) {
                (Op::Append(_, at, bytes), Ok(Value::Position(end))) => {
                    assert_eq!(at, end, "append acknowledged another LSN");
                    Some((*at, bytes.clone()))
                }
                _ => None,
            })
            .collect()
    }
}

fn writer(network: &Arc<Network>, identity: &Identity, ensemble: [KeeperId; 3]) -> Writer {
    Writer::new(network.client(identity), ensemble).unwrap()
}

fn position(result: Outcome) -> Lsn {
    match result {
        Ok(Value::Position(at)) => at,
        other => panic!("expected a position, got {other:?}"),
    }
}

fn payload(seed: u64, tag: u8) -> Bytes {
    let mut bytes = seed.to_be_bytes().repeat(8);
    bytes.push(tag);
    Bytes::from(bytes)
}

async fn seed_run(seed: u64, trace: Option<&mut BufWriter<File>>) -> Coverage {
    let mut rng = seed;
    let target = ENSEMBLE[(random(&mut rng) % 3) as usize];
    let profile = seed % (FAULTS.len() as u64 + 2);
    let fault = FAULTS.get(profile as usize).copied();
    let replacing = profile == FAULTS.len() as u64;
    let network = Network::new(
        seed,
        Limits {
            max_record_bytes: LIMITS.max_record_bytes as u32,
            stream_quota_bytes: LIMITS.stream_quota_bytes,
            round_bytes_per_stream: 112,
            ..Limits::default()
        },
    );
    if trace.is_some() {
        network.record_trace();
    }
    let history = History::new(&network);
    let old = writer(&network, &OLD, ENSEMBLE);
    let mut ensemble = ENSEMBLE;
    let mut new = writer(&network, &NEW, ensemble);
    let mut reader = writer(&network, &READER, ensemble);
    let first = payload(seed, 1);
    let second = payload(seed, 2);

    history.call(&old, &OLD, Op::Create).await.unwrap();
    sleep(18).await;
    assert_eq!(
        position(history.call(&old, &OLD, Op::Seal(E1)).await),
        Lsn(0)
    );
    sleep(30).await;
    if replacing {
        // Only two keepers can receive the record. Next, lose one of those two.
        network.isolate(Some(ENSEMBLE.into_iter().find(|&id| id != target).unwrap()));
    }
    assert_eq!(
        position(
            history
                .call(&old, &OLD, Op::Append(E1, Lsn(1), first.clone()))
                .await
        ),
        Lsn(1)
    );
    sleep(45).await;

    if replacing {
        network.lose_disk(target);
        network.isolate(None);
        let survivors: Vec<_> = ENSEMBLE.into_iter().filter(|&id| id != target).collect();
        network.restart_survivors();
        assert_eq!(
            network.copies(&survivors, STREAM, Lsn(1), &first, false),
            1,
            "disk loss witness must begin repair with one copy (seed {seed})"
        );
        let survivors: [KeeperId; 2] = survivors.try_into().unwrap();
        let plan = Sweep::new(STREAM, ENSEMBLE, survivors, LEARNER, E2);
        let next = ENSEMBLE.map(|id| if id == target { LEARNER } else { id });
        let transport = network.client(&NEW);
        let split = SplitInstall {
            transport: &*transport,
            survivors,
            installed: Notify::new(),
        };
        let mut outcomes = sweep_idle(&split, [plan]).await;
        let outcome = outcomes.pop().unwrap().1;
        assert!(
            matches!(
                outcome,
                Err(super::SweepError::Transport { keeper, error: TransportError::Unreachable })
                    if keeper == survivors[1]
            ),
            "replacement did not repair both survivors before splitting (seed {seed}): {outcome:?}"
        );
        let stale_seal = Request::Seal {
            stream: STREAM,
            ensemble: ENSEMBLE,
            epoch: Epoch(9),
            proposal: None,
        };
        assert_eq!(
            network.client(&OLD).call(survivors[0], stale_seal.clone()).await.unwrap(),
            Reply::Refused(Refusal::WrongEnsemble { ensemble: next }),
            "replacement: split install admitted a stale seal (seed {seed})"
        );
        network.hit("split install");
        network.restart_survivors();
        let results = sweep_idle(&*transport, [plan]).await;
        results
            .into_iter()
            .next()
            .unwrap()
            .1
            .unwrap_or_else(|error| {
                panic!("replacement did not repair both survivors (seed {seed}): {error}")
            });
        network.hit("keeper replacement");
        assert_eq!(
            network.copies(&survivors, STREAM, Lsn(1), &first, false),
            2,
            "durability: both survivors must hold the record after repair (seed {seed})"
        );
        assert_eq!(
            network.copies(&[LEARNER], STREAM, Lsn(1), &first, false),
            1,
            "durability: replacement must install the record (seed {seed})"
        );
        ensemble = next;
        new = writer(&network, &NEW, ensemble);
        reader = writer(&network, &READER, ensemble);
        assert_eq!(
            network
                .client(&OLD)
                .call(survivors[0], stale_seal)
                .await
                .unwrap(),
            Reply::Refused(Refusal::WrongEnsemble { ensemble }),
            "replacement: a keeper promised an epoch on the stale ensemble (seed {seed})"
        );
        assert_eq!(
            history.call(&old, &OLD, Op::Seal(Epoch(9))).await,
            Err(JournalError::Unavailable),
            "replacement: old ensemble still admitted a seal (seed {seed})"
        );
    } else {
        if let Some(fault) = fault {
            network.arm(target, fault);
        }
        let race_seal = random(&mut rng) % 4 == 0;
        let (appended, _, _, _) = tokio::join!(
            history.call(&old, &OLD, Op::Append(E1, Lsn(2), second)),
            history.call(&reader, &READER, Op::Head),
            history.call(&reader, &READER, Op::Read(Lsn(1), 4)),
            async {
                if race_seal {
                    sleep(12).await;
                    history.call(&new, &NEW, Op::Seal(E2)).await.ok()
                } else {
                    None
                }
            }
        );
        if appended.is_ok() {
            network.hit("append acknowledged during fault phase");
        }
        sleep(70).await;
        network.isolate(None);
        network.restart_survivors();
        if let Some(fault) = fault {
            assert!(
                network.coverage().contains_key(fault.name()),
                "seed {seed} did not reach {fault:?}"
            );
        }
    }

    for (at, bytes) in history.acknowledged() {
        assert!(
            network.copies(&ensemble, STREAM, at, &bytes, false) >= 1,
            "durability: acknowledged record {at:?} vanished from recovered WALs (seed {seed})"
        );
    }
    let epoch = if replacing { E3 } else { E2 };
    let end = position(history.call(&new, &NEW, Op::Seal(epoch)).await);
    assert!(
        history.acknowledged().iter().all(|(at, _)| *at <= end),
        "seal head missed an acknowledged append (seed {seed})"
    );
    history
        .call(&reader, &READER, Op::Read(Lsn(1), 8))
        .await
        .unwrap();
    for (at, bytes) in history.acknowledged() {
        assert!(
            network.copies(&ensemble, STREAM, at, &bytes, true) >= 2,
            "durability: recovery omitted acknowledged record {at:?} (seed {seed})"
        );
    }

    let at = Lsn(end.0 + 1);
    let record = payload(seed, 3);
    let (written, _, _, _) = tokio::join!(
        history.call(&new, &NEW, Op::Append(epoch, at, record.clone())),
        history.call(&reader, &READER, Op::Head),
        history.call(&reader, &READER, Op::Read(Lsn(1), 8)),
        async {
            if !replacing {
                return Some(history.call(&old, &OLD, Op::Append(E1, at, first)).await);
            }
            None
        }
    );
    assert_eq!(
        position(written),
        at,
        "recovered writer must append (seed {seed})"
    );
    let (retried, _, _) = tokio::join!(
        history.call(&new, &NEW, Op::Append(epoch, at, record)),
        history.call(&new, &NEW, Op::Append(epoch, at, payload(seed, 4))),
        history.call(
            &new,
            &NEW,
            Op::Append(epoch, Lsn(at.0 + 2), Bytes::from_static(b"gap"))
        ),
    );
    assert_eq!(position(retried), at);
    let (trimmed, _, _) = tokio::join!(
        history.call(&new, &NEW, Op::Trim(epoch, Lsn(1))),
        history.call(&reader, &READER, Op::Read(Lsn(1), 8)),
        history.call(&reader, &READER, Op::Head),
    );
    trimmed.unwrap();
    history
        .call(&reader, &READER, Op::Read(Lsn(1), 8))
        .await
        .ok();
    history
        .call(&reader, &READER, Op::Read(Lsn(2), 8))
        .await
        .unwrap();
    history.call(&new, &NEW, Op::Delete).await.unwrap();
    history.call(&reader, &READER, Op::Head).await.ok();
    history.call(&new, &NEW, Op::Create).await.ok();
    history.check(seed);
    // Let detached copies of a final quorum request finish before the next seed.
    sleep(20).await;
    if let Some(trace) = trace {
        network.write_trace(seed, trace).unwrap();
    }
    network.coverage()
}

#[tokio::test(start_paused = true)]
async fn seeded_stream_journal() {
    let first =
        env::var("LOGKEEPER_SIM_FIRST_SEED").map_or(0, |value| value.parse::<u64>().unwrap());
    let count = env::var("LOGKEEPER_SIM_SEEDS").map_or(44, |value| value.parse::<u64>().unwrap());
    assert!(count > 0);
    let mut coverage = Coverage::new();
    let mut trace = env::var_os("LOGKEEPER_SIM_PUBLICATION_TRACE")
        .map(|path| BufWriter::new(File::create(path).unwrap()));
    for seed in first..first + count {
        let observed =
            tokio::time::timeout(Duration::from_secs(90), seed_run(seed, trace.as_mut()))
                .await
                .unwrap_or_else(|_| panic!("executor did not quiesce in seed {seed}"));
        for (event, count) in observed {
            *coverage.entry(event).or_default() += count;
        }
    }
    if let Some(mut trace) = trace {
        trace.flush().unwrap();
    }
    if first == 0 && count >= 11 {
        for event in FAULTS.map(Fault::name).into_iter().chain([
            "reordering",
            "duplicate delivered",
            "reopened WAL",
            "disk loss",
            "keeper replacement",
            "split install",
        ]) {
            assert!(
                coverage.contains_key(event),
                "missing fault coverage for {event}"
            );
        }
    }
    eprintln!(
        "stream journal seeds {first}..{}: {coverage:?}",
        first + count
    );
}
