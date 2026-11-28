//! Seeded keeper loss with automatic repair racing a live writer on the shipped keeper.
//!
//! Each seed loses one keeper's disk, then runs the repairer against a parked stream and
//! an active stream while the active writer keeps appending and taking the stream back
//! whenever it is fenced. A survivor can drop out during repair (a second loss) and a
//! repair pass can be cut off mid-replacement (a repairer crash). The final state must
//! be the replacement ensemble on every member, with every acknowledged record durable
//! and the active stream's history linearizable.

use std::{
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

use journal_contract::{
    BoxFuture, JournalError,
    conformance::history::{Op, Value},
};

use super::network::{ENSEMBLE, LEARNER, Network, sleep};
use super::{
    E1, History, LIMITS, NEW, OLD, READER, STREAM, network::random, payload, position, writer,
};
use crate::stream::{
    keeper::Limits,
    repair::{Member, Roster, repair_lost},
    wire::*,
};

const PARKED: StreamId = StreamId(2);
static REPAIRER: Identity = Identity::from_static("urn:logkeeper:client:repair");

/// Fails every call after its budget, as if the repairer process died there.
struct Crashing {
    inner: Arc<dyn Transport>,
    budget: AtomicUsize,
}

impl Transport for Crashing {
    fn identity(&self) -> &Identity {
        self.inner.identity()
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> BoxFuture<'_, Result<Reply, TransportError>> {
        if self
            .budget
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |left| {
                left.checked_sub(1)
            })
            .is_ok()
        {
            self.inner.call(keeper, request)
        } else {
            Box::pin(async { Err(TransportError::Unreachable) })
        }
    }
}

/// Records each seal of the history's stream in the history before sending it.
struct Recording<'a> {
    inner: Arc<dyn Transport>,
    history: &'a History<'a>,
}

impl Recording<'_> {
    fn record(&self, request: &Request) {
        match request {
            Request::Seal { stream, epoch, .. } if *stream == STREAM => {
                self.history.external_seal(&REPAIRER, *epoch)
            }
            Request::Batch(requests) => requests.iter().for_each(|request| self.record(request)),
            _ => {}
        }
    }
}

impl Transport for Recording<'_> {
    fn identity(&self) -> &Identity {
        self.inner.identity()
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> BoxFuture<'_, Result<Reply, TransportError>> {
        self.record(&request);
        self.inner.call(keeper, request)
    }
}

async fn seed_run(seed: u64) -> Vec<&'static str> {
    let mut rng = seed;
    let mut hits = Vec::new();
    let target = ENSEMBLE[(seed % 3) as usize];
    let survivors: Vec<_> = ENSEMBLE.into_iter().filter(|&id| id != target).collect();
    let next = ENSEMBLE.map(|id| if id == target { LEARNER } else { id });
    let zones = ["a", "b", "c"];
    let roster = Roster::new(
        ENSEMBLE
            .iter()
            .zip(zones)
            .map(|(&id, zone)| Member {
                id,
                zone: zone.into(),
            })
            .chain([Member {
                id: LEARNER,
                zone: zones[(seed % 3) as usize].into(),
            }]),
    );
    let network = Network::new(
        seed,
        Limits {
            max_record_bytes: LIMITS.max_record_bytes as u32,
            stream_quota_bytes: LIMITS.stream_quota_bytes,
            round_bytes_per_stream: 112,
            ..Limits::default()
        },
    );
    let history = History::new(&network);

    // A parked stream: its writer commits and goes away.
    {
        let parked = writer(&network, &NEW, ENSEMBLE);
        use journal_contract::Journal;
        parked.create(PARKED).await.unwrap();
        sleep(18).await;
        parked.seal(PARKED, E1).await.unwrap();
        for at in 1..=2 {
            parked
                .append(PARKED, E1, Lsn(at), payload(seed, at as u8))
                .await
                .unwrap();
        }
    }
    let old = writer(&network, &OLD, ENSEMBLE);
    history.call(&old, &OLD, Op::Create).await.unwrap();
    sleep(18).await;
    assert_eq!(
        position(history.call(&old, &OLD, Op::Seal(E1)).await),
        Lsn(0)
    );
    position(
        history
            .call(&old, &OLD, Op::Append(E1, Lsn(1), payload(seed, 1)))
            .await,
    );
    sleep(30).await;
    network.lose_disk(target);
    let crash = (random(&mut rng) % 40) as usize;
    let outage = random(&mut rng);
    let pause = random(&mut rng);

    // The live writer keeps appending and retakes the stream whenever it is fenced.
    let writing = async {
        let mut epoch = E1;
        let mut at = Lsn(2);
        let mut tag = 16u8;
        let mut raced = false;
        for _ in 0..24 {
            if at > Lsn(4) {
                break;
            }
            tag = tag.wrapping_add(1);
            match history
                .call(&old, &OLD, Op::Append(epoch, at, payload(seed, tag)))
                .await
            {
                Ok(_) => at = Lsn(at.0 + 1),
                Err(error) => {
                    let current = match error {
                        JournalError::Fenced { current } => {
                            raced = true;
                            current
                        }
                        _ => epoch,
                    };
                    sleep(10 + (pause >> (tag % 32)) % 30).await;
                    epoch = Epoch(current.0.max(epoch.0) + 1);
                    if let Ok(Value::Position(head)) =
                        history.call(&old, &OLD, Op::Seal(epoch)).await
                    {
                        at = Lsn(head.0 + 1);
                    }
                }
            }
        }
        raced
    };

    // The repairer's seals of the live stream enter the history as unacknowledged
    // seals, so the writer's `Fenced` replies name epochs the history knows.
    let repairer = Recording {
        inner: network.client(&REPAIRER),
        history: &history,
    };
    // Repair passes, the first cut off after a seeded number of calls.
    let repairing = async {
        sleep(outage % 40).await;
        let crashing = Crashing {
            inner: network.client(&REPAIRER),
            budget: AtomicUsize::new(crash),
        };
        let crashing = Recording {
            inner: Arc::new(crashing),
            history: &history,
        };
        let first = repair_lost(&crashing, &roster, target, &[]).await;
        if first.pending() > 0 {
            hits.push("repairer crash");
        }
        let mut done = first.pending() == 0 && first.listed > 0;
        for _ in 0..12 {
            if done {
                break;
            }
            let report = repair_lost(&repairer, &roster, target, &[]).await;
            done = report.pending() == 0;
            sleep(25).await;
        }
    };

    // A survivor drops out for a while during repair: a second loss.
    let second = survivors[(outage % 2) as usize];
    let losing = async {
        if outage % 3 == 0 {
            sleep(5 + outage % 50).await;
            network.isolate(Some(second));
            sleep(20 + (outage >> 8) % 80).await;
            network.isolate(None);
            true
        } else {
            false
        }
    };
    let (raced, _, isolated) = tokio::join!(writing, repairing, losing);
    if isolated {
        hits.push("second loss during repair");
    }
    if raced {
        hits.push("live writer fenced by repair");
    }
    network.isolate(None);
    // Converge: passes after the faults end must finish every stream.
    let mut report = repair_lost(&repairer, &roster, target, &[]).await;
    for _ in 0..4 {
        if report.pending() == 0 {
            break;
        }
        sleep(30).await;
        report = repair_lost(&repairer, &roster, target, &[]).await;
    }
    assert_eq!(report.pending(), 0, "seed {seed}: {report:?}");
    hits.push("keeper loss repaired");

    let probe = network.client(&READER);
    for stream in [STREAM, PARKED] {
        for keeper in next {
            match probe
                .call(
                    keeper,
                    Request::Check {
                        stream,
                        epoch: Epoch(0),
                    },
                )
                .await
            {
                Ok(Reply::Checked(view)) => assert!(
                    view.ensemble == next && !view.learner,
                    "seed {seed}: {keeper:?} holds {:?} for {stream:?}",
                    view.ensemble
                ),
                other => panic!("seed {seed}: {keeper:?} answered {other:?}"),
            }
        }
    }

    // A successor that only knows the old ensemble follows the move.
    let successor = writer(&network, &READER, ENSEMBLE);
    let end = position(
        history
            .call(&successor, &READER, Op::Seal(Epoch(1000)))
            .await,
    );
    assert!(
        history.acknowledged().iter().all(|(at, _)| *at <= end),
        "seed {seed}: seal head missed an acknowledged append"
    );
    for (at, bytes) in history.acknowledged() {
        assert!(
            network.copies(&next, STREAM, at, &bytes, true) >= 2,
            "seed {seed}: acknowledged record {at:?} lost by repair"
        );
    }
    history
        .call(&successor, &READER, Op::Read(Lsn(1), 16))
        .await
        .unwrap();
    history.check(seed);
    {
        use journal_contract::Journal;
        assert_eq!(successor.seal(PARKED, Epoch(1000)).await, Ok(Lsn(2)));
        let page = successor
            .read(PARKED, Lsn(1), 8, Duration::ZERO)
            .await
            .unwrap();
        assert_eq!(
            page.records,
            [(Lsn(1), payload(seed, 1)), (Lsn(2), payload(seed, 2))],
            "seed {seed}: parked stream lost records"
        );
    }
    sleep(20).await;
    hits
}

#[tokio::test(start_paused = true)]
async fn seeded_keeper_loss_repair() {
    let first = std::env::var("LOGKEEPER_SIM_FIRST_SEED").map_or(0, |value| value.parse().unwrap());
    let count: u64 =
        std::env::var("LOGKEEPER_SIM_SEEDS").map_or(48, |value| value.parse().unwrap());
    let mut coverage = std::collections::BTreeMap::<&str, usize>::new();
    for seed in first..first + count {
        let hits = tokio::time::timeout(Duration::from_secs(120), seed_run(seed))
            .await
            .unwrap_or_else(|_| panic!("executor did not quiesce in seed {seed}"));
        for hit in hits {
            *coverage.entry(hit).or_default() += 1;
        }
    }
    if first == 0 && count >= 24 {
        for event in [
            "keeper loss repaired",
            "repairer crash",
            "second loss during repair",
            "live writer fenced by repair",
        ] {
            assert!(
                coverage.contains_key(event),
                "missing repair coverage for {event}: {coverage:?}"
            );
        }
    }
    eprintln!("repair seeds {first}..{}: {coverage:?}", first + count);
}
