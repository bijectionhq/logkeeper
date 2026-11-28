//! Automatic repair after keeper loss, against the real keeper reducer.

use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use bytes::Bytes;
use journal_contract::{BoxFuture, Epoch, Identity, Journal, JournalError, Lsn, StreamId};

use tokio::sync::Semaphore;

use super::keeper::{Kind, Network};
use crate::stream::{
    repair::{Member, Outcome, Roster, repair_lost},
    wire::{KeeperId, Refusal, Reply, Request, Transport, TransportError},
    writer::Writer,
};

const K: [KeeperId; 5] = [
    KeeperId(1),
    KeeperId(2),
    KeeperId(3),
    KeeperId(4),
    KeeperId(5),
];
const OLD: [KeeperId; 3] = [K[0], K[1], K[2]];
/// The spare in the lost keeper's zone.
const NEW: [KeeperId; 3] = [K[0], K[1], K[3]];
const REPAIRER: u128 = 99;
const STREAMS: [StreamId; 3] = [StreamId(7), StreamId(8), StreamId(9)];

/// Zones a, b, c for the initial ensemble; keeper 4 spares zone c and keeper 5 zone a.
fn roster() -> Roster {
    Roster::new(
        [(1, "a"), (2, "b"), (3, "c"), (4, "c"), (5, "a")].map(|(id, zone)| Member {
            id: KeeperId(id),
            zone: zone.into(),
        }),
    )
}

fn network() -> Arc<Network> {
    Arc::new(Network::new(5, 64, 4096))
}

fn writer(network: &Arc<Network>, identity: u128) -> Writer {
    Writer::new(network.client(identity), K).unwrap()
}

fn record(index: u64) -> Bytes {
    Bytes::from(format!("record-{index}"))
}

/// Create `streams` on the first three keepers and commit `records` to each, then
/// let the writer go: the streams are parked.
async fn parked(network: &Arc<Network>, streams: &[StreamId], records: u64) {
    let writer = writer(network, 1);
    for &stream in streams {
        writer.create(stream).await.unwrap();
        network
            .until(|| OLD.iter().all(|&id| network.view(id, stream).is_some()))
            .await;
        assert_eq!(writer.seal(stream, Epoch(1)).await, Ok(Lsn(0)));
        for at in 1..=records {
            assert_eq!(
                writer.append(stream, Epoch(1), Lsn(at), record(at)).await,
                Ok(Lsn(at))
            );
        }
    }
}

fn installed(network: &Network, stream: StreamId, ensemble: [KeeperId; 3]) -> bool {
    ensemble.iter().all(|&id| {
        network
            .view(id, stream)
            .is_some_and(|view| view.ensemble == ensemble && !view.learner)
    })
}

/// Seal with a fresh client that only knows the URL's first three keepers, read
/// everything back and append once more.
async fn reopen(network: &Arc<Network>, stream: StreamId, epoch: Epoch, records: u64) {
    let successor = writer(network, 2);
    assert_eq!(successor.seal(stream, epoch).await, Ok(Lsn(records)));
    let page = successor
        .read(stream, Lsn(1), 64, std::time::Duration::ZERO)
        .await
        .unwrap();
    let expected: Vec<_> = (1..=records).map(|at| (Lsn(at), record(at))).collect();
    assert_eq!(page.records, expected);
    let next = Lsn(records + 1);
    assert_eq!(
        successor.append(stream, epoch, next, record(next.0)).await,
        Ok(next)
    );
    assert_eq!(successor.head(stream).await, Ok(next));
}

fn stale_seal(stream: StreamId, ensemble: [KeeperId; 3]) -> Request {
    Request::Seal {
        stream,
        ensemble,
        epoch: Epoch(1000),
        proposal: 1,
    }
}

#[tokio::test(start_paused = true)]
async fn parked_streams_move_to_a_spare_in_the_lost_keepers_zone() {
    let network = network();
    parked(&network, &STREAMS, 3).await;
    network.down(K[2], true);

    let report = repair_lost(&*network.client(REPAIRER), &roster(), K[2], &[]).await;
    assert_eq!(report.listed, STREAMS.len());
    assert_eq!(report.pending(), 0, "{report:?}");
    for (stream, outcome) in &report.outcomes {
        assert!(
            matches!(outcome, Outcome::Repaired { learner, .. } if *learner == K[3]),
            "{stream:?}: {outcome:?}"
        );
        assert!(installed(&network, *stream, NEW));
    }
    // A stale route cannot assemble a quorum on the old ensemble.
    let client = network.client(1);
    assert_eq!(
        client.call(K[0], stale_seal(STREAMS[0], OLD)).await,
        Ok(Reply::Refused(Refusal::WrongEnsemble { ensemble: NEW }))
    );
    for stream in STREAMS {
        reopen(&network, stream, Epoch(5), 3).await;
    }
    // Nothing is left to repair, so a second pass changes nothing.
    let again = repair_lost(&*network.client(REPAIRER), &roster(), K[2], &[]).await;
    assert_eq!((again.listed, again.pending()), (0, 0), "{again:?}");
}

#[tokio::test(start_paused = true)]
async fn a_live_writer_is_fenced_by_repair_and_follows_the_new_ensemble() {
    let network = network();
    let active = writer(&network, 1);
    let stream = STREAMS[0];
    active.create(stream).await.unwrap();
    network
        .until(|| OLD.iter().all(|&id| network.view(id, stream).is_some()))
        .await;
    active.seal(stream, Epoch(1)).await.unwrap();
    active
        .append(stream, Epoch(1), Lsn(1), record(1))
        .await
        .unwrap();
    network.down(K[2], true);
    // The writer keeps committing on the two survivors.
    active
        .append(stream, Epoch(1), Lsn(2), record(2))
        .await
        .unwrap();

    let report = repair_lost(&*network.client(REPAIRER), &roster(), K[2], &[]).await;
    assert!(
        matches!(
            report.outcomes[..],
            [(
                _,
                Outcome::Repaired {
                    epoch: Epoch(2),
                    ..
                }
            )]
        ),
        "{report:?}"
    );
    assert_eq!(
        active.append(stream, Epoch(1), Lsn(3), record(3)).await,
        Err(JournalError::Fenced { current: Epoch(2) })
    );
    // The consumer takes the stream back at a higher epoch; the writer follows.
    assert_eq!(active.seal(stream, Epoch(3)).await, Ok(Lsn(2)));
    assert_eq!(
        active.append(stream, Epoch(3), Lsn(3), record(3)).await,
        Ok(Lsn(3))
    );
    assert!(installed(&network, stream, NEW));
    // The writer's new lanes include the spare.
    network
        .until(|| network.view(K[3], stream).unwrap().synced == Some(Epoch(3)))
        .await;
}

/// The repairer installs the new ensemble on one survivor while a writer seals the
/// other on the old ensemble. Neither ensemble can form a quorum until the repairer
/// retries above the writer's epoch.
#[tokio::test(start_paused = true)]
async fn a_writer_sealing_mid_replacement_cannot_split_the_stream() {
    let network = network();
    parked(&network, &STREAMS[..1], 2).await;
    let stream = STREAMS[0];
    network.down(K[2], true);
    let repairer = HoldReplace::new(network.client(REPAIRER), K[1]);
    let roster = roster();
    let repair = repair_lost(&repairer, &roster, K[2], &[]);
    tokio::pin!(repair);
    let writer = writer(&network, 1);
    tokio::select! {
        _ = &mut repair => panic!("the held Replace cannot complete"),
        () = repairer.reached() => {}
    }
    // K1 holds the new ensemble, K2 the old one, and K4 is still a learner.
    assert_eq!(network.view(K[0], stream).unwrap().ensemble, NEW);
    assert_eq!(network.view(K[1], stream).unwrap().ensemble, OLD);
    assert_eq!(
        writer.seal(stream, Epoch(9)).await,
        Err(JournalError::Unavailable),
        "a seal assembled a quorum during the split install"
    );
    for (keeper, ensemble) in [(K[0], OLD), (K[1], NEW), (K[3], NEW)] {
        assert!(
            !matches!(
                network
                    .client(3)
                    .call(keeper, stale_seal(stream, ensemble))
                    .await,
                Ok(Reply::Sealed(_))
            ),
            "{keeper:?} accepted a seal for {ensemble:?}"
        );
    }
    repairer.release();
    let report = repair.await;
    assert!(
        matches!(report.outcomes[..], [(_, Outcome::Repaired { epoch, .. })] if epoch > Epoch(9)),
        "{report:?}"
    );
    assert!(installed(&network, stream, NEW));
    reopen(&network, stream, Epoch(2000), 2).await;
}

/// Holds the delivery of the first Replace to one keeper until released.
struct HoldReplace {
    inner: Arc<dyn Transport>,
    keeper: KeeperId,
    held: AtomicUsize,
    reached: Semaphore,
    released: Semaphore,
}

impl HoldReplace {
    fn new(inner: Arc<dyn Transport>, keeper: KeeperId) -> Self {
        Self {
            inner,
            keeper,
            held: AtomicUsize::new(0),
            reached: Semaphore::new(0),
            released: Semaphore::new(0),
        }
    }

    async fn reached(&self) {
        self.reached.acquire().await.unwrap().forget();
    }

    fn release(&self) {
        self.released.add_permits(1);
    }
}

impl Transport for HoldReplace {
    fn identity(&self) -> &Identity {
        self.inner.identity()
    }

    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> BoxFuture<'_, Result<Reply, TransportError>> {
        Box::pin(async move {
            if keeper == self.keeper
                && matches!(request, Request::Replace { .. })
                && self.held.fetch_add(1, Ordering::SeqCst) == 0
            {
                self.reached.add_permits(1);
                self.released.acquire().await.unwrap().forget();
            }
            self.inner.call(keeper, request).await
        })
    }
}

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
        let alive = self
            .budget
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |left| {
                left.checked_sub(1)
            })
            .is_ok();
        if alive {
            self.inner.call(keeper, request)
        } else {
            Box::pin(async { Err(TransportError::Unreachable) })
        }
    }
}

#[tokio::test(start_paused = true)]
async fn a_repairer_crash_at_any_step_is_completed_by_the_next_pass() {
    // Count the calls of an uninterrupted repair.
    let network = network();
    parked(&network, &STREAMS[..1], 2).await;
    network.down(K[2], true);
    let counting = Crashing {
        inner: network.client(REPAIRER),
        budget: AtomicUsize::new(usize::MAX),
    };
    let report = repair_lost(&counting, &roster(), K[2], &[]).await;
    assert_eq!(report.pending(), 0);
    let calls = usize::MAX - counting.budget.load(Ordering::SeqCst);

    for crash in 0..calls {
        let network = self::network();
        parked(&network, &STREAMS[..1], 2).await;
        network.down(K[2], true);
        let crashing = Crashing {
            inner: network.client(REPAIRER),
            budget: AtomicUsize::new(crash),
        };
        let _ = repair_lost(&crashing, &roster(), K[2], &[]).await;
        // A restarted repairer has a new proposal and starts from the keepers alone.
        let report = repair_lost(&*network.client(REPAIRER), &roster(), K[2], &[]).await;
        assert_eq!(report.pending(), 0, "crash after {crash} calls: {report:?}");
        assert!(
            installed(&network, STREAMS[0], NEW),
            "crash after {crash} calls left another ensemble"
        );
        reopen(&network, STREAMS[0], Epoch(100), 2).await;
    }
}

#[tokio::test(start_paused = true)]
async fn a_second_loss_during_repair_stalls_safely_and_resumes() {
    let network = network();
    parked(&network, &STREAMS[..1], 2).await;
    let stream = STREAMS[0];
    network.down(K[2], true);
    // K2 fails after K1 installed the new ensemble.
    let repairer = HoldReplace::new(network.client(REPAIRER), K[1]);
    let roster = roster();
    let repair = repair_lost(&repairer, &roster, K[2], &[]);
    tokio::pin!(repair);
    tokio::select! {
        _ = &mut repair => panic!("the held Replace cannot complete"),
        () = repairer.reached() => {}
    }
    assert_eq!(network.view(K[0], stream).unwrap().ensemble, NEW);
    network.down(K[1], true);
    repairer.release();
    let report = repair.await;
    assert!(
        matches!(report.outcomes[..], [(_, Outcome::Failed(_))]),
        "{report:?}"
    );
    // One survivor cannot serve or be repaired, and no seal can succeed.
    assert_eq!(
        writer(&network, 2).seal(stream, Epoch(50)).await,
        Err(JournalError::Unavailable)
    );
    let stalled = repair_lost(&*network.client(REPAIRER), &roster, K[2], &[K[1]]).await;
    assert_eq!(stalled.pending(), 1, "{stalled:?}");

    // The second keeper returns, and the next pass completes the same move.
    network.down(K[1], false);
    let report = repair_lost(&*network.client(REPAIRER), &roster, K[2], &[]).await;
    assert!(
        matches!(report.outcomes[..], [(_, Outcome::Repaired { learner, .. })] if learner == K[3]),
        "{report:?}"
    );
    reopen(&network, stream, Epoch(100), 2).await;
}

#[tokio::test(start_paused = true)]
async fn a_second_loss_after_repair_moves_the_stream_again() {
    let network = network();
    parked(&network, &STREAMS[..1], 2).await;
    let stream = STREAMS[0];
    network.down(K[2], true);
    let first = repair_lost(&*network.client(REPAIRER), &roster(), K[2], &[]).await;
    assert_eq!(first.pending(), 0);
    network.down(K[0], true);
    let second = repair_lost(&*network.client(REPAIRER), &roster(), K[0], &[K[2]]).await;
    assert!(
        matches!(second.outcomes[..], [(_, Outcome::Repaired { learner, .. })] if learner == K[4]),
        "{second:?}"
    );
    let twice = [K[4], K[1], K[3]];
    assert!(installed(&network, stream, twice));
    // A client that only knows the URL's first three keepers follows both moves.
    reopen(&network, stream, Epoch(100), 2).await;
}

#[tokio::test(start_paused = true)]
async fn listing_pages_streams_by_member_after_the_cursor() {
    let network = network();
    parked(&network, &STREAMS, 0).await;
    let client = network.client(REPAIRER);
    let list = |stream, member, max| Request::List {
        stream,
        member,
        max,
    };
    assert_eq!(
        client.call(K[0], list(StreamId(0), K[2], 2)).await,
        Ok(Reply::Listed {
            streams: vec![(STREAMS[0], OLD), (STREAMS[1], OLD)]
        })
    );
    assert_eq!(
        client.call(K[0], list(STREAMS[1], K[2], 2)).await,
        Ok(Reply::Listed {
            streams: vec![(STREAMS[2], OLD)]
        })
    );
    assert_eq!(
        client.call(K[0], list(StreamId(0), K[4], 2)).await,
        Ok(Reply::Listed { streams: vec![] })
    );
    writer(&network, 1).delete(STREAMS[0]).await.unwrap();
    network
        .until(|| network.calls(Kind::Delete).len() == 3)
        .await;
    assert_eq!(
        client.call(K[1], list(StreamId(0), K[2], 8)).await,
        Ok(Reply::Listed {
            streams: vec![(STREAMS[1], OLD), (STREAMS[2], OLD)]
        })
    );
}
