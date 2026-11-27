//! Reusable conformance suite for a healthy journal with three caller identities.
//!
//! Configure the journal with [LIMITS] and give each run a fresh stream
//! namespace. The factory must return handles to the same journal. The suite is
//! async and uses the caller's executor. It panics with the failed check's name.
//!
//! A consumer taking over a stream must apply records through the head returned
//! by seal before it serves requests.

pub mod history;

use crate::{
    Epoch, Identity, Journal, JournalError::*, Lsn, Page, StreamId, reference::Limits, timer::Sleep,
};
use bytes::Bytes;
use history::{History, Op, Value};
use std::{
    fmt::Debug,
    future::{Future, poll_fn},
    pin::pin,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
    },
    task::{Poll, Wake, Waker},
    time::{Duration, Instant},
};

/// Limits required on the test fixture so quota errors use small payloads.
pub const LIMITS: Limits = Limits {
    max_record_bytes: 8,
    stream_quota_bytes: 16,
};

const SEQUENCE: &str = "committed sequence";
const EXACT_READ: &str = "exact committed read";
const SEAL_HEAD: &str = "seal reports head";
const SAME_SEAL: &str = "same identity reseal";
const EQUAL_EPOCH: &str = "equal epoch fencing";
const STALE_EPOCH: &str = "stale epoch fencing";
const APPEND_IDENTITY: &str = "append caller fencing";
const HEAD: &str = "fresh head";
const RETRY: &str = "identical retry";
const CONFLICT: &str = "conflicting payload";
const GAP: &str = "conditional append";
const TRIM_RACE: &str = "trim order and committed read snapshots";
const TRIM_FENCE: &str = "trim caller fencing";
const TRIM_HEAD: &str = "trim bounded by head";
const POLL_PENDING: &str = "long poll waits at head";
const POLL_WAKE: &str = "append wakes long polls";
const POLL_TIMEOUT: &str = "long poll deadline";
const MISSING: &str = "missing stream";
const TOO_LARGE: &str = "record size limit";
const FULL: &str = "stream byte quota";
const TRIM_SPACE: &str = "trim frees quota";
const TOMBSTONE: &str = "permanent deletion";
const RANDOM: &str = "seeded history linearizability";

const SEQUENCE_STREAM: StreamId = StreamId(1);
const FENCING_STREAM: StreamId = StreamId(2);
const RETRY_STREAM: StreamId = StreamId(3);
const TRIM_STREAM: StreamId = StreamId(4);
const POLL_STREAM: StreamId = StreamId(5);
const LIMITS_STREAM: StreamId = StreamId(6);
const FIRST_SEED_STREAM: u128 = 100;
const SEEDS: u64 = 24;
const PHASES: u64 = 3;

const READ_WAIT: Duration = Duration::from_millis(30);
const WAKE_DEADLINE: Duration = Duration::from_secs(2);
const LONG_WAIT: Duration = Duration::from_secs(10);
const SUITE_DEADLINE: Duration = Duration::from_secs(90);

/// Runs the directed checks and 24 seeded concurrent histories.
///
/// The factory is called once per identity. Use an isolated test fixture with
/// [LIMITS], since the suite creates streams and permanently deletes one.
pub async fn run<F: Fn(Identity) -> Arc<dyn Journal>>(make: F) {
    let start = Instant::now();
    run_with_clock(make, || start.elapsed(), Sleep::new).await;
}

/// Runs conformance with the fixture's clock. `now` returns time since an
/// arbitrary origin, and `sleep` waits on that same clock.
pub async fn run_with_clock<F, Timer>(
    make: F,
    now: impl Fn() -> Duration,
    sleep: impl Fn(Duration) -> Timer,
) where
    F: Fn(Identity) -> Arc<dyn Journal>,
    Timer: Future<Output = ()>,
{
    let clients = Clients([0, 1, 2].map(|index| make(Clients::identity(index))));
    within("suite deadline", SUITE_DEADLINE, &sleep, async {
        sequence(&clients, &sleep).await;
        fencing(&clients).await;
        retries(&clients).await;
        trimming(&clients).await;
        long_polls(&clients, &now, &sleep).await;
        limits_and_lifecycle(&clients).await;
        for seed in 0..SEEDS {
            seeded(&clients, seed)
                .await
                .check(&format!("{RANDOM} (seed {seed})"));
        }
    })
    .await;
}

struct Clients([Arc<dyn Journal>; 3]);

impl Clients {
    fn identity(index: usize) -> Identity {
        Identity::from(format!("urn:logkeeper:client:{}", index + 1))
    }
}

fn expect<T: Debug + PartialEq>(name: &str, actual: T, expected: T) {
    assert_eq!(actual, expected, "{name}");
}

async fn within<F: Future, Timer: Future<Output = ()>>(
    check: &str,
    duration: Duration,
    sleep: &impl Fn(Duration) -> Timer,
    future: F,
) -> F::Output {
    let mut future = pin!(future);
    let mut timeout = pin!(sleep(duration));
    poll_fn(|cx| {
        let result = future.as_mut().poll(cx);
        if result.is_pending() {
            assert!(
                timeout.as_mut().poll(cx).is_pending(),
                "{check}: deadline expired"
            );
        }
        result
    })
    .await
}

// Every expected page holds client data only: no append yields a typed
// recovery entry, so each compared read also checks `Page::recoveries`.
fn page(floor: u64, head: u64, entries: &[(u64, &'static [u8])]) -> crate::Result<Page> {
    Ok(Page::new(
        Lsn(floor),
        entries
            .iter()
            .map(|&(at, bytes)| (Lsn(at), Bytes::from_static(bytes)))
            .collect(),
        Lsn(head),
    ))
}

// The healthy fixture must eventually make each append visible on the read path.
async fn read_through<Timer: Future<Output = ()>>(
    journal: &dyn Journal,
    check: &str,
    stream: StreamId,
    from: Lsn,
    max: usize,
    head: Lsn,
    sleep: &impl Fn(Duration) -> Timer,
) -> crate::Result<Page> {
    within(check, WAKE_DEADLINE, sleep, async {
        loop {
            let reply = journal.read(stream, from, max, Duration::ZERO).await;
            if !matches!(&reply, Ok(page) if page.head < head) {
                return reply;
            }
            sleep(Duration::from_millis(1)).await;
        }
    })
    .await
}

async fn sequence<Timer: Future<Output = ()>>(
    clients: &Clients,
    sleep: &impl Fn(Duration) -> Timer,
) {
    let [a, b, _] = &clients.0;
    let stream = SEQUENCE_STREAM;
    expect(SEQUENCE, a.create(stream).await, Ok(()));
    expect(
        SEQUENCE,
        b.read(stream, Lsn(1), 2, Duration::ZERO).await,
        page(1, 0, &[]),
    );
    expect(SEQUENCE, a.seal(stream, Epoch(1)).await, Ok(Lsn(0)));
    expect(
        SEQUENCE,
        a.append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"one"))
            .await,
        Ok(Lsn(1)),
    );
    expect(SEQUENCE, b.create(stream).await, Ok(()));
    expect(
        SEQUENCE,
        a.append(stream, Epoch(1), Lsn(2), Bytes::from_static(b"two"))
            .await,
        Ok(Lsn(2)),
    );
    expect(
        SEQUENCE,
        read_through(b.as_ref(), SEQUENCE, stream, Lsn(1), 2, Lsn(2), sleep).await,
        page(1, 2, &[(1, b"one"), (2, b"two")]),
    );
    expect(
        EXACT_READ,
        read_through(b.as_ref(), EXACT_READ, stream, Lsn(1), 1, Lsn(2), sleep).await,
        page(1, 2, &[(1, b"one")]),
    );
    expect(
        EXACT_READ,
        read_through(b.as_ref(), EXACT_READ, stream, Lsn(2), 2, Lsn(2), sleep).await,
        page(1, 2, &[(2, b"two")]),
    );
    expect(
        EXACT_READ,
        read_through(b.as_ref(), EXACT_READ, stream, Lsn(3), 2, Lsn(2), sleep).await,
        page(1, 2, &[]),
    );
    expect(HEAD, b.head(stream).await, Ok(Lsn(2)));
}

async fn fencing(clients: &Clients) {
    let stream = FENCING_STREAM;
    let [a, _, _] = &clients.0;
    a.create(stream).await.unwrap();
    a.seal(stream, Epoch(1)).await.unwrap();
    a.append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"a"))
        .await
        .unwrap();

    let replies = History::new(stream)
        .round(
            clients,
            [
                (1, Op::Seal(Epoch(2))),
                (2, Op::Seal(Epoch(2))),
                (
                    0,
                    Op::Append(Epoch(1), Lsn(2), Bytes::from_static(b"before")),
                ),
            ],
            &mut Schedule(1),
        )
        .await;
    let winner = match (&replies[0], &replies[1]) {
        (Ok(Value::Position(_)), Err(Fenced { current: Epoch(2) })) => 1,
        (Err(Fenced { current: Epoch(2) }), Ok(Value::Position(_))) => 2,
        _ => panic!("{EQUAL_EPOCH}: {replies:?}"),
    };
    let head = match replies[2] {
        Ok(Value::Position(Lsn(2))) => Lsn(2),
        Err(Fenced { current: Epoch(2) }) => Lsn(1),
        _ => panic!("{STALE_EPOCH}: {replies:?}"),
    };
    expect(
        SEAL_HEAD,
        replies[winner - 1].clone(),
        Ok(Value::Position(head)),
    );
    let loser = &clients.0[3 - winner];
    let owner = &clients.0[winner];
    expect(SAME_SEAL, owner.seal(stream, Epoch(2)).await, Ok(head));
    expect(
        EQUAL_EPOCH,
        loser.seal(stream, Epoch(2)).await,
        Err(Fenced { current: Epoch(2) }),
    );
    expect(
        STALE_EPOCH,
        a.seal(stream, Epoch(1)).await,
        Err(Fenced { current: Epoch(2) }),
    );
    let next = Lsn(head.0 + 1);
    expect(
        STALE_EPOCH,
        a.append(stream, Epoch(1), next, Bytes::from_static(b"stale"))
            .await,
        Err(Fenced { current: Epoch(2) }),
    );
    expect(
        APPEND_IDENTITY,
        loser
            .append(stream, Epoch(2), next, Bytes::from_static(b"wrong"))
            .await,
        Err(Fenced { current: Epoch(2) }),
    );
    expect(HEAD, owner.head(stream).await, Ok(head));
}

async fn retries(clients: &Clients) {
    let a = &clients.0[0];
    let stream = RETRY_STREAM;
    let payload = Bytes::from_static(b"original");
    a.create(stream).await.unwrap();
    a.seal(stream, Epoch(1)).await.unwrap();
    a.append(stream, Epoch(1), Lsn(1), payload.clone())
        .await
        .unwrap();
    a.append(stream, Epoch(1), Lsn(2), payload.clone())
        .await
        .unwrap();
    expect(
        RETRY,
        a.append(stream, Epoch(1), Lsn(1), payload).await,
        Ok(Lsn(1)),
    );
    let conflict = Err(Conflict { head: Lsn(2) });
    expect(
        CONFLICT,
        a.append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"other"))
            .await,
        conflict.clone(),
    );
    expect(
        GAP,
        a.append(stream, Epoch(1), Lsn(4), Bytes::new()).await,
        conflict,
    );
    expect(
        RETRY,
        a.read(stream, Lsn(1), 3, Duration::ZERO).await,
        page(1, 2, &[(1, b"original"), (2, b"original")]),
    );
}

async fn trimming(clients: &Clients) {
    let [a, b, _] = &clients.0;
    let stream = TRIM_STREAM;
    let mut history = History::new(stream);
    let mut schedule = Schedule(2);
    for operation in [
        Op::Create,
        Op::Seal(Epoch(1)),
        Op::Append(Epoch(1), Lsn(1), Bytes::from_static(b"a")),
        Op::Append(Epoch(1), Lsn(2), Bytes::from_static(b"b")),
        Op::Append(Epoch(1), Lsn(3), Bytes::from_static(b"c")),
    ] {
        history
            .round(clients, [(0, operation)], &mut schedule)
            .await[0]
            .as_ref()
            .unwrap();
    }
    expect(
        TRIM_FENCE,
        b.trim(stream, Epoch(1), Lsn(2)).await,
        Err(Fenced { current: Epoch(1) }),
    );
    expect(
        TRIM_HEAD,
        a.trim(stream, Epoch(1), Lsn(4)).await,
        Err(Conflict { head: Lsn(3) }),
    );
    history
        .round(
            clients,
            [
                (0, Op::Trim(Epoch(1), Lsn(2))),
                (1, Op::Read(Lsn(1), 2)),
                (2, Op::Read(Lsn(3), 2)),
                (2, Op::Head),
            ],
            &mut schedule,
        )
        .await;
    history
        .round(clients, [(0, Op::Trim(Epoch(1), Lsn(1)))], &mut schedule)
        .await;
    history
        .round(
            clients,
            [(1, Op::Read(Lsn(1), 2)), (2, Op::Read(Lsn(3), 2))],
            &mut schedule,
        )
        .await;
    history
        .round(
            clients,
            [(0, Op::Append(Epoch(1), Lsn(2), Bytes::from_static(b"b")))],
            &mut schedule,
        )
        .await;
    history.check(TRIM_RACE);
}

async fn long_polls<Timer: Future<Output = ()>>(
    clients: &Clients,
    now: &impl Fn() -> Duration,
    sleep: &impl Fn(Duration) -> Timer,
) {
    let [a, b, c] = &clients.0;
    let stream = POLL_STREAM;
    a.create(stream).await.unwrap();
    a.seal(stream, Epoch(1)).await.unwrap();
    a.append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"a"))
        .await
        .unwrap();

    let mut waiting =
        [b, c].map(|journal| Box::pin(on_wake(journal.read(stream, Lsn(2), 2, LONG_WAIT))));
    poll_fn(|cx| {
        for read in &mut waiting {
            assert!(read.as_mut().poll(cx).is_pending(), "{POLL_PENDING}");
        }
        Poll::Ready(())
    })
    .await;

    a.append(stream, Epoch(1), Lsn(2), Bytes::from_static(b"wake"))
        .await
        .unwrap();
    within(POLL_WAKE, WAKE_DEADLINE, sleep, async {
        for read in waiting {
            expect(POLL_WAKE, read.await, page(1, 2, &[(2, b"wake")]));
        }
    })
    .await;

    let start = now();
    let result = within(
        POLL_TIMEOUT,
        WAKE_DEADLINE,
        sleep,
        b.read(stream, Lsn(3), 2, READ_WAIT),
    )
    .await;
    let result = result.unwrap_or_else(|error| panic!("{POLL_TIMEOUT}: {error}"));
    assert!(
        result.head <= Lsn(2) && result.floor == Lsn(1) && result.records.is_empty(),
        "{POLL_TIMEOUT}: invalid empty page {result:?}"
    );
    assert!(
        now() - start >= READ_WAIT,
        "{POLL_TIMEOUT}: returned before the deadline"
    );
}

// Repoll a read only after it signals progress, independently of the other
// read and the watchdog.
async fn on_wake<F: Future>(future: F) -> F::Output {
    let mut future = pin!(future);
    let ready = Arc::new(Readiness {
        notified: AtomicBool::new(true),
        parent: Mutex::new(None),
    });
    let waker = Waker::from(ready.clone());
    poll_fn(|cx| {
        *ready.parent.lock().unwrap() = Some(cx.waker().clone());
        if ready.notified.swap(false, Ordering::AcqRel) {
            future
                .as_mut()
                .poll(&mut std::task::Context::from_waker(&waker))
        } else {
            Poll::Pending
        }
    })
    .await
}

struct Readiness {
    notified: AtomicBool,
    parent: Mutex<Option<Waker>>,
}

impl Wake for Readiness {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.notified.store(true, Ordering::Release);
        let parent = self.parent.lock().unwrap().clone();
        if let Some(parent) = parent {
            parent.wake();
        }
    }
}

async fn limits_and_lifecycle(clients: &Clients) {
    let [a, b, _] = &clients.0;
    let stream = LIMITS_STREAM;
    let payload = Bytes::from_static(b"12345678");
    expect(MISSING, a.head(stream).await, Err(NotFound));
    expect(
        MISSING,
        b.read(stream, Lsn(1), 1, Duration::ZERO).await,
        Err(NotFound),
    );
    a.create(stream).await.unwrap();
    a.seal(stream, Epoch(1)).await.unwrap();
    expect(
        TOO_LARGE,
        a.append(stream, Epoch(1), Lsn(1), Bytes::from_static(b"123456789"))
            .await,
        Err(TooLarge {
            max: LIMITS.max_record_bytes,
        }),
    );
    a.append(stream, Epoch(1), Lsn(1), payload.clone())
        .await
        .unwrap();
    a.append(stream, Epoch(1), Lsn(2), payload.clone())
        .await
        .unwrap();
    expect(
        FULL,
        a.append(stream, Epoch(1), Lsn(3), payload.clone()).await,
        Err(Full { floor: Lsn(1) }),
    );
    expect(TRIM_SPACE, a.trim(stream, Epoch(1), Lsn(1)).await, Ok(()));
    expect(
        TRIM_SPACE,
        a.append(stream, Epoch(1), Lsn(3), payload).await,
        Ok(Lsn(3)),
    );
    expect(
        FULL,
        a.append(stream, Epoch(1), Lsn(4), Bytes::from_static(b"x"))
            .await,
        Err(Full { floor: Lsn(2) }),
    );
    expect(TOMBSTONE, b.delete(stream).await, Ok(()));
    expect(TOMBSTONE, a.create(stream).await, Err(Deleted));
    expect(TOMBSTONE, a.head(stream).await, Err(Deleted));
    expect(
        TOMBSTONE,
        b.read(stream, Lsn(2), 2, Duration::ZERO).await,
        Err(Deleted),
    );
    expect(TOMBSTONE, a.seal(stream, Epoch(2)).await, Err(Deleted));
    expect(
        TOMBSTONE,
        a.append(stream, Epoch(1), Lsn(4), Bytes::new()).await,
        Err(Deleted),
    );
    expect(
        TOMBSTONE,
        a.trim(stream, Epoch(1), Lsn(3)).await,
        Err(Deleted),
    );
}

async fn seeded(clients: &Clients, seed: u64) -> History {
    let mut history = History::new(StreamId(FIRST_SEED_STREAM + u128::from(seed)));
    let mut schedule = Schedule(seed);
    let mut owner = 0;
    let mut head = Lsn(1);
    for operation in [
        Op::Create,
        Op::Seal(Epoch(1)),
        Op::Append(Epoch(1), head, Bytes::from_static(b"start")),
    ] {
        history
            .round(clients, [(owner, operation)], &mut schedule)
            .await;
    }
    for phase in 1..=PHASES {
        let epoch = Epoch(phase + 1);
        let mut challengers = [(owner + 1) % 3, (owner + 2) % 3];
        schedule.shuffle(&mut challengers);
        let [first, second] = challengers;
        let next = Lsn(head.0 + 1);
        let sealed = history
            .round(
                clients,
                [
                    (first, Op::Seal(epoch)),
                    (second, Op::Seal(epoch)),
                    (
                        owner,
                        Op::Append(Epoch(phase), next, Bytes::from_static(b"old")),
                    ),
                    (first, Op::Head),
                    (second, Op::Read(head, 2)),
                ],
                &mut schedule,
            )
            .await;
        let (winner, loser) = if sealed[0].is_ok() {
            (first, second)
        } else {
            (second, first)
        };
        owner = winner;
        if sealed[2] == Ok(Value::Position(next)) {
            head = next;
        }
        let next = Lsn(head.0 + 1);
        let payload = Bytes::from(vec![seed as u8, phase as u8]);
        let retry = if schedule.next() % 2 == 0 {
            payload.clone()
        } else {
            Bytes::from_static(b"other")
        };
        let from = Lsn(1 + schedule.next() % head.0);
        let max = (schedule.next() % 3) as usize + 1;
        let appended = history
            .round(
                clients,
                [
                    (owner, Op::Append(epoch, next, payload.clone())),
                    (owner, Op::Append(epoch, next, retry)),
                    (loser, Op::Append(epoch, next, payload)),
                    (owner, Op::Trim(epoch, head)),
                    (loser, Op::Read(from, max)),
                    (owner, Op::Read(next, 2)),
                    (loser, Op::Head),
                ],
                &mut schedule,
            )
            .await;
        if appended[..2].contains(&Ok(Value::Position(next))) {
            head = next;
        }
    }
    history
        .round(
            clients,
            [(1, Op::Head), (2, Op::Read(head, 2))],
            &mut schedule,
        )
        .await;
    history
}

struct Schedule(u64);

impl Schedule {
    fn next(&mut self) -> u64 {
        // SplitMix64, including a well-defined schedule for seed zero.
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut value = self.0;
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
        value ^ (value >> 31)
    }

    fn shuffle<T>(&mut self, entries: &mut [T]) {
        for i in (1..entries.len()).rev() {
            entries.swap(i, (self.next() % (i + 1) as u64) as usize);
        }
    }
}

#[cfg(test)]
mod tests;
