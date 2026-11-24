use super::*;
use crate::{
    BoxFuture, FileJournal, MemoryJournal, Result,
    test_support::{Scratch, block_on, panics_at},
};
use std::task::Context;

#[test]
fn memory() {
    let journal = MemoryJournal::new(LIMITS);
    block_on(run(|identity| Arc::new(journal.handle(identity))));
}

#[test]
fn file() {
    let scratch = Scratch::new();
    let journal = FileJournal::open(scratch.path().join("journal"), LIMITS).unwrap();
    block_on(run(|identity| Arc::new(journal.handle(identity))));
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Fault {
    LoseRecord,
    WrongPage,
    SealEnd,
    RejectReseal,
    SealTie,
    StaleAppend,
    WrongCaller,
    FutureHead,
    ForgetRetry,
    AcceptConflict,
    AcceptGap,
    ForgetTrim,
    WrongTrimCaller,
    TrimBeyondEnd,
    PollEarly,
    LoseWake,
    TimeoutEarly,
    MissingAsEmpty,
    IgnoreRecordSize,
    IgnoreQuota,
    KeepTrimmedBytes,
    ForgetTombstone,
    StaleHistoryHead,
    FutureHistoryHead,
}

struct Broken {
    journal: MemoryJournal,
    inner: Arc<dyn Journal>,
    identity: Identity,
    fault: Fault,
    sealed: AtomicBool,
}

impl Broken {
    async fn bypass_fence(&self, stream: StreamId, at: Lsn, payload: Bytes) -> Result<Lsn> {
        for identity in [Identity(2), Identity(3)] {
            let result = self
                .journal
                .handle(identity)
                .append(stream, Epoch(2), at, payload.clone())
                .await;
            if !matches!(result, Err(Fenced { .. })) {
                return result;
            }
        }
        unreachable!("the fixture has a sealed owner");
    }
}

impl Journal for Broken {
    fn create(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            if self.fault == Fault::LoseRecord
                && stream == SEQUENCE_STREAM
                && self.inner.head(stream).await == Ok(Lsn(1))
            {
                self.journal
                    .handle(Identity(1))
                    .trim(stream, Epoch(1), Lsn(1))
                    .await?;
            }
            self.inner.create(stream).await
        })
    }

    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            let result = self.inner.seal(stream, epoch).await;
            if stream != FENCING_STREAM || epoch != Epoch(2) {
                return result;
            }
            match self.fault {
                Fault::SealEnd => result.map(|_| Lsn(0)),
                Fault::RejectReseal
                    if result.is_ok() && self.sealed.swap(true, Ordering::Relaxed) =>
                {
                    Err(Fenced { current: epoch })
                }
                Fault::SealTie if result.is_err() => self.inner.head(stream).await,
                _ => result,
            }
        })
    }

    fn append(
        &self,
        stream: StreamId,
        epoch: Epoch,
        at: Lsn,
        payload: Bytes,
    ) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            match (self.fault, stream, at, payload.as_ref()) {
                (Fault::StaleAppend, FENCING_STREAM, _, b"stale")
                | (Fault::WrongCaller, FENCING_STREAM, _, b"wrong") => {
                    return self.bypass_fence(stream, at, payload).await;
                }
                (Fault::ForgetRetry, RETRY_STREAM, Lsn(1), b"original")
                    if self.inner.head(stream).await == Ok(Lsn(2)) =>
                {
                    return Err(Conflict {
                        committed_end: Lsn(2),
                    });
                }
                (Fault::AcceptConflict, RETRY_STREAM, Lsn(1), b"other")
                | (Fault::AcceptGap, RETRY_STREAM, Lsn(4), b"")
                | (Fault::IgnoreRecordSize, LIMITS_STREAM, Lsn(1), b"123456789")
                | (Fault::IgnoreQuota, LIMITS_STREAM, Lsn(3), _) => return Ok(at),
                (Fault::KeepTrimmedBytes, LIMITS_STREAM, Lsn(3), _)
                    if self.inner.read(stream, Lsn(1), 1, Duration::ZERO).await
                        == Err(Trimmed { floor: Lsn(2) }) =>
                {
                    return Err(Full { floor: Lsn(2) });
                }
                _ => {}
            }
            self.inner.append(stream, epoch, at, payload).await
        })
    }

    fn read(
        &self,
        stream: StreamId,
        from: Lsn,
        max: usize,
        wait: Duration,
    ) -> BoxFuture<'_, Result<Page>> {
        Box::pin(async move {
            let wait = match (self.fault, stream, from) {
                (Fault::PollEarly, POLL_STREAM, Lsn(2))
                | (Fault::TimeoutEarly, POLL_STREAM, Lsn(3)) => Duration::ZERO,
                _ => wait,
            };
            let mut read = self.inner.read(stream, from, max, wait);
            let result = if self.fault == Fault::LoseWake
                && stream == POLL_STREAM
                && self.identity == Identity(3)
                && from == Lsn(2)
            {
                poll_fn(|_| read.as_mut().poll(&mut Context::from_waker(Waker::noop()))).await
            } else {
                read.await
            };
            let mut page = result?;
            if self.fault == Fault::WrongPage && stream == SEQUENCE_STREAM && max == 1 {
                page.records[0].1 = Bytes::from_static(b"draft");
            }
            Ok(page)
        })
    }

    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            let result = self.inner.head(stream).await;
            match self.fault {
                Fault::FutureHead if stream == SEQUENCE_STREAM => result.map(|end| Lsn(end.0 + 1)),
                Fault::MissingAsEmpty if stream == LIMITS_STREAM && result == Err(NotFound) => {
                    Ok(Lsn(0))
                }
                Fault::StaleHistoryHead if stream.0 >= FIRST_SEED_STREAM => result.map(|_| Lsn(0)),
                Fault::FutureHistoryHead if stream.0 >= FIRST_SEED_STREAM => {
                    result.map(|end| Lsn(end.0 + 1))
                }
                _ => result,
            }
        })
    }

    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            if stream == TRIM_STREAM
                && match self.fault {
                    Fault::ForgetTrim => through == Lsn(2) && self.identity == Identity(1),
                    Fault::WrongTrimCaller => self.identity == Identity(2),
                    Fault::TrimBeyondEnd => through == Lsn(4),
                    _ => false,
                }
            {
                return Ok(());
            }
            self.inner.trim(stream, epoch, through).await
        })
    }

    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            if self.fault == Fault::ForgetTombstone && stream == LIMITS_STREAM {
                return Ok(());
            }
            self.inner.delete(stream).await
        })
    }
}

fn rejects(fault: Fault, check: &str) {
    let journal = MemoryJournal::new(LIMITS);
    panics_at(check, || {
        block_on(run(|identity| {
            Arc::new(Broken {
                journal: journal.clone(),
                inner: Arc::new(journal.handle(identity)),
                identity,
                fault,
                sealed: AtomicBool::new(false),
            })
        }));
    });
}

macro_rules! controls {
    ($($test:ident => $fault:ident, $check:ident;)*) => {$(
        #[test]
        fn $test() {
            rejects(Fault::$fault, $check);
        }
    )*};
}

controls! {
    rejects_lost_record => LoseRecord, SEQUENCE;
    rejects_wrong_page => WrongPage, EXACT_READ;
    rejects_wrong_seal_end => SealEnd, SEAL_END;
    rejects_failed_reseal => RejectReseal, SAME_SEAL;
    rejects_seal_tie => SealTie, EQUAL_EPOCH;
    rejects_stale_append => StaleAppend, STALE_EPOCH;
    rejects_wrong_caller => WrongCaller, APPEND_IDENTITY;
    rejects_future_head => FutureHead, HEAD;
    rejects_forgotten_retry => ForgetRetry, RETRY;
    rejects_accepted_conflict => AcceptConflict, CONFLICT;
    rejects_accepted_gap => AcceptGap, GAP;
    rejects_forgotten_trim => ForgetTrim, TRIM_RACE;
    rejects_wrong_trim_caller => WrongTrimCaller, TRIM_FENCE;
    rejects_trim_beyond_end => TrimBeyondEnd, TRIM_END;
    rejects_early_poll => PollEarly, POLL_PENDING;
    rejects_lost_wake => LoseWake, POLL_WAKE;
    rejects_early_timeout => TimeoutEarly, POLL_TIMEOUT;
    rejects_missing_as_empty => MissingAsEmpty, MISSING;
    rejects_ignored_record_size => IgnoreRecordSize, TOO_LARGE;
    rejects_ignored_quota => IgnoreQuota, FULL;
    rejects_retained_quota => KeepTrimmedBytes, TRIM_SPACE;
    rejects_forgotten_tombstone => ForgetTombstone, TOMBSTONE;
    rejects_stale_history_head => StaleHistoryHead, RANDOM;
    rejects_future_history_head => FutureHistoryHead, RANDOM;
}
