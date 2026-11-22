//! Every stream a server holds, and the order in which their mutations reach the journal.

use super::journal::{Captured, Journal, Recovered, Work, Write};
use super::payload::{Item, Source, Stored};
use super::state::{Decision, StreamState, Window};
use crate::history::RetainedChain;
use crate::protocol::{Accepted, CloseJournal, DigestPage, Entries, Entry, Failed, MAXIMUM_FRAME_BYTES, PageDigest, RequestBody, ResponseBody};
use bytes::Bytes;
use parking_lot::{Mutex, RwLock};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Notify, OwnedRwLockReadGuard, Semaphore, mpsc, oneshot};
use tokio_util::sync::CancellationToken;

const COMPACTION_SLACK_BYTES: u64 = 1 << 20;
const PENDING_WRITE_BYTES: usize = MAXIMUM_FRAME_BYTES + 1024;
const MINIMUM_WRITE_CHARGE: usize = 1024;
const DIGEST_PAGE_ENTRIES: usize = 1024;
const DIGEST_PAGE_BYTES: usize = 4 << 20;
const CONCURRENT_DIGEST_PAGES: usize = 2;

/// A stream's state; a stream with no waiting reader owns no task and no timer.
pub(crate) struct Slot {
    /// Names the stream in the journal's records.
    pub id: u64,
    pub name: String,
    pub state: Mutex<StreamState<Stored>>,
    /// Woken when the commit lsn or trim point moves, or the stream is dropped.
    pub progressed: Notify,
}

pub(crate) struct Store {
    journal: Arc<Journal>,
    member: Option<String>,
    admission_closed: RwLock<bool>,
    payload_reads: Arc<tokio::sync::RwLock<()>>,
    streams: Mutex<HashMap<String, Arc<Slot>>>,
    queue: mpsc::UnboundedSender<Work>,
    pending_writes: Arc<Semaphore>,
    digest_pages: Semaphore,
}

pub(crate) enum Outcome {
    Now(ResponseBody),
    /// The reply, to be sent once the journal reports the decision durable.
    Durable(oneshot::Receiver<Result<(), String>>, ResponseBody),
}

type Compaction = oneshot::Receiver<Result<(), String>>;

impl Store {
    pub fn new(journal: Arc<Journal>, recovered: Vec<Recovered>, queue: mpsc::UnboundedSender<Work>, member: Option<String>) -> Self {
        let streams = recovered.into_iter().map(|stream| {
            let slot = Slot { id: stream.id, name: stream.name.clone(), state: Mutex::new(stream.state), progressed: Notify::new() };
            (stream.name, Arc::new(slot))
        }).collect();
        Self { admission_closed: RwLock::new(journal.is_closed()), payload_reads: Default::default(), journal, member, streams: Mutex::new(streams), queue, pending_writes: Arc::new(Semaphore::new(PENDING_WRITE_BYTES)), digest_pages: Semaphore::new(CONCURRENT_DIGEST_PAGES) }
    }

    fn slot(&self, name: &str) -> Arc<Slot> {
        let mut streams = self.streams.lock();
        if let Some(slot) = streams.get(name) { return Arc::clone(slot); }
        let slot = Arc::new(Slot { id: self.journal.allocate_id(), name: name.to_owned(), state: Mutex::new(StreamState::default()), progressed: Notify::new() });
        streams.insert(name.to_owned(), Arc::clone(&slot));
        slot
    }

    fn existing(&self, name: &str) -> Option<Arc<Slot>> { self.streams.lock().get(name).cloned() }

    /// Reserves journal capacity before deciding the mutation.
    /// The decision and submission share the stream lock, so decisions reach the journal in order.
    pub async fn mutate(&self, body: RequestBody, frame_bytes: usize) -> Outcome {
        let charge = frame_bytes.saturating_add(MINIMUM_WRITE_CHARGE).min(PENDING_WRITE_BYTES) as u32;
        let Ok(admission) = self.pending_writes.clone().acquire_many_owned(charge).await else {
            return Outcome::Now(failed("the journal has stopped"));
        };
        let closed = self.admission_closed.read();
        if *closed || self.queue.is_closed() { return Outcome::Now(failed("the journal has closed admission")); }
        let (stream, decide): (String, Box<dyn FnOnce(&mut StreamState<Stored>) -> Decision>) = match body {
            RequestBody::Append(append) => (append.stream, Box::new(move |state| state.append(append.epoch, append.first_lsn, append.entries, append.commit_lsn))),
            RequestBody::Overwrite(overwrite) if overwrite.activate_ensemble.is_empty() => (overwrite.stream, Box::new(move |state| {
                state.overwrite(overwrite.epoch, overwrite.from_lsn, overwrite.entries, overwrite.complete, overwrite.commit_lsn)
            })),
            RequestBody::Overwrite(overwrite) => {
                let Ok(ensemble) = overwrite.activate_ensemble.as_ref().try_into() else { return Outcome::Now(failed("invalid ensemble digest")); };
                if !overwrite.complete { return Outcome::Now(failed("activation requires a complete overwrite")); }
                (overwrite.stream, Box::new(move |state| state.repair(overwrite.epoch, overwrite.from_lsn, overwrite.entries, overwrite.commit_lsn, ensemble)))
            }
            RequestBody::Commit(commit) => (commit.stream, Box::new(move |state| state.commit(commit.epoch, commit.commit_lsn))),
            RequestBody::Seal(seal) => (seal.stream, Box::new(move |state| state.seal(seal.epoch))),
            RequestBody::Trim(trim) => (trim.stream, Box::new(move |state| state.trim(trim.through_lsn))),
            RequestBody::DropStream(drop) => (drop.stream, Box::new(move |state| state.drop_stream(drop.epoch))),
            RequestBody::CheckSynced(check) => return self.check_after_durability(&check.stream, admission, |state| state.check_synced(check.epoch)),
            RequestBody::ActivateLoglet(check) => {
                let Ok(ensemble) = check.ensemble.as_ref().try_into() else { return Outcome::Now(failed("invalid ensemble digest")); };
                (check.stream, Box::new(move |state| state.activate(check.epoch, ensemble)))
            }
            RequestBody::ReadIndex(check) => {
                if !self.journal.is_durable() { return Outcome::Now(failed("read indexes require a durable journal")); }
                let Ok(ensemble) = check.ensemble.as_ref().try_into() else { return Outcome::Now(failed("invalid ensemble digest")); };
                return self.check_after_durability(&check.stream, admission, |state| state.read_index(check.epoch, ensemble));
            }
            RequestBody::Read(_) | RequestBody::Fetch(_) | RequestBody::Check(_) | RequestBody::Retire(_) |
            RequestBody::Identify(_) | RequestBody::RetireJournalCopy(_) | RequestBody::CloseJournal(_) | RequestBody::DigestPage(_) => return Outcome::Now(failed("not a direct mutation")),
        };
        let slot = self.slot(&stream);
        let mut state = slot.state.lock();
        let before = (state.commit, state.trim, state.dropped);
        let decision = decide(&mut state);
        if matches!(decision.reply, ResponseBody::Refused(_) | ResponseBody::Failed(_)) { return Outcome::Now(decision.reply); }
        let (done, durable) = oneshot::channel();
        if self.queue.send(Work { write: Write::Events(Arc::clone(&slot), decision.events), done, _admission: Some(admission) }).is_err() {
            return Outcome::Now(failed("the journal has stopped"));
        }
        if (state.commit, state.trim, state.dropped) != before { slot.progressed.notify_waiters(); }
        Outcome::Durable(durable, decision.reply)
    }

    /// Queues a compaction once the segments hold more than twice what the streams retain.
    /// Every stream is captured under its lock, all held together while the compaction is queued, so each capture sits exactly where it belongs in its stream's order.
    pub fn compact_if_mostly_dead(&self) {
        let disk = self.journal.bytes();
        if disk <= COMPACTION_SLACK_BYTES { return; }
        let slots: Vec<Arc<Slot>> = self.streams.lock().values().cloned().collect();
        let live: u64 = slots.iter().map(|slot| slot.state.lock().retained_bytes() as u64).sum();
        if disk <= 2 * live + COMPACTION_SLACK_BYTES { return; }
        let _ = self.queue_compaction();
    }

    fn queue_compaction(&self) -> Result<Option<Compaction>, String> {
        let closed = self.admission_closed.read();
        if *closed { return Err("the journal has closed admission".into()); }
        if !self.journal.claim_compaction() { return Ok(None); }
        let streams = self.streams.lock();
        let locked: Vec<_> = streams.values().map(|slot| (slot, slot.state.lock())).collect();
        let captured = locked.iter().map(|(slot, state)| Captured { slot: Arc::clone(slot), state: (**state).clone() }).collect();
        let (done, finished) = oneshot::channel();
        if self.queue.send(Work { write: Write::Compact(captured), done, _admission: None }).is_err() {
            self.journal.release_compaction();
            return Err("the journal has stopped".into());
        }
        Ok(Some(finished))
    }

    pub async fn close_journal(&self, request: CloseJournal) -> ResponseBody {
        if !self.journal.is_durable() || self.member.as_ref() != Some(&request.journal) {
            return failed("closure requires the original durable journal");
        }
        {
            let mut closed = self.admission_closed.write();
            if self.journal.is_closed() { return empty_ack(); }
            if *closed { return failed("journal closure is still pending"); }
            if self.streams.lock().values().any(|slot| {
                let state = slot.state.lock();
                !state.dropped && *state != StreamState::default()
            }) {
                return failed("the journal still holds a live stream");
            }
            *closed = true;
        }
        // A selected payload can retain an unlinked segment through compaction.
        // Wait for those readers before publishing the terminal base.
        let _readers = self.payload_reads.write().await;
        let (done, durable) = oneshot::channel();
        if self.queue.send(Work { write: Write::CloseJournal, done, _admission: None }).is_err() {
            return failed("the journal has stopped");
        }
        match durable.await {
            Ok(Ok(())) => empty_ack(),
            Ok(Err(error)) => failed(error),
            Err(_) => failed("the journal has stopped"),
        }
    }

    pub async fn retire_journal_copy(&self, copy: crate::protocol::RetireJournalCopy, frame_bytes: usize) -> ResponseBody {
        let Some(retirement) = copy.retirement.filter(|_| self.member.as_ref() == Some(&copy.journal)) else {
            return failed("the journal does not hold the requested member identity");
        };
        self.retire(retirement, frame_bytes).await
    }

    /// After the fence and trim are durable, wait for a base that contains
    /// neither acknowledged nor uncommitted payloads of the retired stream.
    pub async fn retire(&self, body: crate::protocol::Retire, frame_bytes: usize) -> ResponseBody {
        if !self.journal.is_durable() { return failed("retirement requires a durable journal"); }
        if body.epoch == 0 { return failed("epochs start at 1"); }
        if self.journal.is_closed() { return empty_ack(); }
        let slot = self.slot(&body.stream);
        let epoch = body.epoch;
        let accepted = match self.mutate(RequestBody::DropStream(crate::protocol::DropStream { stream: body.stream, epoch }), frame_bytes).await {
            Outcome::Now(reply) => return reply,
            Outcome::Durable(durable, reply) => match durable.await {
                Ok(Ok(())) => reply,
                Ok(Err(error)) => return failed(error),
                Err(_) => return failed("the journal has stopped"),
            },
        };
        if !matches!(accepted, ResponseBody::Accepted(_)) { return accepted; }
        loop {
            let released = self.journal.compaction_finished();
            if self.journal.is_closed() || self.journal.compacted_retirement(slot.id, epoch) { return accepted; }
            match self.queue_compaction() {
                Ok(Some(finished)) => return match finished.await {
                    Ok(Ok(())) => accepted,
                    Ok(Err(error)) => failed(error),
                    Err(_) => failed("the journal has stopped"),
                },
                Ok(None) => released.await,
                Err(error) => return failed(error),
            }
        }
    }

    pub fn check(&self, stream: &str, epoch: u64) -> ResponseBody {
        let closed = self.admission_closed.read();
        if *closed { return failed("the journal has closed admission"); }
        match self.existing(stream) { Some(slot) => slot.state.lock().check(epoch), None => StreamState::<Stored>::default().check(epoch) }
    }

    fn check_after_durability(
        &self, stream: &str, admission: tokio::sync::OwnedSemaphorePermit, check: impl FnOnce(&StreamState<Stored>) -> ResponseBody,
    ) -> Outcome {
        let Some(slot) = self.existing(stream) else {
            return Outcome::Now(check(&StreamState::default()));
        };
        let state = slot.state.lock();
        let reply = check(&state);
        if !matches!(reply, ResponseBody::Accepted(_)) { return Outcome::Now(reply); }

        // The reply's position includes accepted mutations that the journal may still be syncing.
        let (done, durable) = oneshot::channel();
        let barrier = Work { write: Write::Events(Arc::clone(&slot), Vec::new()), done, _admission: Some(admission) };
        if self.queue.send(barrier).is_err() { return Outcome::Now(failed("the journal has stopped")); }
        Outcome::Durable(durable, reply)
    }

    fn admit_payload_read(&self) -> Result<OwnedRwLockReadGuard<()>, ResponseBody> {
        let closed = self.admission_closed.read();
        if *closed { return Err(failed("the journal has closed admission")); }
        self.payload_reads.clone().try_read_owned().map_err(|_| failed("the journal has closed admission"))
    }

    /// Selects entries in `[from, to]` and where to find each payload, under the stream's lock.
    fn select(&self, state: &StreamState<Stored>, from: i64, to: i64, max_entries: usize, max_bytes: usize) -> Window<Item> {
        state.window(from, to, max_entries, max_bytes, |lsn, held| Item { lsn, epoch: held.epoch, timestamp: held.timestamp, source: self.journal.source(&held.payload) })
    }

    /// Held entries in `[from, to)`, committed or not; a selection with payloads still on disk is resolved by `entries`.
    pub fn fetch(&self, stream: &str, from: i64, to: i64, max_entries: usize, max_bytes: usize) -> Result<Selected, ResponseBody> {
        let admitted = self.admit_payload_read()?;
        let Some(slot) = self.existing(stream) else {
            return Ok(Selected(self.select(&StreamState::default(), from, -1, 0, 0), admitted));
        };
        let state = slot.state.lock();
        if state.dropped { return Err(failed("the stream was dropped")); }
        let to = to.saturating_sub(1).min(state.last());
        Ok(Selected(self.select(&state, from, to, max_entries, max_bytes), admitted))
    }

    /// Reads whatever payloads a selection still needs from the segments, off the async threads.
    pub async fn entries(&self, selected: Selected) -> ResponseBody {
        let Selected(window, admitted) = match selected.ready() { Ok(body) => return body, Err(selected) => selected };
        let journal = Arc::clone(&self.journal);
        match tokio::task::spawn_blocking(move || {
            let _admitted = admitted;
            journal.resolve(window)
        }).await {
            Ok(Ok(entries)) => ResponseBody::Entries(entries),
            Ok(Err(error)) => failed(format!("reading the segments failed: {error}")),
            Err(error) => failed(format!("reading the segments failed: {error}")),
        }
    }

    pub async fn digest_page(&self, page: DigestPage) -> ResponseBody {
        if !self.journal.is_durable() { return failed("history proofs require a durable journal"); }
        if page.from_lsn < 0 || page.through_lsn < page.from_lsn {
            return failed("invalid digest interval");
        }
        let mut chain = if page.preceding_digest.is_empty() {
            RetainedChain::new(&page.stream, page.from_lsn)
        } else if let Ok(digest) = <[u8; 32]>::try_from(page.preceding_digest.as_ref()) {
            RetainedChain::from_bytes(digest)
        } else {
            return failed("invalid preceding digest");
        };
        let Ok(_page) = self.digest_pages.try_acquire() else { return failed("history proof capacity exhausted"); };
        let admitted = match self.admit_payload_read() { Ok(admitted) => admitted, Err(reply) => return reply };
        let Some(slot) = self.existing(&page.stream) else { return failed("the stream was not found"); };
        let (window, durable) = {
            let state = slot.state.lock();
            if state.dropped || page.from_lsn <= state.trim || page.through_lsn > state.commit {
                return failed("the digest interval is outside the committed retained window");
            }
            let window = self.select(&state, page.from_lsn, page.through_lsn, DIGEST_PAGE_ENTRIES, DIGEST_PAGE_BYTES);
            let (done, durable) = oneshot::channel();
            // A selected commit can still be queued for fsync. The barrier is ordered after that commit.
            if self.queue.send(Work { write: Write::Events(Arc::clone(&slot), Vec::new()), done, _admission: None }).is_err() {
                return failed("the journal has stopped");
            }
            (window, durable)
        };
        if !matches!(durable.await, Ok(Ok(()))) { return failed("the digest interval was not made durable"); }
        let journal = Arc::clone(&self.journal);
        match tokio::task::spawn_blocking(move || {
            let _admitted = admitted;
            let entries = match journal.resolve(window) {
                Ok(entries) => entries.entries,
                Err(error) => return failed(error.to_string()),
            };
            let Some(last) = entries.last() else { return failed("the digest page is empty"); };
            for (offset, entry) in entries.iter().enumerate() {
                if page.from_lsn.checked_add(offset as i64) != Some(entry.lsn) {
                    return failed("the digest page is not contiguous");
                }
                chain.append(entry);
            }
            ResponseBody::PageDigest(PageDigest { through_lsn: last.lsn, digest: Bytes::copy_from_slice(&chain.bytes()) })
        }).await {
            Ok(reply) => reply,
            Err(error) => failed(error.to_string()),
        }
    }

    /// Long-polls up to `wait` for a committed entry at `from`.
    pub async fn read(&self, stream: &str, from: i64, max_entries: usize, max_bytes: usize, wait: Duration, cancellation: &CancellationToken) -> ResponseBody {
        let read = |state: &StreamState<Stored>, admitted| {
            if state.dropped { return Err(failed("the stream was dropped")); }
            Ok(Selected(self.select(state, from, state.commit, max_entries, max_bytes), admitted))
        };
        if wait.is_zero() {
            let admitted = match self.admit_payload_read() { Ok(admitted) => admitted, Err(reply) => return reply };
            let selected = match self.existing(stream) {
                Some(slot) => read(&slot.state.lock(), admitted),
                None => read(&StreamState::default(), admitted),
            };
            return match selected { Ok(selected) => self.entries(selected).await, Err(reply) => reply };
        }
        let slot = self.slot(stream);
        let deadline = tokio::time::Instant::now() + wait;
        loop {
            let progressed = slot.progressed.notified();
            tokio::pin!(progressed);
            progressed.as_mut().enable();
            let admitted = match self.admit_payload_read() { Ok(admitted) => admitted, Err(reply) => return reply };
            let selected = match read(&slot.state.lock(), admitted) { Ok(selected) => selected, Err(reply) => return reply };
            if !selected.0.items.is_empty() || from <= selected.0.trim_lsn { return self.entries(selected).await; }
            let Ok(empty) = selected.ready() else { unreachable!("an empty selection needs no segment reads"); };
            tokio::select! {
                _ = progressed => (),
                _ = tokio::time::sleep_until(deadline) => return empty,
                _ = cancellation.cancelled() => return empty,
            }
        }
    }
}

/// Entries selected under their stream's lock, some of whose payloads may still have to be read from the segments.
pub(crate) struct Selected(Window<Item>, OwnedRwLockReadGuard<()>);

impl Selected {
    /// The reply, if every payload is already in hand.
    pub fn ready(self) -> std::result::Result<ResponseBody, Selected> {
        if self.0.items.iter().any(|item| matches!(item.source, Source::Disk(..))) { return Err(self); }
        let Window { items, commit_lsn, trim_lsn, last_lsn } = self.0;
        let entries = items.into_iter().map(|item| {
            let Source::Ready(payload) = item.source else { unreachable!("checked above") };
            Entry { lsn: item.lsn, epoch: item.epoch, timestamp: item.timestamp, payload }
        }).collect();
        Ok(ResponseBody::Entries(Entries { entries, commit_lsn, trim_lsn, last_lsn }))
    }
}

fn empty_ack() -> ResponseBody { ResponseBody::Accepted(Accepted { last_lsn: -1, commit_lsn: -1 }) }

pub(crate) fn failed(message: impl Into<String>) -> ResponseBody { ResponseBody::Failed(Failed { message: message.into() }) }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::{Check, DropStream, Overwrite};
    use crate::server::state::Event;
    use bytes::Bytes;

    #[tokio::test]
    async fn closing_a_journal_waits_for_its_selected_disk_payload() {
        let directory = tempfile::tempdir().unwrap();
        let (journal, recovered, _) = Journal::open(directory.path(), true, 0, None).unwrap();
        let journal = Arc::new(journal);
        let (queue, work) = mpsc::unbounded_channel();
        let store = Arc::new(Store::new(Arc::clone(&journal), recovered, queue, Some("member".to_owned())));
        let runner = tokio::spawn(super::super::journal::run(journal, Arc::downgrade(&store), work));
        let request = RequestBody::Overwrite(Overwrite {
            stream: "orders".into(), epoch: 1, from_lsn: 0, complete: true, commit_lsn: 0,
            entries: vec![Entry { lsn: 0, epoch: 1, timestamp: 0, payload: Bytes::from_static(b"order") }],
            activate_ensemble: Bytes::new(),
        });
        let Outcome::Durable(written, _) = store.mutate(request, 64).await else { panic!("overwrite must persist"); };
        written.await.unwrap().unwrap();
        let selected = store.fetch("orders", 0, 1, 1, 64).unwrap();
        assert!(matches!(selected.0.items[0].source, Source::Disk(..)));
        let request = DropStream { stream: "orders".into(), epoch: 2 };
        let Outcome::Durable(dropped, _) = store.mutate(RequestBody::DropStream(request), 64).await else { panic!("drop must persist"); };
        dropped.await.unwrap().unwrap();

        {
            let mut closure = Box::pin(store.close_journal(CloseJournal { journal: "member".to_owned() }));
            assert!(futures::poll!(&mut closure).is_pending());
            assert!(store.fetch("orders", 0, 1, 1, 64).is_err());
            let ResponseBody::Entries(entries) = store.entries(selected).await else { panic!("admitted reader must finish"); };
            assert_eq!(entries.entries[0].payload, Bytes::from_static(b"order"));
            assert!(matches!(closure.await, ResponseBody::Accepted(_)));
        }
        drop(store);
        runner.await.unwrap().unwrap();
    }

    #[tokio::test]
    async fn a_full_journal_queue_delays_the_decision_until_capacity_is_available() {
        let directory = tempfile::tempdir().unwrap();
        let (journal, recovered, _) = Journal::open(directory.path(), false, 0, None).unwrap();
        let (queue, mut work) = mpsc::unbounded_channel();
        let store = Store::new(Arc::new(journal), recovered, queue, None);
        let overwrite = |stream: &str| RequestBody::Overwrite(Overwrite {
            stream: stream.into(), epoch: 1, from_lsn: 0, entries: Vec::new(), complete: true, commit_lsn: -1, activate_ensemble: Bytes::new(),
        });
        assert!(matches!(store.mutate(overwrite("first"), MAXIMUM_FRAME_BYTES).await, Outcome::Durable(_, _)));
        let mut second = Box::pin(store.mutate(overwrite("second"), 32));
        assert!(futures::poll!(&mut second).is_pending());
        assert!(store.existing("second").is_none());
        let pending = work.recv().await.unwrap();
        assert!(futures::poll!(&mut second).is_pending());
        drop(pending);
        assert!(matches!(second.await, Outcome::Durable(_, _)));
        assert!(store.existing("second").is_some());
    }

    #[tokio::test]
    async fn a_synced_check_waits_for_a_queued_epoch_install() {
        let directory = tempfile::tempdir().unwrap();
        let (journal, recovered, _) = Journal::open(directory.path(), true, 0, None).unwrap();
        let (queue, mut work) = mpsc::unbounded_channel();
        let store = Store::new(Arc::new(journal), recovered, queue, None);
        let check = || RequestBody::CheckSynced(Check { stream: "pending-sync".into(), epoch: 2 });

        assert!(matches!(store.mutate(check(), 32).await, Outcome::Now(ResponseBody::Refused(_))));
        let incoming = RequestBody::Overwrite(Overwrite {
            stream: "pending-sync".into(), epoch: 2, from_lsn: 0,
            entries: Vec::new(), complete: true, commit_lsn: -1, activate_ensemble: Bytes::new(),
        });
        let Outcome::Durable(installed, ResponseBody::Accepted(_)) = store.mutate(incoming, 32).await else {
            panic!("the complete overwrite must wait for the journal");
        };
        let Outcome::Durable(mut confirmed, ResponseBody::Accepted(_)) = store.mutate(check(), 32).await else {
            panic!("the check must wait behind the overwrite");
        };
        assert!(futures::poll!(&mut confirmed).is_pending());
        let install = work.recv().await.unwrap();
        assert!(matches!(&install.write, Write::Events(_, events) if events.contains(&Event::Synced(Some(2)))));
        install.done.send(Ok(())).unwrap();
        installed.await.unwrap().unwrap();
        let barrier = work.recv().await.unwrap();
        assert!(matches!(&barrier.write, Write::Events(_, events) if events.is_empty()));
        barrier.done.send(Ok(())).unwrap();
        confirmed.await.unwrap().unwrap();
    }

    #[tokio::test]
    async fn a_drop_queued_after_an_older_compaction_schedules_reclamation_again() {
        let directory = tempfile::tempdir().unwrap();
        let (journal, recovered, _) = Journal::open(directory.path(), true, 0, None).unwrap();
        let journal = Arc::new(journal);
        let (queue, work) = mpsc::unbounded_channel();
        let store = Arc::new(Store::new(Arc::clone(&journal), recovered, queue, None));
        assert!(matches!(store.mutate(RequestBody::Overwrite(Overwrite {
            stream: "drop-me".into(),
            epoch: 1,
            from_lsn: 0,
            entries: vec![Entry { lsn: 0, epoch: 1, timestamp: 0, payload: Bytes::from(vec![1; 2 << 20]) }],
            complete: true,
            commit_lsn: 0, activate_ensemble: Bytes::new(),
        }), 2 << 20).await, Outcome::Durable(_, _)));
        let slot = store.existing("drop-me").unwrap();
        let capture = Captured { slot: Arc::clone(&slot), state: slot.state.lock().clone() };
        assert!(journal.claim_compaction());
        let first_compaction = Work { write: Write::Compact(vec![capture]), done: oneshot::channel().0, _admission: None };
        assert!(store.queue.send(first_compaction).is_ok());
        let Outcome::Durable(dropped, _) = store.mutate(RequestBody::DropStream(DropStream { stream: "drop-me".into(), epoch: 2 }), 32).await else {
            panic!("the drop was refused");
        };
        let task = tokio::spawn(super::super::journal::run(Arc::clone(&journal), Arc::downgrade(&store), work));
        dropped.await.unwrap().unwrap();
        tokio::time::timeout(Duration::from_secs(5), async {
            while journal.bytes() >= COMPACTION_SLACK_BYTES { tokio::time::sleep(Duration::from_millis(10)).await; }
        }).await.expect("a follow-up compaction reclaimed the drop");
        drop(store);
        task.await.unwrap().unwrap();
    }
}
