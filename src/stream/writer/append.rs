//! One ordered append pipeline per keeper. A slow keeper never delays a quorum.

use std::{
    collections::HashMap,
    sync::{Arc, Weak},
};

use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Result, StreamId};
use parking_lot::Mutex;
use tokio::sync::{oneshot, watch};

use super::{
    Io, KeeperId, Reply, Request, Stream,
    decision::{append_head, fresh_sample},
    quorum,
    recovery::{self, Recovery},
};

type Sender = oneshot::Sender<Result<Lsn>>;

pub(super) use crate::stream::proposer::append::APPEND_RECORDS;
use crate::stream::{
    proposer::append::{Admission, Completions, State, Work},
    timed::{Entry, TimedOriginal},
};
type Observation = watch::Receiver<Option<Result<Lsn>>>;

pub(super) struct Active {
    pub(super) epoch: Epoch,
    io: Arc<Io>,
    stream: StreamId,
    ensemble: [KeeperId; 3],
    recovery: Recovery,
    state: Mutex<DriverState>,
    change: watch::Sender<()>,
}

struct DriverState {
    proposer: State,
    waiters: HashMap<u64, Sender>,
    observations: [Option<(u64, Observation)>; 3],
}

impl DriverState {
    fn complete(&mut self, completions: Completions) {
        for (id, result) in completions {
            if let Some(sender) = self.waiters.remove(&id) {
                let _ = sender.send(result);
            }
        }
    }
}

impl Active {
    pub(super) fn start(io: Arc<Io>, stream: &Stream, recovery: Recovery) -> Arc<Self> {
        let active = Arc::new(Self {
            epoch: recovery.epoch,
            io,
            stream: stream.id,
            ensemble: stream.ensemble,
            state: Mutex::new(DriverState {
                proposer: State::new(recovery.tail(), recovery.floor),
                waiters: HashMap::new(),
                observations: [None, None, None],
            }),
            recovery,
            change: watch::channel(()).0,
        });
        for lane in 0..active.ensemble.len() {
            tokio::spawn(replicate(
                Arc::downgrade(&active),
                lane,
                active.change.subscribe(),
            ));
        }
        active
    }

    pub(super) async fn ready(&self) -> Result<()> {
        let mut change = self.change.subscribe();
        loop {
            if let Some(ready) = self.state.lock().proposer.ready() {
                self.wake();
                return ready;
            }
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        }
    }

    pub(super) fn head(&self) -> Lsn {
        self.state.lock().proposer.head()
    }

    pub(super) async fn published(&self, tail: Lsn) -> Result<()> {
        if tail == Lsn(0) {
            return Ok(());
        }
        let mut change = self.change.subscribe();
        loop {
            if let Some(result) = self.state.lock().proposer.publication(tail) {
                return result;
            }
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        }
    }

    pub(super) fn trim(&self, floor: Lsn) {
        self.state.lock().proposer.trim(floor);
        self.wake();
    }

    pub(super) fn close(&self, error: JournalError) {
        let mut state = self.state.lock();
        let completions = state.proposer.close(error);
        state.complete(completions);
        self.wake();
    }

    pub(super) async fn append(&self, at: Lsn, payload: Entry) -> Result<Lsn> {
        let mut change = self.change.subscribe();
        let wait = loop {
            {
                let mut state = self.state.lock();
                match state.proposer.append(at, &payload) {
                    Admission::Accepted(id) => {
                        let (send, wait) = oneshot::channel();
                        state.waiters.insert(id, send);
                        self.wake();
                        break Some(wait);
                    }
                    Admission::Retry => {
                        self.wake();
                        break None;
                    }
                    Admission::Refused(error) => return Err(error),
                    Admission::Waiting => {}
                }
            }
            // A competing live append can choose this position. Wait for that
            // decision before reporting the head in a conflict.
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        };
        match wait {
            Some(wait) => wait.await.unwrap_or(Err(JournalError::Unavailable)),
            None => self.retry_committed(at, payload).await,
        }
    }

    async fn retry_committed(&self, at: Lsn, payload: Entry) -> Result<Lsn> {
        // Check retained bytes before publishing. Caller-supplied bytes are never
        // sent in a lane Append until the writer has assigned them a position.
        let accepted = {
            let state = self.state.lock();
            std::array::from_fn::<_, 3, _>(|index| {
                state
                    .proposer
                    .accepted(index, at)
                    .then_some(self.ensemble[index])
            })
        };
        quorum(accepted.map(|keeper| {
            let payload = &payload;
            async move {
                let keeper = keeper.ok_or(JournalError::Unavailable)?;
                let retained =
                    recovery::fetch(&self.io, keeper, self.stream, self.epoch, at).await?;
                if retained != *payload {
                    return Err(JournalError::Conflict { head: self.head() });
                }
                self.io.publish(keeper, self.stream, self.epoch, at).await
            }
        }))
        .await
        .map(|_| at)
        .map_err(|error| match error {
            JournalError::Conflict { .. } => JournalError::Conflict { head: self.head() },
            error => error,
        })
    }

    pub(super) fn reserve_timed(&self, original: TimedOriginal) -> Result<()> {
        self.state.lock().proposer.reserve_timed(original)
    }

    pub(super) fn timed_entry(&self, original: TimedOriginal) -> Option<Entry> {
        self.state.lock().proposer.timed_entry(original)
    }

    fn wake(&self) {
        self.change.send_replace(());
    }

    pub(super) fn open_round(&self) -> u64 {
        self.state.lock().proposer.open()
    }

    pub(super) fn retry_lanes(&self) {
        self.state.lock().proposer.retry_lanes();
        self.wake();
    }

    pub(super) fn observation(&self, lane: usize, after: u64) -> Option<Observation> {
        self.state.lock().observations[lane]
            .as_ref()
            .filter(|(serial, _)| fresh_sample(after, *serial))
            .map(|(_, result)| result.clone())
    }

    pub(super) async fn cover(&self, sample: Lsn) -> Result<Lsn> {
        let mut change = self.change.subscribe();
        loop {
            if let Some(result) = self.state.lock().proposer.cover(sample) {
                return result;
            }
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        }
    }

    async fn run(&self, index: usize, work: Work) -> Result<Option<Lsn>> {
        let keeper = self.ensemble[index];
        match work {
            Work::Sync(floor) => recovery::sync(&self.io, &self.recovery, keeper, floor)
                .await
                .map(Some),
            Work::InstallFloor(floor) => {
                recovery::install_floor(&self.io, keeper, self.stream, self.epoch, floor)
                    .await
                    .map(Some)
            }
            Work::Append {
                at,
                payloads,
                limit,
                head,
            } => {
                let (payloads, head) = match payloads {
                    Some(payloads) => (payloads, head),
                    None => {
                        let run = self.fetch_committed(at, index, limit).await?;
                        // The fetched run is committed. Lane bookkeeping keeps the lower
                        // `head` from the work item, which costs at most an extra publish.
                        let last = Lsn(at.0 + run.len() as u64 - 1);
                        (
                            run,
                            Lsn(append_head(self.state.lock().proposer.head().0, last.0)).max(head),
                        )
                    }
                };
                let last = Lsn(at.0 + payloads.len() as u64 - 1);
                let observed = self.observe(index);
                let result = self.send_append(keeper, at, payloads, head).await;
                observed.send_replace(Some(result.clone()));
                // After a lost reply the keeper can already hold more of this writer's
                // records than the retry carried. Those positions stay assigned, so
                // its tail is accepted up to the highest known position.
                result.map(|tail| Some(self.state.lock().proposer.accepted_tail(tail, last)))
            }
            Work::Publish(head) => {
                let observed = self.observe(index);
                let result = self.io.publish(keeper, self.stream, self.epoch, head).await;
                observed.send_replace(Some(result.clone()));
                result.map(|_| None)
            }
        }
    }

    fn observe(&self, index: usize) -> watch::Sender<Option<Result<Lsn>>> {
        let (send, receive) = watch::channel(None);
        let mut state = self.state.lock();
        let serial = state.proposer.mark_sent();
        state.observations[index] = Some((serial, receive));
        send
    }

    /// Fetch a contiguous committed run from `at`, up to the writer's head.
    async fn fetch_committed(&self, at: Lsn, index: usize, limit: usize) -> Result<Vec<Entry>> {
        let sources = self.state.lock().proposer.recover(at, index, limit)?;
        let mut fetches =
            FuturesUnordered::from_iter(self.ensemble.into_iter().zip(sources).filter_map(
                |(keeper, max)| {
                    max.map(|max| {
                        recovery::fetch_run(&self.io, keeper, self.stream, self.epoch, at, max)
                    })
                },
            ));
        while let Some(result) = fetches.next().await {
            if let Ok(payload) = result {
                return Ok(payload);
            }
        }
        Err(JournalError::Unavailable)
    }

    async fn send_append(
        &self,
        keeper: KeeperId,
        at: Lsn,
        entries: Vec<Entry>,
        head: Lsn,
    ) -> Result<Lsn> {
        let last = Lsn(at.0 + entries.len() as u64 - 1);
        let request = match entries.as_slice() {
            [Entry::Timed { evidence, payload }] => {
                let original = evidence.origin.original;
                if original.stream != self.stream
                    || original.epoch != self.epoch
                    || original.at != at
                {
                    return Err(JournalError::Unavailable);
                }
                Request::AppendOriginal {
                    stream: self.stream,
                    evidence: evidence.clone(),
                    payload: payload.clone(),
                    head,
                }
            }
            _ => Request::Append {
                stream: self.stream,
                epoch: self.epoch,
                at,
                records: entries
                    .into_iter()
                    .map(|entry| match entry {
                        Entry::Ordinary(bytes) => Ok(bytes),
                        _ => Err(JournalError::Unavailable),
                    })
                    .collect::<Result<_>>()?,
                head,
            },
        };
        match self.io.call(keeper, request).await? {
            Reply::Appended { tail } if tail >= last => Ok(tail),
            _ => Err(JournalError::Unavailable),
        }
    }
}

async fn replicate(active: Weak<Active>, index: usize, mut change: watch::Receiver<()>) {
    loop {
        change.borrow_and_update();
        let Some(current) = active.upgrade() else {
            return;
        };
        let next = current
            .state
            .lock()
            .proposer
            .dispatch(index, current.io.append_records);
        let Some((work, flight)) = next else {
            drop(current);
            if change.changed().await.is_err() {
                return;
            }
            continue;
        };
        let result = current.run(index, work).await;
        let mut state = current.state.lock();
        let completions = state.proposer.receive(current.epoch, index, flight, result);
        state.complete(completions);
        current.wake();
    }
}
