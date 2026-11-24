//! One ordered append pipeline per keeper. A slow keeper never delays a quorum.

use std::{
    collections::BTreeMap,
    sync::{Arc, Weak},
};

use bytes::Bytes;
use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Result, StreamId};
use parking_lot::Mutex;
use tokio::sync::{oneshot, watch};

use super::{
    Io, KeeperId, QUORUM, Reply, Request, Stream,
    decision::{accepted_tail, acknowledged, append_head, fresh_sample},
    quorum,
    recovery::{self, Recovery},
    refusal,
};

type Sender = oneshot::Sender<Result<Lsn>>;

/// Bounds on the contiguous pending records one lane sends in a single keeper append.
/// A batch below the transport's shared-connection threshold is coalesced with other streams.
pub(super) const APPEND_RECORDS: usize = 1024;
const APPEND_BYTES: usize = 512 * 1024;
/// Committed payloads kept for lanes that have not yet accepted them, per stream.
const RETAIN_BYTES: usize = 1024 * 1024;
type Observation = watch::Receiver<Option<Result<Lsn>>>;

pub(super) struct Active {
    pub(super) epoch: Epoch,
    io: Arc<Io>,
    stream: StreamId,
    ensemble: [KeeperId; 3],
    recovery: Recovery,
    state: Mutex<State>,
    change: watch::Sender<()>,
}

struct State {
    enabled: bool,
    closed: Option<JournalError>,
    head: Lsn,
    floor: Lsn,
    pending: BTreeMap<Lsn, Pending>,
    /// Chosen payloads that some lane may still need. Bounded by `RETAIN_BYTES`.
    committed: BTreeMap<Lsn, Bytes>,
    committed_bytes: usize,
    lanes: [Lane; 3],
    revision: u64,
    serial: u64,
}

#[derive(Default)]
struct Lane {
    accepted: Option<Lsn>,
    published: Option<Lsn>,
    floor: Option<Lsn>,
    failure: Option<Failure>,
    observation: Option<(u64, Observation)>,
}

struct Failure {
    revision: u64,
    at: Lsn,
    error: JournalError,
}

struct Pending {
    payload: Bytes,
    waiters: Vec<Sender>,
}

enum Work {
    Sync(Lsn),
    InstallFloor(Lsn),
    /// `payloads` is the contiguous known run from `at`, or `None` to fetch up to
    /// `limit` committed records that this lane lacks.
    Append {
        at: Lsn,
        payloads: Option<Vec<Bytes>>,
        limit: usize,
        head: Lsn,
    },
    Publish(Lsn),
}

impl Active {
    pub(super) fn start(io: Arc<Io>, stream: &Stream, recovery: Recovery) -> Arc<Self> {
        let active = Arc::new(Self {
            epoch: recovery.epoch,
            io,
            stream: stream.id,
            ensemble: stream.ensemble,
            state: Mutex::new(State {
                enabled: false,
                closed: None,
                head: recovery.tail(),
                floor: recovery.floor,
                pending: BTreeMap::new(),
                committed: BTreeMap::new(),
                committed_bytes: 0,
                lanes: std::array::from_fn(|_| Lane::default()),
                revision: 0,
                serial: 0,
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
            {
                let mut state = self.state.lock();
                if state
                    .lanes
                    .iter()
                    .filter(|lane| lane.accepted.is_some())
                    .count()
                    >= QUORUM
                {
                    state.enabled = true;
                    self.wake();
                    return Ok(());
                }
                if let Some(error) = state.impossible(Lsn(0)) {
                    return Err(error);
                }
            }
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        }
    }

    pub(super) fn head(&self) -> Lsn {
        self.state.lock().head
    }

    pub(super) async fn published(&self, tail: Lsn) -> Result<()> {
        if tail == Lsn(0) {
            return Ok(());
        }
        let mut change = self.change.subscribe();
        loop {
            if let Some(result) = self.state.lock().publication(tail) {
                return result;
            }
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        }
    }

    pub(super) fn trim(&self, floor: Lsn) {
        let mut state = self.state.lock();
        state.floor = state.floor.max(floor);
        state.revision += 1;
        self.wake();
    }

    pub(super) fn close(&self, error: JournalError) {
        let mut state = self.state.lock();
        state.closed = Some(error.clone());
        for pending in state.pending.values_mut() {
            notify(pending, Err(error.clone()));
        }
        self.wake();
    }

    pub(super) async fn append(&self, at: Lsn, payload: Bytes) -> Result<Lsn> {
        let mut change = self.change.subscribe();
        let wait = loop {
            {
                let mut state = self.state.lock();
                if let Some(error) = &state.closed {
                    return Err(error.clone());
                }
                if at < state.floor {
                    return Err(JournalError::Trimmed { floor: state.floor });
                }
                if at <= state.head {
                    // A retry can arrive after an unavailable keeper has returned.
                    // Wake its lane so it can catch up using the chosen payload.
                    state.revision += 1;
                    self.wake();
                    break None;
                }
                let last = state
                    .pending
                    .last_key_value()
                    .map_or(state.head, |(at, _)| *at);
                let conflict = JournalError::Conflict { head: state.head };
                if at.0 == u64::MAX || at.0 > last.0 + 1 {
                    return Err(conflict);
                }
                let pending = state.pending.entry(at).or_insert_with(|| Pending {
                    payload: payload.clone(),
                    waiters: Vec::new(),
                });
                if pending.payload == payload {
                    let (send, wait) = oneshot::channel();
                    pending.waiters.push(send);
                    state.revision += 1;
                    self.wake();
                    break Some(wait);
                }
                if pending.waiters.is_empty() {
                    // A prior attempt may have accepted these bytes without deciding
                    // the position. Only a chosen record can resolve the conflict.
                    return Err(match state.impossible(at) {
                        Some(error @ JournalError::Fenced { .. }) => error,
                        _ => JournalError::Unavailable,
                    });
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
            Some(wait) => {
                let at = wait.await.unwrap_or(Err(JournalError::Unavailable))?;
                // An observer can read the choice immediately after we acknowledge it.
                self.published(at)
                    .await
                    .map_err(|_| JournalError::Unavailable)?;
                Ok(at)
            }
            None => self.retry_committed(at, payload).await,
        }
    }

    async fn retry_committed(&self, at: Lsn, payload: Bytes) -> Result<Lsn> {
        // Check retained bytes before publishing. Caller-supplied bytes are never
        // sent in a lane Append until the writer has assigned them a position.
        let accepted = {
            let state = self.state.lock();
            std::array::from_fn::<_, 3, _>(|index| {
                state.lanes[index]
                    .accepted
                    .is_some_and(|tail| tail >= at)
                    .then_some(self.ensemble[index])
            })
        };
        quorum(FuturesUnordered::from_iter(
            accepted.into_iter().flatten().map(|keeper| {
                let payload = &payload;
                async move {
                    let retained =
                        recovery::fetch(&self.io, keeper, self.stream, self.epoch, at).await?;
                    if retained != *payload {
                        return Err(JournalError::Conflict { head: self.head() });
                    }
                    self.io.publish(keeper, self.stream, self.epoch, at).await
                }
            }),
        ))
        .await
        .map(|_| at)
        .map_err(|error| match error {
            JournalError::Conflict { .. } => JournalError::Conflict { head: self.head() },
            error => error,
        })
    }

    fn wake(&self) {
        self.change.send_replace(());
    }

    pub(super) fn open_round(&self) -> u64 {
        self.state.lock().serial
    }

    pub(super) fn observation(&self, lane: usize, after: u64) -> Option<Observation> {
        self.state.lock().lanes[lane]
            .observation
            .as_ref()
            .filter(|(serial, _)| fresh_sample(after, *serial))
            .map(|(_, result)| result.clone())
    }

    pub(super) async fn cover(&self, sample: Lsn) -> Result<Lsn> {
        let mut change = self.change.subscribe();
        loop {
            {
                let state = self.state.lock();
                if let Some(error) = &state.closed {
                    return Err(error.clone());
                }
                if state.head >= sample {
                    return Ok(state.head);
                }
                if !state.pending.contains_key(&sample) {
                    return Err(JournalError::Unavailable);
                }
                if let Some(error) = state.impossible(sample) {
                    return Err(error);
                }
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
            Work::Sync(floor) => self
                .recovery
                .sync(&self.io, self.stream, self.ensemble, keeper, floor)
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
                            Lsn(append_head(self.state.lock().head.0, last.0)).max(head),
                        )
                    }
                };
                let last = Lsn(at.0 + payloads.len() as u64 - 1);
                let observed = self.observe(index);
                let result = self.send_append(keeper, at, payloads, head).await;
                observed.send_replace(Some(result.clone()));
                // After a lost reply the keeper can already hold more of this writer's
                // records than the retry carried. Positions are never reassigned within
                // an epoch, so its tail is accepted up to the highest known position.
                let known = {
                    let state = self.state.lock();
                    state
                        .pending
                        .last_key_value()
                        .map_or(state.head, |(at, _)| *at)
                };
                result.map(|tail| Some(Lsn(accepted_tail(tail.0, known.0, last.0))))
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
        state.serial += 1;
        let serial = state.serial;
        state.lanes[index].observation = Some((serial, receive));
        send
    }

    /// Fetch a contiguous committed run from `at`, up to the writer's head.
    async fn fetch_committed(&self, at: Lsn, index: usize, limit: usize) -> Result<Vec<Bytes>> {
        let (source, max) = {
            let state = self.state.lock();
            if at < state.floor {
                return Err(JournalError::Trimmed { floor: state.floor });
            }
            let committed = (state.head.0 - at.0 + 1).min(limit.max(1) as u64);
            let source = std::array::from_fn::<_, 3, _>(|i| {
                (i != index && state.lanes[i].accepted.is_some_and(|tail| tail >= at))
                    .then(|| (self.ensemble[i], state.lanes[i].accepted.unwrap()))
            });
            (source, committed)
        };
        let mut fetches =
            FuturesUnordered::from_iter(source.into_iter().flatten().map(|(keeper, accepted)| {
                let max = max.min(accepted.0 - at.0 + 1) as u32;
                recovery::fetch_run(&self.io, keeper, self.stream, self.epoch, at, max)
            }));
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
        records: Vec<Bytes>,
        head: Lsn,
    ) -> Result<Lsn> {
        let last = Lsn(at.0 + records.len() as u64 - 1);
        match self
            .io
            .call(
                keeper,
                Request::Append {
                    stream: self.stream,
                    epoch: self.epoch,
                    at,
                    records,
                    head,
                },
            )
            .await?
        {
            Reply::Appended { tail } if tail >= last => Ok(tail),
            _ => Err(JournalError::Unavailable),
        }
    }
}

impl State {
    fn work(&self, index: usize, records: usize) -> Option<Work> {
        let lane = &self.lanes[index];
        if self.closed.is_some()
            || lane
                .failure
                .as_ref()
                .is_some_and(|f| f.revision == self.revision)
        {
            return None;
        }
        let Some(tail) = lane.accepted else {
            return Some(Work::Sync(self.floor));
        };
        if !self.enabled {
            return None;
        }
        let at = Lsn(tail.0 + 1);
        if lane.floor.is_none_or(|floor| floor < self.floor) {
            return Some(Work::InstallFloor(self.floor));
        }
        if self.pending.contains_key(&at) || at <= self.head {
            // A retry after an uncertain outcome carries one record. The keeper verifies
            // it against its history instead of refusing a range that overlaps its tail.
            let limit = if lane.failure.is_some() { 1 } else { records };
            let payloads = Some(self.run_from(at, limit)).filter(|run| !run.is_empty());
            let last = Lsn(at.0 + payloads.as_ref().map_or(1, Vec::len) as u64 - 1);
            return Some(Work::Append {
                at,
                payloads,
                limit,
                head: Lsn(append_head(self.head.0, last.0)),
            });
        }
        if lane.published.is_none_or(|published| published < self.head) {
            return Some(Work::Publish(self.head));
        }
        None
    }

    /// The contiguous retained and pending payloads from `at`, within one append's bounds.
    fn run_from(&self, at: Lsn, records: usize) -> Vec<Bytes> {
        let mut bytes = 0;
        let mut next = at;
        let mut payloads = Vec::new();
        let known = self
            .committed
            .range(at..)
            .chain(self.pending.range(at..).map(|(lsn, p)| (lsn, &p.payload)));
        for (&lsn, payload) in known {
            if lsn != next
                || payloads.len() == records.max(1)
                || (!payloads.is_empty() && bytes + payload.len() > APPEND_BYTES)
            {
                break;
            }
            bytes += payload.len();
            payloads.push(payload.clone());
            next = Lsn(lsn.0 + 1);
        }
        payloads
    }

    /// Forget committed payloads that every lane has accepted, that lie below the floor,
    /// or that exceed the retention bound. A lane that still needs them fetches them.
    fn release_committed(&mut self) {
        let accepted = self
            .lanes
            .iter()
            .map(|lane| lane.accepted.unwrap_or(Lsn(0)))
            .min()
            .unwrap();
        while let Some((&lsn, payload)) = self.committed.first_key_value() {
            if lsn > accepted && lsn >= self.floor && self.committed_bytes <= RETAIN_BYTES {
                break;
            }
            self.committed_bytes -= payload.len();
            self.committed.pop_first();
        }
    }

    fn impossible(&self, at: Lsn) -> Option<JournalError> {
        self.failed(|_, failure| failure.at <= at)
    }

    fn publication(&self, tail: Lsn) -> Option<Result<()>> {
        if let Some(error) = &self.closed {
            return Some(Err(error.clone()));
        }
        let covered = |lane: &Lane| lane.published.is_some_and(|head| head >= tail);
        if self.lanes.iter().filter(|lane| covered(lane)).count() >= QUORUM {
            return Some(Ok(()));
        }
        // A failed later append can block a lane before it publishes this head.
        self.failed(|lane, _| !covered(lane)).map(Err)
    }

    fn failed(&self, blocked: impl Fn(&Lane, &Failure) -> bool) -> Option<JournalError> {
        let errors: Vec<_> = self
            .lanes
            .iter()
            .filter_map(|lane| {
                lane.failure
                    .as_ref()
                    .filter(|failure| failure.revision == self.revision && blocked(lane, failure))
                    .map(|f| f.error.clone())
            })
            .collect();
        if errors.len() >= QUORUM {
            Some(refusal(&errors))
        } else {
            None
        }
    }

    fn advance(&mut self, epoch: Epoch) {
        let [a, b, c] = self
            .lanes
            .each_ref()
            .map(|lane| lane.accepted.map(|tail| (epoch.0, tail.0)));
        while let Some((&at, _)) = self.pending.first_key_value() {
            if !acknowledged(a, b, c, epoch.0, at.0) {
                break;
            }
            self.head = at;
            let mut pending = self.pending.pop_first().unwrap().1;
            notify(&mut pending, Ok(at));
            self.committed_bytes += pending.payload.len();
            self.committed.insert(at, pending.payload);
        }
        self.release_committed();
    }

    fn fail_waiters(&mut self) {
        let Some((&first, _)) = self.pending.first_key_value() else {
            return;
        };
        let failed_at_first = self.lanes.iter().all(|lane| {
            lane.failure.as_ref().is_some_and(|failure| {
                failure.revision == self.revision
                    && failure.at == first
                    && matches!(
                        failure.error,
                        JournalError::Full { .. } | JournalError::TooLarge { .. }
                    )
            })
        });
        if failed_at_first {
            // A different payload is safe only if every keeper definitively refused this one.
            let error = self.impossible(first).unwrap();
            for (_, mut pending) in std::mem::take(&mut self.pending) {
                notify(&mut pending, Err(error.clone()));
            }
            return;
        }
        if let Some((&last, _)) = self.pending.last_key_value() {
            if self.impossible(last).is_none() {
                return;
            }
        }
        let failed: Vec<_> = self
            .pending
            .iter()
            .filter(|(_, pending)| !pending.waiters.is_empty())
            .filter_map(|(&at, _)| self.impossible(at).map(|error| (at, error)))
            .collect();
        for (at, error) in failed {
            let error = match error {
                JournalError::Conflict { .. } => JournalError::Conflict { head: self.head },
                error => error,
            };
            notify(self.pending.get_mut(&at).unwrap(), Err(error));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn publication_detects_a_lane_blocked_by_a_later_append() {
        let mut state = State {
            enabled: true,
            closed: None,
            head: Lsn(3),
            floor: Lsn(1),
            pending: BTreeMap::new(),
            committed: BTreeMap::new(),
            committed_bytes: 0,
            lanes: [
                Lane {
                    accepted: Some(Lsn(4)),
                    published: Some(Lsn(2)),
                    failure: Some(Failure {
                        revision: 1,
                        at: Lsn(5),
                        error: JournalError::Unavailable,
                    }),
                    ..Lane::default()
                },
                Lane {
                    accepted: Some(Lsn(3)),
                    published: Some(Lsn(3)),
                    ..Lane::default()
                },
                Lane {
                    failure: Some(Failure {
                        revision: 1,
                        at: Lsn(1),
                        error: JournalError::Unavailable,
                    }),
                    ..Lane::default()
                },
            ],
            revision: 1,
            serial: 0,
        };
        assert_eq!(
            state.publication(Lsn(3)),
            Some(Err(JournalError::Unavailable)),
            "pending publication must finish when both uncovered lanes are blocked"
        );
        state.revision += 1;
        assert_eq!(state.publication(Lsn(3)), None);
    }
}

fn notify(pending: &mut Pending, result: Result<Lsn>) {
    for waiter in pending.waiters.drain(..) {
        let _ = waiter.send(result.clone());
    }
}

async fn replicate(active: Weak<Active>, index: usize, mut change: watch::Receiver<()>) {
    loop {
        change.borrow_and_update();
        let Some(current) = active.upgrade() else {
            return;
        };
        let (work, revision) = {
            let state = current.state.lock();
            (state.work(index, current.io.append_records), state.revision)
        };
        let Some(work) = work else {
            drop(current);
            if change.changed().await.is_err() {
                return;
            }
            continue;
        };
        let (at, published, floor) = match &work {
            Work::Sync(floor) => (Lsn(0), Lsn(floor.0 - 1), Some(*floor)),
            Work::InstallFloor(floor) => (*floor, Lsn(floor.0 - 1), Some(*floor)),
            Work::Append { at, head, .. } => (*at, *head, None),
            Work::Publish(head) => (Lsn(head.0 + 1), *head, None),
        };
        let result = current.run(index, work).await;
        {
            let mut state = current.state.lock();
            if state.closed.is_some() {
                return;
            }
            let lane = &mut state.lanes[index];
            match result {
                Ok(accepted) => {
                    if let Some(tail) = accepted {
                        lane.accepted = Some(tail);
                    }
                    lane.published = lane.published.max(Some(published));
                    lane.floor = lane.floor.max(floor);
                    lane.failure = None;
                    state.advance(current.epoch);
                }
                Err(error) => {
                    lane.failure = Some(Failure {
                        revision,
                        at,
                        error,
                    });
                    state.fail_waiters();
                }
            }
            current.wake();
        }
    }
}
