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
    decision::acknowledged,
    quorum,
    recovery::{self, Recovery},
    refusal,
};

type Sender = oneshot::Sender<Result<Lsn>>;
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
    commit: Lsn,
    floor: Lsn,
    pending: BTreeMap<Lsn, Pending>,
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
    Append {
        at: Lsn,
        payload: Option<Bytes>,
        commit: Lsn,
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
                commit: recovery.end(),
                floor: recovery.floor,
                pending: BTreeMap::new(),
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

    pub(super) fn commit(&self) -> Lsn {
        self.state.lock().commit
    }

    pub(super) async fn published(&self, end: Lsn) -> Result<()> {
        if end == Lsn(0) {
            return Ok(());
        }
        let mut change = self.change.subscribe();
        loop {
            {
                let state = self.state.lock();
                if let Some(error) = &state.closed {
                    return Err(error.clone());
                }
                if state
                    .lanes
                    .iter()
                    .filter(|lane| lane.published.is_some_and(|at| at >= end))
                    .count()
                    >= QUORUM
                {
                    return Ok(());
                }
                if let Some(error) = state.impossible(Lsn(end.0 + 1)) {
                    return Err(error);
                }
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
                if at <= state.commit {
                    break None;
                }
                let last = state
                    .pending
                    .last_key_value()
                    .map_or(state.commit, |(at, _)| *at);
                let conflict = JournalError::Conflict {
                    committed_end: state.commit,
                };
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
                    return Err(conflict);
                }
            }
            // A competing live append can choose this position. Wait for that
            // decision before reporting the committed end in a conflict.
            change
                .changed()
                .await
                .map_err(|_| JournalError::Unavailable)?;
        };
        match wait {
            Some(wait) => {
                let at = wait.await.unwrap_or(Err(JournalError::Unavailable))?;
                // An observer can read the choice immediately after we acknowledge it.
                self.published(at).await?;
                Ok(at)
            }
            None => self.retry_committed(at, payload).await,
        }
    }

    async fn retry_committed(&self, at: Lsn, payload: Bytes) -> Result<Lsn> {
        let commit = self.commit();
        quorum(FuturesUnordered::from_iter(self.ensemble.map(|keeper| {
            self.send_append(keeper, at, payload.clone(), commit)
        })))
        .await
        .map(|_| at)
        .map_err(|error| match error {
            JournalError::Conflict { .. } => JournalError::Conflict {
                committed_end: self.commit(),
            },
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
            .filter(|(serial, _)| *serial > after)
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
                if state.commit >= sample {
                    return Ok(state.commit);
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
                payload,
                commit,
            } => {
                let payload = match payload {
                    Some(payload) => payload,
                    None => self.fetch_committed(at, index).await?,
                };
                let observed = self.observe(index);
                let result = self.send_append(keeper, at, payload, commit).await;
                observed.send_replace(Some(result.clone()));
                result.map(|_| Some(at))
            }
            Work::Publish(commit) => {
                let observed = self.observe(index);
                let result = self
                    .io
                    .publish(keeper, self.stream, self.epoch, commit)
                    .await;
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

    async fn fetch_committed(&self, at: Lsn, index: usize) -> Result<Bytes> {
        let source = {
            let state = self.state.lock();
            if at < state.floor {
                return Err(JournalError::Trimmed { floor: state.floor });
            }
            std::array::from_fn::<_, 3, _>(|i| {
                (i != index && state.lanes[i].accepted.is_some_and(|end| end >= at))
                    .then_some(self.ensemble[i])
            })
        };
        let mut fetches = FuturesUnordered::from_iter(
            source
                .into_iter()
                .flatten()
                .map(|keeper| recovery::fetch(&self.io, keeper, self.stream, self.epoch, at)),
        );
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
        payload: Bytes,
        commit: Lsn,
    ) -> Result<Lsn> {
        match self
            .io
            .call(
                keeper,
                Request::Append {
                    stream: self.stream,
                    epoch: self.epoch,
                    holder: self.io.holder,
                    at,
                    records: vec![payload],
                    commit,
                },
            )
            .await?
        {
            Reply::Appended { end } if end >= at => Ok(end),
            _ => Err(JournalError::Unavailable),
        }
    }
}

impl State {
    fn work(&self, index: usize) -> Option<Work> {
        let lane = &self.lanes[index];
        if self.closed.is_some()
            || lane
                .failure
                .as_ref()
                .is_some_and(|f| f.revision == self.revision)
        {
            return None;
        }
        let Some(end) = lane.accepted else {
            return Some(Work::Sync(self.floor));
        };
        if !self.enabled {
            return None;
        }
        let at = Lsn(end.0 + 1);
        if lane.floor.is_none_or(|floor| floor < self.floor) {
            return Some(Work::InstallFloor(self.floor));
        }
        let pending = self.pending.get(&at);
        if pending.is_some() || at <= self.commit {
            return Some(Work::Append {
                at,
                payload: pending.map(|p| p.payload.clone()),
                commit: self.commit.min(at),
            });
        }
        if lane
            .published
            .is_none_or(|published| published < self.commit)
        {
            return Some(Work::Publish(self.commit));
        }
        None
    }

    fn impossible(&self, at: Lsn) -> Option<JournalError> {
        let errors: Vec<_> = self
            .lanes
            .iter()
            .filter_map(|lane| {
                lane.failure
                    .as_ref()
                    .filter(|f| f.revision == self.revision && f.at <= at)
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
            .map(|lane| lane.accepted.map(|end| (epoch.0, end.0)));
        while let Some((&at, _)) = self.pending.first_key_value() {
            if !acknowledged(a, b, c, epoch.0, at.0) {
                break;
            }
            self.commit = at;
            notify(&mut self.pending.pop_first().unwrap().1, Ok(at));
        }
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
                JournalError::Conflict { .. } => JournalError::Conflict {
                    committed_end: self.commit,
                },
                error => error,
            };
            notify(self.pending.get_mut(&at).unwrap(), Err(error));
        }
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
            (state.work(index), state.revision)
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
            Work::Append { at, commit, .. } => (*at, *commit, None),
            Work::Publish(commit) => (Lsn(commit.0 + 1), *commit, None),
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
                    if let Some(end) = accepted {
                        lane.accepted = Some(end);
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
