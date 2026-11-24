//! A durable keeper for many streams. The keeper serializes decisions and WAL rounds.
mod checkpoint;
mod durability;
mod legacy;
#[cfg(test)]
pub(super) mod memory;
mod rules;
mod state;
mod sweep;

mod wal;

pub use rules::Limits;
pub use sweep::{Sweep, SweepError, sweep_idle};

use std::{
    collections::{HashMap, HashSet, VecDeque},
    io,
    path::Path,
    sync::Arc,
    time::Duration,
};

use bytes::{Bytes, BytesMut};
use tokio::sync::{mpsc, oneshot, watch};

use self::{
    rules::Decision,
    state::Stream,
    wal::{FRAME_OVERHEAD, MAX_IDENTITY_BYTES, Wal},
};
use super::{codec, wire::*};

type CallResult = Result<Reply, TransportError>;

/// Optional policy for the authenticated certificate identity.
pub trait SealPolicy: Send + Sync + 'static {
    fn allow(&self, identity: &Identity, stream: StreamId, epoch: Epoch) -> bool;
}

impl<F> SealPolicy for F
where
    F: Fn(&Identity, StreamId, Epoch) -> bool + Send + Sync + 'static,
{
    fn allow(&self, identity: &Identity, stream: StreamId, epoch: Epoch) -> bool {
        self(identity, stream, epoch)
    }
}

struct Allow;
impl SealPolicy for Allow {
    fn allow(&self, _: &Identity, _: StreamId, _: Epoch) -> bool {
        true
    }
}

#[derive(Clone)]
pub struct Keeper {
    /// Each item is one envelope: a single request, or every request of a batch.
    work: mpsc::Sender<Vec<Work>>,
}

impl Keeper {
    pub fn open(path: &Path, keeper: KeeperId, limits: Limits) -> io::Result<Self> {
        Self::open_with_policy(path, keeper, limits, Arc::new(Allow))
    }

    pub fn open_with_policy(
        path: &Path,
        keeper: KeeperId,
        limits: Limits,
        policy: Arc<dyn SealPolicy>,
    ) -> io::Result<Self> {
        let engine = Engine::open(path, keeper, limits, policy)?;
        let (work, incoming) = mpsc::channel::<Vec<Work>>(limits.round_requests);
        std::thread::Builder::new()
            .name("stream-keeper-wal".into())
            .spawn(move || {
                if let Err(error) = engine.run(incoming) {
                    eprintln!("stream keeper WAL stopped: {error}");
                }
            })?;
        Ok(Self { work })
    }

    /// Process one request from an already authenticated identity. A `Batch` is
    /// admitted to a single round and answered with one reply per request, in order.
    pub async fn call(&self, identity: &Identity, request: Request) -> CallResult {
        if identity.as_str().is_empty() || identity.as_str().len() > MAX_IDENTITY_BYTES {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        }
        let Request::Batch(requests) = request else {
            let (work, result) = Work::new(identity, request.clone());
            self.work
                .send(vec![work])
                .await
                .map_err(|_| TransportError::Unreachable)?;
            return self.finish(identity, request, result).await;
        };
        if requests.is_empty() || requests.iter().any(|r| matches!(r, Request::Batch(_))) {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        }
        let (works, results): (Vec<_>, Vec<_>) = requests
            .iter()
            .map(|request| Work::new(identity, request.clone()))
            .unzip();
        self.work
            .send(works)
            .await
            .map_err(|_| TransportError::Unreachable)?;
        let replies = futures::future::join_all(
            requests
                .into_iter()
                .zip(results)
                .map(|(request, result)| self.finish(identity, request, result)),
        )
        .await;
        Ok(Reply::Batch(replies.into_iter().collect::<Result<_, _>>()?))
    }

    /// Wait for a request's first decision. A waiting read resubmits itself alone.
    async fn finish(
        &self,
        identity: &Identity,
        mut request: Request,
        result: oneshot::Receiver<Response>,
    ) -> CallResult {
        let wait = match request {
            Request::Read { wait_ms, .. } => Duration::from_millis(u64::from(wait_ms)),
            _ => Duration::ZERO,
        };
        let deadline = tokio::time::Instant::now() + wait;
        let mut result = result;
        loop {
            let (reply, changed) = result.await.map_err(|_| TransportError::Unreachable)?;
            let Some(mut changed) = changed else {
                return reply;
            };
            match tokio::time::timeout_at(deadline, changed.changed()).await {
                Ok(Ok(())) => {}
                Ok(Err(_)) => return Err(TransportError::Unreachable),
                Err(_) => {
                    // Sample once more at the deadline in case a head raced the timer.
                    if let Request::Read { wait_ms, .. } = &mut request {
                        *wait_ms = 0;
                    }
                }
            }
            let (work, next) = Work::new(identity, request.clone());
            self.work
                .send(vec![work])
                .await
                .map_err(|_| TransportError::Unreachable)?;
            result = next;
        }
    }
}

/// A round admits whole envelopes until it holds `round_requests` requests, so every
/// request of a batch is decided and synced in the same round.
fn admit(
    first: Vec<Work>,
    incoming: &mut mpsc::Receiver<Vec<Work>>,
    round_requests: usize,
) -> VecDeque<Work> {
    let mut pending = VecDeque::from(first);
    while pending.len() < round_requests {
        let Ok(work) = incoming.try_recv() else {
            break;
        };
        pending.extend(work);
    }
    pending
}

type Response = (CallResult, Option<watch::Receiver<()>>);
type Done = oneshot::Sender<Response>;

struct Work {
    request: Request,
    identity: Identity,
    done: Done,
    pending: Option<(Bytes, usize)>,
}

impl Work {
    fn new(identity: &Identity, request: Request) -> (Self, oneshot::Receiver<Response>) {
        let (done, result) = oneshot::channel();
        let work = Self {
            identity: identity.clone(),
            request,
            done,
            pending: None,
        };
        (work, result)
    }

    fn seal_identity(&self) -> Option<&Identity> {
        matches!(self.request, Request::Seal { .. }).then_some(&self.identity)
    }

    fn is_mutation(&self) -> bool {
        !matches!(
            self.request,
            Request::Check { .. } | Request::Read { .. } | Request::Recover { .. }
        )
    }
}

struct Engine {
    keeper: KeeperId,
    limits: Limits,
    policy: Arc<dyn SealPolicy>,
    wal: Wal,
    streams: HashMap<StreamId, Stream>,
    deletions: HashMap<StreamId, Vec<Done>>,
    rotating_deletions: HashMap<StreamId, Vec<Done>>,
    recovering: bool,
}

impl Engine {
    fn open(
        path: &Path,
        keeper: KeeperId,
        limits: Limits,
        policy: Arc<dyn SealPolicy>,
    ) -> io::Result<Self> {
        if keeper.0 == 0
            || limits.round_bytes_per_stream <= FRAME_OVERHEAD
            || !(1..=tokio::sync::Semaphore::MAX_PERMITS).contains(&limits.round_requests)
            || !rules::valid_limits(&limits)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid keeper identity or byte limits",
            ));
        }
        let (wal, streams) = Wal::open(path, keeper)?;
        Ok(Self {
            keeper,
            limits,
            policy,
            wal,
            streams,
            deletions: HashMap::new(),
            rotating_deletions: HashMap::new(),
            recovering: false,
        })
    }

    fn run(mut self, mut incoming: mpsc::Receiver<Vec<Work>>) -> io::Result<()> {
        self.maintain()?;
        loop {
            let event = futures::executor::block_on(async {
                tokio::select! {
                    biased;
                    _ = self.wal.rotation_ready() => Some(None),
                    first = incoming.recv() => first.map(Some),
                }
            });
            match event {
                Some(Some(first)) => {
                    if first.iter().any(Work::is_mutation) {
                        std::thread::sleep(Duration::from_micros(200));
                    }
                    self.process(admit(first, &mut incoming, self.limits.round_requests))?;
                }
                Some(None) => {
                    self.complete_rotation()?;
                    self.maintain()?;
                }
                None => return Ok(()),
            }
        }
    }

    fn complete_rotation(&mut self) -> io::Result<()> {
        self.wal.finish_rotation()?;
        self.recovering = false;
        for done in std::mem::take(&mut self.rotating_deletions)
            .into_values()
            .flatten()
        {
            let _ = done.send((Ok(Reply::Deleted), None));
        }
        Ok(())
    }

    #[cfg(test)]
    fn drain_checkpoints(&mut self) -> io::Result<()> {
        while self.wal.rotating() {
            self.complete_rotation()?;
            self.maintain()?;
        }
        Ok(())
    }

    fn maintain(&mut self) -> io::Result<()> {
        if self.wal.rotation_finished() {
            self.complete_rotation()?;
        }
        if !self.wal.rotating()
            && (self.wal.bootstrap
                || !self.deletions.is_empty()
                || self.wal.uncheckpointed >= wal::SEGMENT_BYTES - FRAME_OVERHEAD as u64)
        {
            self.recovering = self.wal.bootstrap;
            self.wal
                .start_rotation(&self.streams, !self.deletions.is_empty())?;
            self.rotating_deletions = std::mem::take(&mut self.deletions);
        }
        Ok(())
    }

    fn process(&mut self, mut pending: VecDeque<Work>) -> io::Result<()> {
        self.maintain()?;
        // Bound the WAL suffix even if compaction runs slowly. Finish the admitted
        // work, then ask new mutations to retry while observations keep advancing.
        let backlogged = self.wal.uncheckpointed >= wal::MAX_WAL_SUFFIX_BYTES;
        while !pending.is_empty() {
            if self.wal.remaining() <= FRAME_OVERHEAD {
                self.wal.roll_segment()?;
            }
            self.round(&mut pending, backlogged)?;
        }
        self.maintain()
    }

    /// Decide and buffer in arrival order per stream. Other streams can advance while a
    /// large mutation is fragmented. A round publishes all its results after one sync.
    fn round(&mut self, pending: &mut VecDeque<Work>, backlogged: bool) -> io::Result<()> {
        let mut buffer = BytesMut::new();
        let mut charged = HashMap::<StreamId, usize>::new();
        let mut blocked = HashSet::new();
        let mut changed = HashSet::new();
        let mut replies = Vec::new();
        for mut work in std::mem::take(pending) {
            let id = codec::stream(&work.request);
            if blocked.contains(&id) {
                pending.push_back(work);
                continue;
            }
            if work.pending.is_none() {
                let state = self.streams.get(&id);
                let seal_allowed = match work.request {
                    Request::Seal { epoch, .. } => self.policy.allow(&work.identity, id, epoch),
                    _ => true,
                };
                match state::decide(
                    state,
                    self.keeper,
                    &work.request,
                    &work.identity,
                    seal_allowed,
                    &self.limits,
                    &mut self.wal.reader,
                )? {
                    Decision::Reply(Reply::Deleted) => {
                        if let Some(waiting) = self.deletions.get_mut(&id) {
                            waiting.push(work.done);
                        } else if self.recovering || self.rotating_deletions.contains_key(&id) {
                            self.rotating_deletions
                                .entry(id)
                                .or_default()
                                .push(work.done);
                        } else {
                            replies.push((work.done, (Ok(Reply::Deleted), None)));
                        }
                        continue;
                    }
                    Decision::Reply(reply) => {
                        replies.push((work.done, (Ok(reply), None)));
                        continue;
                    }
                    Decision::Page { through } => {
                        let state = state.expect("page has state");
                        let (from, max, wait) = match work.request {
                            Request::Recover { from, max, .. } => (from, max, false),
                            Request::Read {
                                from, max, wait_ms, ..
                            } => (from, max, wait_ms != 0),
                            _ => unreachable!(),
                        };
                        let changed =
                            (wait && max != 0 && from > through).then(|| state.changed.subscribe());
                        let reply = state.page(from, max, through, &mut self.wal.reader)?;
                        replies.push((work.done, (Ok(reply), changed)));
                        continue;
                    }
                    Decision::Persist if backlogged => {
                        replies.push((work.done, (Err(TransportError::TimedOut), None)));
                        continue;
                    }
                    Decision::Persist => {}
                }
            }

            let charge = charged.entry(id).or_default();
            let budget = (self.limits.round_bytes_per_stream - *charge)
                .min(self.wal.remaining() - buffer.len());
            if budget <= FRAME_OVERHEAD {
                blocked.insert(id);
                pending.push_back(work);
                continue;
            }
            if work.pending.is_none() {
                let identity = work.seal_identity();
                match wal::entry(&work.request, identity) {
                    Ok(entry) => work.pending = Some((entry, 0)),
                    Err(error) => {
                        replies.push((
                            work.done,
                            (Err(TransportError::Protocol(error.to_string())), None),
                        ));
                        continue;
                    }
                }
            }
            let (entry, offset) = work.pending.as_mut().expect("mutation encoded");
            let end = *offset + (budget - FRAME_OVERHEAD).min(entry.len() - *offset);
            let last = end == entry.len();
            wal::fragment(&mut buffer, id, *offset == 0, last, &entry[*offset..end]);
            *charge += FRAME_OVERHEAD + end - *offset;
            *offset = end;
            if !last {
                blocked.insert(id);
                pending.push_back(work);
                continue;
            }

            let identity = work.seal_identity().cloned();
            let reply =
                self.streams
                    .entry(id)
                    .or_default()
                    .apply(self.keeper, work.request, identity)?;
            self.wal.dirty.insert(id);
            changed.insert(id);
            if reply == Reply::Deleted {
                self.deletions.entry(id).or_default().push(work.done);
            } else {
                replies.push((work.done, (Ok(reply), None)));
            }
        }
        self.wal.write_round(&buffer)?;
        for id in changed {
            self.streams[&id].changed.send_replace(());
        }
        for (done, reply) in replies {
            let _ = done.send(reply);
        }
        Ok(())
    }
}

#[cfg(test)]
mod simulation;
#[cfg(test)]
mod tests;
