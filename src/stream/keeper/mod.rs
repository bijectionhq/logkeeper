//! A durable keeper for many streams. The keeper serializes decisions and WAL rounds.
mod durability;
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
    rules::{Decision, StreamView},
    state::Stream,
    wal::{FRAME_OVERHEAD, MAX_PRINCIPAL, Wal},
};
use super::{codec, wire::*};

const ROUND_BYTES: usize = 16 * 1024 * 1024;
const WAVE_BYTES: usize = 64 * 1024 * 1024;
const WAVE_REQUESTS: usize = 64;
type CallResult = Result<Reply, TransportError>;

/// Nomination policy receives the authenticated certificate URI and proposed holder.
pub trait SealPolicy: Send + Sync + 'static {
    fn allow(&self, principal: &str, stream: StreamId, epoch: Epoch, holder: Holder) -> bool;
}

impl<F> SealPolicy for F
where
    F: Fn(&str, StreamId, Epoch, Holder) -> bool + Send + Sync + 'static,
{
    fn allow(&self, principal: &str, stream: StreamId, epoch: Epoch, holder: Holder) -> bool {
        self(principal, stream, epoch, holder)
    }
}

struct Allow;
impl SealPolicy for Allow {
    fn allow(&self, _: &str, _: StreamId, _: Epoch, _: Holder) -> bool {
        true
    }
}

#[derive(Clone)]
pub struct Keeper {
    work: mpsc::Sender<Work>,
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
        let mut engine = Engine::open(path, keeper, limits, policy)?;
        let (work, mut incoming) = mpsc::channel::<Work>(WAVE_REQUESTS);
        std::thread::Builder::new()
            .name("stream-keeper-wal".into())
            .spawn(move || {
                while let Some(first) = incoming.blocking_recv() {
                    let mut bytes = first.estimated_bytes();
                    let mut wave = VecDeque::from([first]);
                    if wave.front().is_some_and(|work| work.is_mutation()) {
                        std::thread::sleep(Duration::from_micros(200));
                    }
                    while wave.len() < WAVE_REQUESTS && bytes < WAVE_BYTES {
                        let Ok(work) = incoming.try_recv() else {
                            break;
                        };
                        bytes += work.estimated_bytes();
                        wave.push_back(work);
                    }
                    if let Err(error) = engine.process(wave) {
                        eprintln!("stream keeper WAL stopped: {error}");
                        return;
                    }
                }
            })?;
        Ok(Self { work })
    }

    /// Process one request from an already authenticated principal.
    pub async fn call(&self, principal: &str, mut request: Request) -> CallResult {
        if principal.is_empty() || principal.len() > MAX_PRINCIPAL {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        }
        let wait = match request {
            Request::Read { wait_ms, .. } => Duration::from_millis(u64::from(wait_ms)),
            _ => Duration::ZERO,
        };
        let deadline = tokio::time::Instant::now() + wait;
        let principal = Bytes::copy_from_slice(principal.as_bytes());
        loop {
            let (done, result) = oneshot::channel();
            self.work
                .send(Work {
                    principal: principal.clone(),
                    request: request.clone(),
                    done,
                    pending: None,
                })
                .await
                .map_err(|_| TransportError::Unreachable)?;
            let (reply, changed) = result.await.map_err(|_| TransportError::Unreachable)?;
            let Some(mut changed) = changed else {
                return reply;
            };
            match tokio::time::timeout_at(deadline, changed.changed()).await {
                Ok(Ok(())) => {}
                Ok(Err(_)) => return Err(TransportError::Unreachable),
                Err(_) => {
                    // Sample once more at the deadline in case a commit raced the timer.
                    if let Request::Read { wait_ms, .. } = &mut request {
                        *wait_ms = 0;
                    }
                }
            }
        }
    }
}

type Response = (CallResult, Option<watch::Receiver<()>>);
type Done = oneshot::Sender<Response>;

struct Work {
    request: Request,
    principal: Bytes,
    done: Done,
    pending: Option<(Bytes, usize)>,
}

impl Work {
    fn is_mutation(&self) -> bool {
        !matches!(
            self.request,
            Request::Check { .. } | Request::Read { .. } | Request::Recover { .. }
        )
    }

    fn estimated_bytes(&self) -> usize {
        128 + self.principal.len()
            + match &self.request {
                Request::Append { records, .. } => {
                    records.iter().map(|record| 4 + record.len()).sum()
                }
                Request::Sync { records, runs, .. } => {
                    runs.len() * 24 + records.iter().map(|record| 4 + record.len()).sum::<usize>()
                }
                _ => 0,
            }
    }
}

struct Engine {
    keeper: KeeperId,
    limits: Limits,
    policy: Arc<dyn SealPolicy>,
    wal: Wal,
    streams: HashMap<StreamId, Stream>,
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
        })
    }

    fn process(&mut self, mut wave: VecDeque<Work>) -> io::Result<()> {
        let mut deletions = Vec::new();
        while !wave.is_empty() {
            self.round(&mut wave, &mut deletions)?;
        }
        if !deletions.is_empty() || self.wal.bytes >= wal::SEGMENT_BYTES {
            self.wal.rotate(&mut self.streams)?;
        }
        for done in deletions {
            let _ = done.send((Ok(Reply::Deleted), None));
        }
        Ok(())
    }

    /// Decide and buffer in arrival order per stream. Other streams can advance while a
    /// large mutation is fragmented. A round publishes all its results after one sync.
    fn round(&mut self, wave: &mut VecDeque<Work>, deletions: &mut Vec<Done>) -> io::Result<()> {
        let mut buffer = BytesMut::new();
        let mut charged = HashMap::<StreamId, usize>::new();
        let mut blocked = HashSet::new();
        let mut changed = HashSet::new();
        let mut replies = Vec::new();
        for mut work in std::mem::take(wave) {
            let id = codec::stream(&work.request);
            if blocked.contains(&id) {
                wave.push_back(work);
                continue;
            }
            if work.pending.is_none() {
                let state = self.streams.get(&id);
                let (identical, retained_bytes) = state
                    .map(|state| state.facts(&work.request, &work.principal, &mut self.wal.reader))
                    .transpose()?
                    .unwrap_or((false, 0));
                let same_principal = state.is_some_and(|state| state.principal == work.principal);
                let seal_allowed = match work.request {
                    Request::Seal { epoch, holder, .. } => self.policy.allow(
                        std::str::from_utf8(&work.principal).expect("principal is UTF-8"),
                        id,
                        epoch,
                        holder,
                    ),
                    _ => true,
                };
                let view = StreamView {
                    keeper: self.keeper,
                    durable: state.map(|state| &state.view),
                    deleted: state.is_some_and(|state| state.deleted),
                    same_principal,
                    seal_allowed,
                    identical,
                    retained_bytes,
                };
                match rules::decide(&view, &work.request, &self.limits) {
                    Decision::Reply(Reply::Deleted)
                        if changed.contains(&id) || !deletions.is_empty() =>
                    {
                        deletions.push(work.done);
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
                    Decision::Persist => {}
                }
            }

            let charge = charged.entry(id).or_default();
            let budget =
                (self.limits.round_bytes_per_stream - *charge).min(ROUND_BYTES - buffer.len());
            if budget <= FRAME_OVERHEAD {
                blocked.insert(id);
                wave.push_back(work);
                continue;
            }
            if work.pending.is_none() {
                let principal = if matches!(work.request, Request::Seal { .. }) {
                    work.principal.clone()
                } else {
                    Bytes::new()
                };
                match wal::entry(&work.request, &principal) {
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
            let end = (*offset + budget - FRAME_OVERHEAD).min(entry.len());
            let last = end == entry.len();
            wal::fragment(&mut buffer, id, *offset == 0, last, &entry[*offset..end]);
            *charge += FRAME_OVERHEAD + end - *offset;
            *offset = end;
            if !last {
                blocked.insert(id);
                wave.push_back(work);
                continue;
            }

            let reply = self.streams.entry(id).or_default().apply(
                self.keeper,
                work.request,
                work.principal,
            )?;
            self.wal.dirty.insert(id);
            changed.insert(id);
            if reply == Reply::Deleted {
                deletions.push(work.done);
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
mod tests;
