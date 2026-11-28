//! Writer-driven stream journal over an authenticated keeper transport.

mod append;
pub(super) mod decision;
mod head;
mod read;
mod recovery;
mod timed;

pub use super::timed::{TimedOriginal, TimedOriginalProof};

use std::{collections::HashMap, future::Future, sync::Arc, time::Duration};

use bytes::Bytes;
use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{
    BoxFuture, Epoch, Identity, Journal, JournalError, Lsn, Page, Result, StreamId,
};
use parking_lot::Mutex;
use tokio::sync::{Mutex as AsyncMutex, oneshot};

use self::{append::Active, decision::QUORUM, recovery::Recovery};
use super::{
    proposer::{
        driver, map_refusal,
        mutation::{Kind, Mutation},
        refusal,
    },
    wire::{KeeperId, Reply, Request, Transport},
};

/// Optional admission policy for seal. By default any authenticated identity can seal.
pub trait SealPolicy: Send + Sync {
    fn authorize(&self, stream: StreamId, epoch: Epoch, identity: &Identity) -> Result<()>;
}

#[derive(Clone)]
pub struct Writer {
    io: Arc<Io>,
    keepers: Arc<[KeeperId]>,
    streams: Arc<Mutex<HashMap<StreamId, Arc<Stream>>>>,
    seal_policy: Option<Arc<dyn SealPolicy>>,
    timed_authority: Option<Arc<timed::Authority>>,
}

struct Io {
    transport: Arc<dyn Transport>,
    proposal: u128,
    /// Most pending records one lane sends in a single keeper append.
    append_records: usize,
}

type Heads = Vec<oneshot::Sender<Result<Lsn>>>;

/// Ensemble moves one call follows, enough for a second replacement during the call.
const FOLLOW_LIMIT: usize = 3;

struct Stream {
    id: StreamId,
    ensemble: [KeeperId; 3],
    mutation: AsyncMutex<Option<Recovery>>,
    active: Mutex<Option<Arc<Active>>>,
    heads: Mutex<Heads>,
}

impl Writer {
    /// `keepers` are the authenticated keeper IDs in `journal_url` order. The transport
    /// authenticates the writer identity. Clone the writer to share its per-stream state.
    pub fn new(
        transport: Arc<dyn Transport>,
        keepers: impl IntoIterator<Item = KeeperId>,
    ) -> Result<Self> {
        let keepers: Arc<[KeeperId]> = keepers.into_iter().collect();
        if keepers.len() < 3
            || keepers
                .iter()
                .enumerate()
                .any(|(i, id)| keepers[..i].contains(id))
        {
            return Err(JournalError::Unavailable);
        }
        Ok(Self {
            io: Arc::new(Io {
                transport,
                proposal: uuid::Uuid::new_v4().as_u128(),
                append_records: append::APPEND_RECORDS,
            }),
            keepers,
            streams: Arc::default(),
            seal_policy: None,
            timed_authority: None,
        })
    }

    /// Negative control for append amortization: limit each keeper append to `records`.
    #[cfg(test)]
    fn with_append_records(mut self, records: usize) -> Self {
        self.io = Arc::new(Io {
            transport: self.io.transport.clone(),
            proposal: self.io.proposal,
            append_records: records,
        });
        self
    }

    pub fn with_seal_policy(mut self, policy: Arc<dyn SealPolicy>) -> Self {
        self.seal_policy = Some(policy);
        self
    }

    /// Supplies the placement of a stream with an explicit ensemble. All clients of
    /// that stream must use the same placement. Bind it before creating or opening it.
    pub fn bind_ensemble(&self, stream: StreamId, ensemble: [KeeperId; 3]) -> Result<()> {
        if ensemble
            .iter()
            .enumerate()
            .any(|(i, id)| ensemble[..i].contains(id) || !self.keepers.contains(id))
        {
            return Err(JournalError::Unavailable);
        }
        let mut streams = self.streams.lock();
        let entry = streams
            .entry(stream)
            .or_insert_with(|| Arc::new(Stream::new(stream, ensemble)));
        if entry.ensemble != ensemble {
            return Err(JournalError::Unavailable);
        }
        Ok(())
    }

    pub async fn create_in(&self, stream: StreamId, ensemble: [KeeperId; 3]) -> Result<()> {
        self.bind_ensemble(stream, ensemble)?;
        self.create(stream).await
    }

    fn stream(&self, id: StreamId) -> Arc<Stream> {
        self.streams
            .lock()
            .entry(id)
            .or_insert_with(|| Arc::new(Stream::new(id, self.keepers[..3].try_into().unwrap())))
            .clone()
    }

    async fn seal_stream(&self, stream: &Arc<Stream>, epoch: Epoch) -> Result<Lsn> {
        let mut recovery = stream.mutation.lock().await;
        if let Some(policy) = &self.seal_policy {
            policy.authorize(stream.id, epoch, self.io.transport.identity())?;
        }
        let active = stream.active.lock().clone();
        if let Some(active) = active {
            if active.epoch > epoch {
                return Err(JournalError::Fenced {
                    current: active.epoch,
                });
            }
            if active.epoch == epoch {
                active.retry_lanes();
                return head::check(&self.io, stream, Some(active)).await;
            }
        }
        if let Some(recovery) = recovery.as_ref().filter(|r| r.epoch > epoch) {
            return Err(JournalError::Fenced {
                current: recovery.epoch,
            });
        }
        if recovery.as_ref().is_none_or(|r| r.epoch != epoch) {
            *recovery = Some(recovery::choose(&self.io, stream, epoch).await?);
        }
        // Keep the selected history across lost replies or cancellation at this epoch.
        let selected = recovery.as_ref().unwrap();
        let active = Active::start(self.io.clone(), stream, selected.clone());
        active.ready().await?;
        let head = selected.tail();
        active.published(head).await?;
        if let Some(previous) = stream.active.lock().replace(active) {
            previous.close(JournalError::Fenced { current: epoch });
        }
        Ok(head)
    }

    fn active(&self, stream: &Stream, epoch: Epoch) -> Result<Arc<Active>> {
        let active = stream.active.lock();
        match active.as_ref() {
            Some(active) if active.epoch == epoch => Ok(active.clone()),
            Some(active) if active.epoch > epoch => Err(JournalError::Fenced {
                current: active.epoch,
            }),
            _ => Err(JournalError::Unavailable),
        }
    }

    async fn trim_stream(&self, stream: &Arc<Stream>, epoch: Epoch, through: Lsn) -> Result<()> {
        let _mutation = stream.mutation.lock().await;
        let active = match self.active(stream, epoch) {
            Ok(active) => active,
            Err(error) => return Err(self.authority(stream, epoch, error).await),
        };
        let head = active.head();
        if through <= head {
            active.published(through).await?;
        }
        // Trim replies establish the current fence and cover the requested
        // head even if the local snapshot is behind.
        let floor = driver::run(
            &*self.io.transport,
            Mutation::new(Kind::Trim { epoch, through }, stream.id, stream.ensemble),
            Some(driver::RPC_TIMEOUT),
        )
        .await
        .map_err(|error| match error {
            JournalError::Conflict { .. } if through > head => JournalError::Conflict { head },
            error => error,
        })?;
        active.trim(floor);
        Ok(())
    }

    /// Run `operation`, following the stream's ensemble after a replacement. An
    /// `Unavailable` result can mean that the keepers moved the stream. Each keeper
    /// enforces its own ensemble on Seal and Replace, so the ensemble this client
    /// follows chooses only which keepers it asks, never what they accept.
    async fn following<T, F>(&self, id: StreamId, operation: impl Fn(Arc<Stream>) -> F) -> Result<T>
    where
        F: Future<Output = Result<T>>,
    {
        let mut stream = self.stream(id);
        for _ in 0..FOLLOW_LIMIT {
            match operation(stream.clone()).await {
                Err(JournalError::Unavailable) => match self.follow(&stream).await {
                    Some(next) => stream = next,
                    None => return Err(JournalError::Unavailable),
                },
                result => return result,
            }
        }
        operation(stream).await
    }

    /// Learn a newer ensemble from a voting member of the current one. A member's
    /// ensemble contains itself and changes only through Replace, so the members of
    /// the ensemble this client uses never report an older one.
    async fn follow(&self, stream: &Arc<Stream>) -> Option<Arc<Stream>> {
        let mut calls = FuturesUnordered::from_iter(stream.ensemble.map(|keeper| async move {
            let check = Request::Check {
                stream: stream.id,
                epoch: Epoch(0),
            };
            (keeper, self.io.call(keeper, check).await)
        }));
        while let Some((keeper, reply)) = calls.next().await {
            let Ok(Reply::Checked(view)) = reply else {
                continue;
            };
            let ensemble = view.ensemble;
            let distinct = ensemble
                .iter()
                .enumerate()
                .all(|(i, id)| id.0 != 0 && !ensemble[..i].contains(id));
            if view.learner
                || ensemble == stream.ensemble
                || !ensemble.contains(&keeper)
                || !distinct
            {
                continue;
            }
            let promised = view.promised.map(|(epoch, ..)| epoch);
            return Some(self.rebind(stream, ensemble, promised));
        }
        None
    }

    fn rebind(
        &self,
        stream: &Arc<Stream>,
        ensemble: [KeeperId; 3],
        promised: Option<Epoch>,
    ) -> Arc<Stream> {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream.id).or_insert_with(|| stream.clone());
        if Arc::ptr_eq(entry, stream) {
            *entry = Arc::new(Stream::new(stream.id, ensemble));
            // The replacement sealed a higher epoch, which fenced this writer.
            if let Some(active) = stream.active.lock().take() {
                active.close(match promised {
                    Some(current) if current > active.epoch => JournalError::Fenced { current },
                    _ => JournalError::Unavailable,
                });
            }
        }
        entry.clone()
    }

    // A client without an active writer still reports a known remote fence or terminal state.
    async fn authority(
        &self,
        stream: &Stream,
        epoch: Epoch,
        fallback: JournalError,
    ) -> JournalError {
        if matches!(
            fallback,
            JournalError::Fenced { .. } | JournalError::Deleted
        ) {
            return fallback;
        }
        let mut calls = FuturesUnordered::from_iter(stream.ensemble.map(|keeper| {
            self.io.call(
                keeper,
                Request::Check {
                    stream: stream.id,
                    epoch,
                },
            )
        }));
        let mut errors = Vec::new();
        while let Some(reply) = calls.next().await {
            match reply {
                Ok(Reply::Checked(view)) => {
                    if let Some((current, identity, _)) = view.promised {
                        if current > epoch
                            || (current == epoch && &identity != self.io.transport.identity())
                        {
                            errors.push(JournalError::Fenced { current });
                        }
                    }
                }
                Err(error) => errors.push(error),
                _ => {}
            }
        }
        // Equal-epoch seal races can leave a losing promise on the third keeper.
        // A local refusal must not be replaced by that keeper's fence.
        if errors
            .iter()
            .filter(|error| matches!(error, JournalError::Fenced { .. }))
            .count()
            < QUORUM
        {
            errors.retain(|error| !matches!(error, JournalError::Fenced { .. }));
        }
        match refusal(&errors) {
            JournalError::Unavailable => fallback,
            error => error,
        }
    }
}

impl Stream {
    fn new(id: StreamId, ensemble: [KeeperId; 3]) -> Self {
        Self {
            id,
            ensemble,
            mutation: AsyncMutex::default(),
            active: Mutex::default(),
            heads: Mutex::default(),
        }
    }
}

impl Journal for Writer {
    fn create(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            let stream = self.stream(stream);
            let _mutation = stream.mutation.lock().await;
            driver::run_detached(
                self.io.transport.clone(),
                Mutation::new(Kind::Create, stream.id, stream.ensemble),
            )
            .await
            .map(|_| ())
        })
    }

    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            self.following(stream, |stream| async move {
                self.seal_stream(&stream, epoch).await
            })
            .await
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
            let stream = self.stream(stream);
            match self.active(&stream, epoch) {
                Ok(active) => match active
                    .append(at, super::timed::Entry::Ordinary(payload))
                    .await
                {
                    Err(error @ (JournalError::Conflict { .. } | JournalError::Trimmed { .. })) => {
                        Err(self.authority(&stream, epoch, error).await)
                    }
                    result => result,
                },
                Err(error) => Err(self.authority(&stream, epoch, error).await),
            }
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
            self.following(stream, |stream| async move {
                read::read(&self.io, &stream, from, max, wait).await
            })
            .await
        })
    }

    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            self.following(stream, |stream| head::head(self.io.clone(), stream))
                .await
        })
    }

    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move { self.trim_stream(&self.stream(stream), epoch, through).await })
    }

    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            self.following(
                stream,
                |stream| async move { self.delete_stream(&stream).await },
            )
            .await
        })
    }
}

impl Writer {
    async fn delete_stream(&self, stream: &Stream) -> Result<()> {
        let mut recovery = stream.mutation.lock().await;
        driver::run_detached(
            self.io.transport.clone(),
            Mutation::new(Kind::Delete, stream.id, stream.ensemble),
        )
        .await?;
        if let Some(active) = stream.active.lock().take() {
            active.close(JournalError::Deleted);
        }
        *recovery = None;
        Ok(())
    }
}

impl Io {
    async fn call(&self, keeper: KeeperId, request: Request) -> Result<Reply> {
        let wait = match &request {
            Request::Read { wait_ms, .. } => Duration::from_millis((*wait_ms).into()),
            _ => Duration::ZERO,
        };
        match tokio::time::timeout(
            wait + driver::RPC_TIMEOUT,
            self.transport.call(keeper, request),
        )
        .await
        {
            Ok(Ok(Reply::Refused(refusal))) => Err(map_refusal(refusal)),
            Ok(Ok(reply)) => Ok(reply),
            _ => Err(JournalError::Unavailable),
        }
    }

    async fn publish(
        &self,
        keeper: KeeperId,
        stream: StreamId,
        epoch: Epoch,
        head: Lsn,
    ) -> Result<Lsn> {
        match self
            .call(
                keeper,
                Request::Append {
                    stream,
                    epoch,
                    at: Lsn(head.0 + 1),
                    records: Vec::new(),
                    head,
                },
            )
            .await?
        {
            Reply::Appended { tail } if tail >= head => Ok(tail),
            _ => Err(JournalError::Unavailable),
        }
    }
}

/// Each slot owns one call on the stream's distinct, fixed ensemble.
async fn quorum<T, F>(calls: [F; 3]) -> Result<[T; QUORUM]>
where
    F: Future<Output = Result<T>>,
{
    let mut calls = FuturesUnordered::from_iter(calls);
    let mut first = None;
    let mut errors = Vec::new();
    while let Some(reply) = calls.next().await {
        match reply {
            Ok(value) => {
                if let Some(previous) = first.take() {
                    return Ok([previous, value]);
                }
                first = Some(value);
            }
            Err(error) => errors.push(error),
        }
    }
    Err(refusal(&errors))
}

#[cfg(test)]
mod tests;
