//! Writer-driven stream journal over an authenticated keeper transport.

mod append;
mod decision;
mod head;
mod read;
mod recovery;

use std::{collections::HashMap, sync::Arc, time::Duration};

use bytes::Bytes;
use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{
    BoxFuture, Epoch, Identity, Journal, JournalError, Lsn, Page, Result, StreamId,
};
use parking_lot::Mutex;
use tokio::sync::{Mutex as AsyncMutex, oneshot};

use self::{append::Active, recovery::Recovery};
use super::wire::{KeeperId, Refusal, Reply, Request, Transport};

const QUORUM: usize = 2;
const RPC_TIMEOUT: Duration = Duration::from_secs(5);

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
}

struct Io {
    transport: Arc<dyn Transport>,
    /// Most pending records one lane sends in a single keeper append.
    append_records: usize,
}

type Heads = Vec<oneshot::Sender<Result<Lsn>>>;

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
                append_records: append::APPEND_RECORDS,
            }),
            keepers,
            streams: Arc::default(),
            seal_policy: None,
        })
    }

    /// Negative control for append amortization: limit each keeper append to `records`.
    #[cfg(test)]
    fn with_append_records(mut self, records: usize) -> Self {
        self.io = Arc::new(Io {
            transport: self.io.transport.clone(),
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
                return head::check(&self.io, stream, Some(active)).await;
            }
        }
        if let Some(recovery) = recovery.as_ref().filter(|r| r.epoch > epoch) {
            return Err(JournalError::Fenced {
                current: recovery.epoch,
            });
        }
        if recovery.as_ref().is_none_or(|r| r.epoch != epoch) {
            *recovery = Some(Recovery::choose(&self.io, stream, epoch).await?);
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
        let floor = quorum(FuturesUnordered::from_iter(stream.ensemble.map(
            |keeper| async move {
                match self
                    .io
                    .call(
                        keeper,
                        Request::Trim {
                            stream: stream.id,
                            epoch,
                            through,
                        },
                    )
                    .await?
                {
                    Reply::Trimmed { floor } if floor > through => Ok(floor),
                    _ => Err(JournalError::Unavailable),
                }
            },
        )))
        .await
        .map_err(|error| match error {
            JournalError::Conflict { .. } if through > head => JournalError::Conflict { head },
            error => error,
        })?
        .into_iter()
        .max()
        .unwrap();
        active.trim(floor);
        Ok(())
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
                    if let Some((current, identity)) = view.promised {
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
            self.io
                .broadcast(
                    &stream,
                    Request::Create {
                        stream: stream.id,
                        ensemble: stream.ensemble,
                    },
                    Reply::Created,
                )
                .await
        })
    }

    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move { self.seal_stream(&self.stream(stream), epoch).await })
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
                Ok(active) => match active.append(at, payload).await {
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
        Box::pin(async move { read::read(&self.io, &self.stream(stream), from, max, wait).await })
    }

    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move { head::head(self.io.clone(), self.stream(stream)).await })
    }

    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move { self.trim_stream(&self.stream(stream), epoch, through).await })
    }

    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            let stream = self.stream(stream);
            let mut recovery = stream.mutation.lock().await;
            self.io
                .broadcast(
                    &stream,
                    Request::Delete {
                        stream: stream.id,
                        ensemble: stream.ensemble,
                    },
                    Reply::Deleted,
                )
                .await?;
            if let Some(active) = stream.active.lock().take() {
                active.close(JournalError::Deleted);
            }
            *recovery = None;
            Ok(())
        })
    }
}

impl Io {
    async fn call(&self, keeper: KeeperId, request: Request) -> Result<Reply> {
        let wait = match &request {
            Request::Read { wait_ms, .. } => Duration::from_millis((*wait_ms).into()),
            _ => Duration::ZERO,
        };
        match tokio::time::timeout(wait + RPC_TIMEOUT, self.transport.call(keeper, request)).await {
            Ok(Ok(Reply::Refused(refusal))) => Err(map_refusal(refusal)),
            Ok(Ok(reply)) => Ok(reply),
            _ => Err(JournalError::Unavailable),
        }
    }

    async fn broadcast(
        self: &Arc<Self>,
        stream: &Stream,
        request: Request,
        expected: Reply,
    ) -> Result<()> {
        // Finish sending to the third keeper after the caller has its quorum.
        let calls = FuturesUnordered::new();
        for keeper in stream.ensemble {
            let (io, request, expected) = (self.clone(), request.clone(), expected.clone());
            calls.push(tokio::spawn(async move {
                if io.call(keeper, request).await? == expected {
                    Ok(())
                } else {
                    Err(JournalError::Unavailable)
                }
            }));
        }
        quorum(FuturesUnordered::from_iter(calls.into_iter().map(
            |call| async move { call.await.unwrap_or(Err(JournalError::Unavailable)) },
        )))
        .await
        .map(|_| ())
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

async fn quorum<T, F>(mut calls: FuturesUnordered<F>) -> Result<Vec<T>>
where
    F: Future<Output = Result<T>>,
{
    let mut successes = Vec::with_capacity(QUORUM);
    let mut errors = Vec::new();
    while let Some(reply) = calls.next().await {
        match reply {
            Ok(value) => {
                successes.push(value);
                if successes.len() == QUORUM {
                    return Ok(successes);
                }
            }
            Err(error) => errors.push(error),
        }
    }
    Err(refusal(&errors))
}

fn map_refusal(refusal: Refusal) -> JournalError {
    match refusal {
        Refusal::Fenced { promised } => JournalError::Fenced { current: promised },
        Refusal::Gap { head } | Refusal::Conflict { head } | Refusal::AboveHead { head } => {
            JournalError::Conflict { head }
        }
        Refusal::BelowFloor { floor } => JournalError::Trimmed { floor },
        Refusal::Full { floor } => JournalError::Full { floor },
        Refusal::TooLarge { max } => JournalError::TooLarge { max: max as usize },
        Refusal::Deleted => JournalError::Deleted,
        Refusal::NotFound => JournalError::NotFound,
        Refusal::NotSynced | Refusal::Unauthorized | Refusal::WrongEnsemble { .. } => {
            JournalError::Unavailable
        }
    }
}

fn refusal(errors: &[JournalError]) -> JournalError {
    for error in [JournalError::Deleted, JournalError::NotFound] {
        if errors.iter().filter(|seen| **seen == error).count() >= QUORUM {
            return error;
        }
    }
    if let Some(error) = errors.iter().find(|first| {
        !matches!(
            first,
            JournalError::Unavailable | JournalError::Fenced { .. }
        ) && errors
            .iter()
            .filter(|second| std::mem::discriminant(*second) == std::mem::discriminant(*first))
            .count()
            >= QUORUM
    }) {
        return error.clone();
    }
    errors
        .iter()
        .filter_map(|error| match error {
            JournalError::Fenced { current } => Some(*current),
            _ => None,
        })
        .max()
        .map_or(JournalError::Unavailable, |current| JournalError::Fenced {
            current,
        })
}

#[cfg(test)]
mod tests;
