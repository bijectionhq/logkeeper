use crate::{
    BoxFuture, Epoch, Identity, Journal, JournalError, Lsn, Page, Result, StreamId,
    file::Storage,
    state::{Mutation, State},
    timer::Sleep,
};
use bytes::Bytes;
use std::{
    collections::HashMap,
    future::{Future, poll_fn},
    pin::pin,
    sync::{Arc, Mutex},
    task::{Poll, Waker},
    time::Duration,
};

pub use crate::file::FileJournal;

/// Static payload limits for every stream in a reference journal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Maximum size in bytes of a single record.
    pub max_record_bytes: usize,
    /// Maximum total payload bytes retained by a stream.
    pub stream_quota_bytes: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_record_bytes: 32 * 1024 * 1024,
            stream_quota_bytes: 8 * 1024 * 1024 * 1024,
        }
    }
}

/// An in-process reference journal shared by all handles created from it.
#[derive(Clone)]
pub struct MemoryJournal(Arc<Engine>);

impl MemoryJournal {
    /// Starts an empty journal with the given limits.
    pub fn new(limits: Limits) -> Self {
        Self(Arc::new(Engine::new(State::new(limits), None)))
    }

    /// Returns an owned handle that makes calls as this identity.
    pub fn handle(&self, identity: Identity) -> impl Journal + use<> {
        self.0.handle(identity)
    }
}

impl Default for MemoryJournal {
    fn default() -> Self {
        Self::new(Limits::default())
    }
}

pub(crate) struct Engine(Mutex<Inner>);

struct Inner {
    state: State,
    storage: Option<Storage>,
    unavailable: bool,
    readers: HashMap<StreamId, HashMap<u64, Waker>>,
    next_reader: u64,
}

impl Inner {
    fn available(&self) -> Result<()> {
        if self.unavailable {
            return Err(JournalError::Unavailable);
        }
        Ok(())
    }
}

impl Engine {
    pub(crate) fn new(state: State, storage: Option<Storage>) -> Self {
        Self(Mutex::new(Inner {
            state,
            storage,
            unavailable: false,
            readers: HashMap::new(),
            next_reader: 0,
        }))
    }

    pub(crate) fn handle(self: &Arc<Self>, identity: Identity) -> impl Journal + use<> {
        Handle {
            engine: self.clone(),
            identity,
        }
    }

    fn mutate(&self, stream: StreamId, mutation: Mutation) -> Result<Lsn> {
        let mut inner = self.0.lock().unwrap();
        inner.available()?;
        let decision = inner.state.decide(stream, &mutation)?;
        if !decision.changed {
            return Ok(decision.position);
        }

        if let Some(storage) = &mut inner.storage
            && storage.persist(stream, &mutation).is_err()
        {
            inner.unavailable = true;
            let readers = std::mem::take(&mut inner.readers);
            drop(inner);
            for waker in readers.into_values().flat_map(HashMap::into_values) {
                waker.wake();
            }
            return Err(JournalError::Unavailable);
        }

        let wakes_readers = mutation.wakes_readers();
        inner.state.apply(stream, mutation);
        let readers = wakes_readers
            .then(|| inner.readers.remove(&stream))
            .flatten();
        drop(inner);
        for waker in readers.into_iter().flat_map(HashMap::into_values) {
            waker.wake();
        }
        Ok(decision.position)
    }

    fn head(&self, stream: StreamId) -> Result<Lsn> {
        let inner = self.0.lock().unwrap();
        inner.available()?;
        Ok(inner.state.live(stream)?.head)
    }

    async fn read(&self, stream: StreamId, from: Lsn, max: usize, wait: Duration) -> Result<Page> {
        let mut timeout = pin!(Sleep::new(wait));
        let mut reader = Reader {
            engine: self,
            stream,
            id: None,
        };
        poll_fn(|cx| {
            let mut inner = self.0.lock().unwrap();
            inner.available()?;
            let live = inner.state.live(stream)?;
            if from < live.floor {
                return Poll::Ready(Err(JournalError::Trimmed { floor: live.floor }));
            }
            if from <= live.head || timeout.as_mut().poll(cx).is_ready() {
                return Poll::Ready(Ok(live.page(from, max)));
            }
            // Check the current head and register under the same lock as append.
            let id = *reader.id.get_or_insert_with(|| {
                let id = inner.next_reader;
                inner.next_reader += 1;
                id
            });
            inner
                .readers
                .entry(stream)
                .or_default()
                .insert(id, cx.waker().clone());
            Poll::Pending
        })
        .await
    }
}

struct Reader<'a> {
    engine: &'a Engine,
    stream: StreamId,
    id: Option<u64>,
}

impl Drop for Reader<'_> {
    fn drop(&mut self) {
        if let Some(id) = self.id {
            let mut inner = self.engine.0.lock().unwrap();
            if let Some(readers) = inner.readers.get_mut(&self.stream) {
                readers.remove(&id);
                if readers.is_empty() {
                    inner.readers.remove(&self.stream);
                }
            }
        }
    }
}

struct Handle {
    engine: Arc<Engine>,
    identity: Identity,
}

impl Journal for Handle {
    fn create(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move { self.engine.mutate(stream, Mutation::Create).map(drop) })
    }

    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            self.engine.mutate(
                stream,
                Mutation::Seal {
                    epoch,
                    identity: self.identity.clone(),
                },
            )
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
            self.engine.mutate(
                stream,
                Mutation::Append {
                    epoch,
                    identity: self.identity.clone(),
                    at,
                    payload,
                },
            )
        })
    }

    fn read(
        &self,
        stream: StreamId,
        from: Lsn,
        max: usize,
        wait: Duration,
    ) -> BoxFuture<'_, Result<Page>> {
        Box::pin(self.engine.read(stream, from, max, wait))
    }

    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move { self.engine.head(stream) })
    }

    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            self.engine
                .mutate(
                    stream,
                    Mutation::Trim {
                        epoch,
                        identity: self.identity.clone(),
                        through,
                    },
                )
                .map(drop)
        })
    }

    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move { self.engine.mutate(stream, Mutation::Delete).map(drop) })
    }
}
