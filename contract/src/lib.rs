//! The journal contract: the whole interface a consumer of an ordered, fenced stream journal sees.
//!
//! A journal is a set of streams. A stream is a totally ordered, durable, fenced sequence of opaque records.
//! The semantics of every verb and the five contract properties are in Logkeeper's `verification/target-journal.md`, section 2.
//! Implementations: an in-memory reference, a single-file reference, and Logkeeper's writer client.

use bytes::Bytes;
use std::{fmt, future::Future, pin::Pin, time::Duration};

mod file;
mod reference;
mod state;
mod timer;

pub use file::FileJournal;
pub use reference::MemoryJournal;

/// A stream's identity. Never reused after `delete`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StreamId(pub u128);

/// The caller identity associated with a journal handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identity(pub u128);

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

/// The writer fence. A stream accepts appends only under its sealed epoch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Epoch(pub u64);

/// A record's position. The first record of a stream is at 1; an empty stream's end is 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lsn(pub u64);

/// A page of committed records.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Page {
    /// The first retained LSN.
    pub floor: Lsn,
    /// Committed records, in LSN order, contiguous from the requested start.
    pub records: Vec<(Lsn, Bytes)>,
    /// The committed end the journal observed while serving the read.
    pub end: Lsn,
}

/// Every way a journal call can fail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JournalError {
    /// A higher epoch has sealed the stream, or another identity sealed this epoch.
    Fenced { current: Epoch },
    /// `at` is not the next LSN, or a different record is committed at `at`.
    Conflict { committed_end: Lsn },
    /// `from` is below the retained floor.
    Trimmed { floor: Lsn },
    /// The payload exceeds the per-record limit.
    TooLarge { max: usize },
    /// The stream's byte quota is exhausted. `trim` frees space and never needs space.
    Full { floor: Lsn },
    /// The stream does not exist.
    NotFound,
    /// The stream was deleted. Its identity is never reused.
    Deleted,
    /// Retry. The outcome of a mutation may be unknown.
    Unavailable,
}

impl fmt::Display for JournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl std::error::Error for JournalError {}

pub type Result<T> = std::result::Result<T, JournalError>;
pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

/// The ordered, fenced stream journal.
pub trait Journal: Send + Sync {
    /// Creates an empty stream. Idempotent. Refused with `Deleted` after `delete`.
    fn create(&self, stream: StreamId) -> BoxFuture<'_, Result<()>>;
    /// Fences every append under a lower epoch and returns the committed end.
    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>>;
    /// Commits `payload` at `at` iff `epoch` is sealed by this caller and `at` is the next LSN.
    /// An identical retry returns `at`.
    fn append(&self, stream: StreamId, epoch: Epoch, at: Lsn, payload: Bytes) -> BoxFuture<'_, Result<Lsn>>;
    /// Committed records in `[from, from + max)`, waiting up to `wait` at the end.
    fn read(&self, stream: StreamId, from: Lsn, max: usize, wait: Duration) -> BoxFuture<'_, Result<Page>>;
    /// A linearizable committed end.
    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>>;
    /// Discards records up to and including `through`. Only the sealed epoch may trim.
    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>>;
    /// Deletes the stream permanently.
    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>>;
}

#[cfg(test)]
mod test_support;
