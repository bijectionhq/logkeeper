//! The journal contract: the whole interface a consumer of an ordered, fenced stream journal sees.
//!
//! A journal is a set of streams. A stream is a totally ordered, durable, fenced sequence of opaque records.
//! The semantics of every verb and the five contract properties are in Logkeeper's `verification/target-journal.md`, section 2.
//! Implementations: an in-memory reference, a single-file reference, and Logkeeper's writer client.

use bytes::Bytes;
use std::{fmt, future::Future, pin::Pin, time::Duration};

#[cfg(feature = "conformance")]
pub mod conformance;

mod file;
pub mod reference;
mod state;
mod timer;

/// A stream's identity. Never reused after `delete`.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StreamId(pub u128);

/// The authenticated caller identity associated with a journal handle.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identity(Bytes);

impl Identity {
    pub const fn from_static(uri: &'static str) -> Self {
        Self(Bytes::from_static(uri.as_bytes()))
    }

    pub fn as_str(&self) -> &str {
        std::str::from_utf8(&self.0).expect("identity is UTF-8")
    }
}

impl From<&str> for Identity {
    fn from(uri: &str) -> Self {
        Self(Bytes::copy_from_slice(uri.as_bytes()))
    }
}

impl From<String> for Identity {
    fn from(uri: String) -> Self {
        Self(Bytes::from(uri))
    }
}

/// The writer fence. A stream accepts appends only under its sealed epoch.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Epoch(pub u64);

/// A record's position. The first record of a stream is at 1; an empty stream's head is 0.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lsn(pub u64);

/// The seal installed by one operator recovery and the head that survived it.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecoveryFence {
    pub epoch: Epoch,
    pub head: Lsn,
}

/// Identifies one writer process or session within its authenticated principal.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WriterSessionId(pub u128);

/// Authority for one writer session on one immutable history.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WriterFence {
    pub stream: StreamId,
    pub writer_epoch: Epoch,
    pub writer_session_id: WriterSessionId,
}

/// The exact committed record that allows an application to discard a prefix.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointAnchor {
    pub announced_at: Lsn,
    pub covered_through: Lsn,
    pub record_sha256: [u8; 32],
}

/// The fence and the committed head chosen at the instant of sealing.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SealReceipt {
    pub fence: WriterFence,
    pub sealed_head_lsn: Lsn,
}

/// A page of committed records.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Page {
    /// The first LSN retained at the source of this page.
    pub floor: Lsn,
    /// Committed records, in LSN order, contiguous from the requested start.
    pub records: Vec<(Lsn, Bytes)>,
    /// The committed position observed at the source of this page.
    pub head: Lsn,
}

/// Every way a journal call can fail.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JournalError {
    /// A higher epoch has sealed the stream, or another identity sealed this epoch.
    Fenced { current: Epoch },
    /// `at` is not the next LSN, or a different record is committed at `at`.
    Conflict { head: Lsn },
    /// The requested start is unavailable and is below an observed retained floor.
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
    /// An operator recovered the stream from a minority of its replicas
    /// after acknowledging data loss. The journal now holds `head`, which may
    /// be below positions it acknowledged before. Seals are refused until an
    /// administrator acknowledges the recovery; consumers must then rebuild
    /// from the journal instead of trusting their previous head.
    Recovered { head: Lsn },
    /// The target keeper or cluster version does not support this request or
    /// feature.
    Unsupported,
    /// A retained record or WAL segment slice failed its checksum on the
    /// replica, which has been durably quarantined.
    Corrupted,
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
    /// Fences every append under a lower epoch and returns the head.
    /// Returns `Recovered` after an operator recovery of the stream until a
    /// writer acknowledges it with `acknowledge_recovery`.
    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>>;
    /// Commits `payload` at `at` iff `epoch` is sealed by this caller and `at` is the next LSN.
    /// An identical retry returns `at`.
    fn append(
        &self,
        stream: StreamId,
        epoch: Epoch,
        at: Lsn,
        payload: Bytes,
    ) -> BoxFuture<'_, Result<Lsn>>;
    /// Reads committed records from one snapshot in `[from, from + max)`, waiting
    /// up to `wait` when `from` exceeds the observed head. The page can lag
    /// `head()` and can include records already trimmed elsewhere.
    fn read(
        &self,
        stream: StreamId,
        from: Lsn,
        max: usize,
        wait: Duration,
    ) -> BoxFuture<'_, Result<Page>>;
    /// A linearizable head.
    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>>;
    /// Discards records up to and including `through`. Only the sealed epoch may trim.
    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>>;
    /// Deletes the stream permanently.
    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>>;
    /// Claims and creates a stream whose committed positions are never reused.
    /// A backend that cannot guarantee this property refuses the operation.
    fn create_immutable(&self, _stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Verifies the claimed stream's immutable history mode without creating it.
    fn require_immutable(&self, _stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Advances the expected epoch and binds it to this principal and session.
    /// Retries by the same session return the original receipt while its fence holds.
    fn seal_session(
        &self,
        _stream: StreamId,
        _expected_writer_epoch: Epoch,
        _writer_session_id: WriterSessionId,
    ) -> BoxFuture<'_, Result<SealReceipt>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Commits the whole batch at the next position, or resolves an exact retained retry.
    fn append_session_batch(
        &self,
        _fence: WriterFence,
        _first_lsn: Lsn,
        _records: Vec<Bytes>,
    ) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Compatibility trim under the current writer session.
    fn trim_session(&self, _fence: WriterFence, _through: Lsn) -> BoxFuture<'_, Result<()>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Trims an immutable stream under its current writer session after
    /// verifying the exact committed announcement. The application verifies
    /// that this announcement can recover every record it covers.
    fn trim_checkpoint(
        &self,
        _fence: WriterFence,
        _anchor: CheckpointAnchor,
    ) -> BoxFuture<'_, Result<()>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Reads one applied view whose head reaches `minimum_head`.
    fn read_page(
        &self,
        _stream: StreamId,
        _from: Lsn,
        _minimum_head: Lsn,
        _limit: usize,
        _wait: Duration,
    ) -> BoxFuture<'_, Result<Page>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Accepts an operator recovery of the stream: lifts the recovery fence so
    /// the next `seal` succeeds, and returns the recovered head. Idempotent.
    /// The recovery itself already accepted the possible loss; a writer
    /// acknowledges to record that it noticed. Journals without operator
    /// recovery return `Unavailable`.
    fn acknowledge_recovery(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        let _ = stream;
        Box::pin(async { Err(JournalError::Unavailable) })
    }

    /// Reads the current operator recovery fence from a linearizable view.
    fn recovery_fence(&self, _stream: StreamId) -> BoxFuture<'_, Result<Option<RecoveryFence>>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Appends an opaque marker at `fence.head + 1` under `fence.epoch` and
    /// clears exactly that fence in one decision. An identical retry returns
    /// the marker's position while it is retained. A superseded or trimmed
    /// attempt never appends a record or clears a fence.
    fn acknowledge_recovery_with_marker(
        &self,
        _stream: StreamId,
        _fence: RecoveryFence,
        _marker: Bytes,
    ) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }
}

#[cfg(test)]
mod test_support;
