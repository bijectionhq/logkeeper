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

/// Where a recovered history's last kept record came from.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RecoverySource {
    /// The surviving voter's log.
    Survivor,
    /// The object store's committed run, longer than the survivor's log.
    ObjectStore,
}

/// The typed entry an operator recovery leaves in its stream: the first
/// entry of the recovered configuration epoch, at `fence.head + 1`.
///
/// The journal writes it when the recovery fence is cleared, by
/// `acknowledge_recovery` or `acknowledge_recovery_with_marker`, and only
/// then. It is never client data: no append can produce an entry of this
/// kind, whatever its bytes, so a reader that finds one in
/// [`Page::recoveries`] knows an operator recovery happened there. In
/// [`Page::records`] the same position holds the entry's canonical encoding
/// ([`RecoveryEntry::encode`]), so positions stay contiguous.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveryEntry {
    /// The recovery fence this entry cleared. `fence.head` is the last
    /// record the recovery kept, and the entry sits right after it.
    pub fence: RecoveryFence,
    /// The configuration epoch the recovery installed.
    pub configuration_epoch: u64,
    /// The last record the recovered history kept, as the recovery reported
    /// it. Records a writer was acknowledged above it are lost.
    pub loss_point: Lsn,
    /// Whether `loss_point` is exact: the recovery knew the history's
    /// committed point. When false, records between it and `fence.head` may
    /// differ from what writers were acknowledged.
    pub exact: bool,
    pub source: RecoverySource,
    /// When the recovery was committed, in Unix milliseconds.
    pub time_unix_ms: u64,
    /// The consumer's marker, given to `acknowledge_recovery_with_marker`.
    pub marker: Option<Bytes>,
}

impl RecoveryEntry {
    const MAGIC: &'static [u8; 8] = b"LKRECOV1";
    /// The encoded size of an entry without its marker.
    pub const HEADER_BYTES: usize = 8 + 5 * 8 + 3;

    /// The entry's canonical encoding: what [`Page::records`] holds at its
    /// position and what a journal stores.
    pub fn encode(&self) -> Bytes {
        let marker = self.marker.as_deref().unwrap_or_default();
        let mut out = Vec::with_capacity(Self::HEADER_BYTES + marker.len());
        out.extend_from_slice(Self::MAGIC);
        for value in [
            self.fence.epoch.0,
            self.fence.head.0,
            self.configuration_epoch,
            self.loss_point.0,
            self.time_unix_ms,
        ] {
            out.extend_from_slice(&value.to_be_bytes());
        }
        out.push(match self.source {
            RecoverySource::Survivor => 0,
            RecoverySource::ObjectStore => 1,
        });
        out.push(u8::from(self.exact));
        out.push(u8::from(self.marker.is_some()));
        out.extend_from_slice(marker);
        Bytes::from(out)
    }

    /// Decodes a canonical encoding. `None` for any other bytes.
    pub fn decode(bytes: &Bytes) -> Option<Self> {
        let header = bytes.get(..Self::HEADER_BYTES)?;
        if &header[..8] != Self::MAGIC {
            return None;
        }
        let word = |index: usize| {
            let at = 8 + index * 8;
            u64::from_be_bytes(header[at..at + 8].try_into().unwrap())
        };
        let source = match header[48] {
            0 => RecoverySource::Survivor,
            1 => RecoverySource::ObjectStore,
            _ => return None,
        };
        let exact = match header[49] {
            0 => false,
            1 => true,
            _ => return None,
        };
        let marker = match header[50] {
            0 if bytes.len() == Self::HEADER_BYTES => None,
            1 => Some(bytes.slice(Self::HEADER_BYTES..)),
            _ => return None,
        };
        Some(Self {
            fence: RecoveryFence {
                epoch: Epoch(word(0)),
                head: Lsn(word(1)),
            },
            configuration_epoch: word(2),
            loss_point: Lsn(word(3)),
            exact,
            time_unix_ms: word(4),
            source,
            marker,
        })
    }

    /// The entry's position: right after the last record kept.
    pub fn at(&self) -> Lsn {
        Lsn(self.fence.head.0.saturating_add(1))
    }
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

/// The announcement to commit together with a new replay floor. The
/// authenticated application writer certifies that its dependencies exist
/// and stay retained for the lifetime of this selected checkpoint.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckpointInstallation {
    pub operation_id: u128,
    /// The expected next position, also used to authenticate the record.
    pub checkpoint_lsn: Lsn,
    pub covered_through_lsn: Lsn,
    pub record: Bytes,
}

/// The recovery base and first retained position selected in one decision.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointReceipt {
    pub checkpoint_lsn: Lsn,
    pub covered_through_lsn: Lsn,
    pub logical_floor_lsn: Lsn,
}

/// One recovery's custody of an exact selected checkpoint on its destination
/// stream. The installation digest binds the issuing authority and operation.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointHold {
    pub operation_id: u128,
    pub installation_sha256: [u8; 32],
    pub anchor: CheckpointAnchor,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointCustody {
    pub hold: CheckpointHold,
    pub released: bool,
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
    /// The typed recovery entries among `records`, in LSN order. Every other
    /// record is client data. Journals without operator recovery leave this
    /// empty.
    #[cfg_attr(feature = "serde", serde(default))]
    pub recoveries: Vec<(Lsn, RecoveryEntry)>,
}

impl Page {
    /// A page of client data only.
    pub fn new(floor: Lsn, records: Vec<(Lsn, Bytes)>, head: Lsn) -> Self {
        Self {
            floor,
            records,
            head,
            recoveries: Vec::new(),
        }
    }

    /// The recovery entry at `at`, when the record there is one.
    pub fn recovery(&self, at: Lsn) -> Option<&RecoveryEntry> {
        self.recoveries
            .binary_search_by_key(&at, |(lsn, _)| *lsn)
            .ok()
            .map(|index| &self.recoveries[index].1)
    }
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

    /// Commits and selects this announcement and advances the floor in one
    /// decision under the current writer fence. An exact retry resolves
    /// while this checkpoint is selected.
    fn install_checkpoint(
        &self,
        _fence: WriterFence,
        _checkpoint: CheckpointInstallation,
    ) -> BoxFuture<'_, Result<CheckpointReceipt>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// The selected recovery base in a linearizable immutable stream view.
    fn selected_checkpoint(
        &self,
        _stream: StreamId,
    ) -> BoxFuture<'_, Result<Option<CheckpointReceipt>>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Pins the exact selected checkpoint and its retained journal suffix.
    fn retain_checkpoint(
        &self,
        _stream: StreamId,
        _hold: CheckpointHold,
    ) -> BoxFuture<'_, Result<CheckpointCustody>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Observes durable custody from a quorum-confirmed stream view.
    fn checkpoint_custody(
        &self,
        _stream: StreamId,
    ) -> BoxFuture<'_, Result<Option<CheckpointCustody>>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Releases the original hold. An exact retry returns the released custody.
    fn release_checkpoint(
        &self,
        _stream: StreamId,
        _hold: CheckpointHold,
    ) -> BoxFuture<'_, Result<CheckpointCustody>> {
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
    /// the next `seal` succeeds, and returns the recovered head, the last
    /// record kept. Idempotent. The recovery itself already accepted the
    /// possible loss; a writer acknowledges to record that it noticed. A
    /// journal that records recoveries in the stream writes the typed
    /// [`RecoveryEntry`], without a marker, at the head plus one in the same
    /// decision. Journals without operator recovery return `Unavailable`.
    fn acknowledge_recovery(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        let _ = stream;
        Box::pin(async { Err(JournalError::Unavailable) })
    }

    /// Reads the current operator recovery fence from a linearizable view.
    fn recovery_fence(&self, _stream: StreamId) -> BoxFuture<'_, Result<Option<RecoveryFence>>> {
        Box::pin(async { Err(JournalError::Unsupported) })
    }

    /// Writes the recovery's entry at `fence.head + 1` under `fence.epoch`,
    /// carrying `marker`, and clears exactly that fence in one decision. A
    /// journal that records recoveries in the stream writes the typed
    /// [`RecoveryEntry`] with the marker inside it; an older one appends the
    /// marker as an opaque record. An identical retry returns the entry's
    /// position while it is retained. A superseded or trimmed attempt never
    /// writes an entry or clears a fence.
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

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(marker: Option<&'static [u8]>) -> RecoveryEntry {
        RecoveryEntry {
            fence: RecoveryFence {
                epoch: Epoch(7),
                head: Lsn(41),
            },
            configuration_epoch: 3,
            loss_point: Lsn(41),
            exact: true,
            source: RecoverySource::ObjectStore,
            time_unix_ms: 1_795_000_000_000,
            marker: marker.map(Bytes::from_static),
        }
    }

    #[test]
    fn recovery_entries_round_trip_and_refuse_other_bytes() {
        for marker in [None, Some(&b""[..]), Some(&b"consumer marker"[..])] {
            let entry = entry(marker);
            let bytes = entry.encode();
            assert_eq!(
                bytes.len(),
                RecoveryEntry::HEADER_BYTES + marker.map_or(0, <[u8]>::len)
            );
            assert_eq!(RecoveryEntry::decode(&bytes), Some(entry.clone()));
            assert_eq!(entry.at(), Lsn(42));
        }
        let bytes = entry(None).encode();
        assert_eq!(RecoveryEntry::decode(&bytes.slice(..10)), None);
        let mut extended = bytes.to_vec();
        extended.push(0);
        assert_eq!(RecoveryEntry::decode(&Bytes::from(extended)), None);
        for (at, value) in [(48, 2), (49, 2), (50, 2)] {
            let mut damaged = bytes.to_vec();
            damaged[at] = value;
            assert_eq!(RecoveryEntry::decode(&Bytes::from(damaged)), None);
        }
        assert_eq!(
            RecoveryEntry::decode(&Bytes::from_static(b"client data")),
            None
        );
    }

    #[test]
    fn pages_find_their_recovery_entries() {
        let entry = entry(Some(b"m"));
        let page = Page {
            floor: Lsn(40),
            records: vec![
                (Lsn(41), Bytes::from_static(b"kept")),
                (Lsn(42), entry.encode()),
            ],
            head: Lsn(42),
            recoveries: vec![(Lsn(42), entry.clone())],
        };
        assert_eq!(page.recovery(Lsn(42)), Some(&entry));
        assert_eq!(page.recovery(Lsn(41)), None);
    }
}
