//! Deterministic decisions over the committed journal view.

pub(super) const MAX_RETAINED_RECORDS: usize = 262_144;
use super::decisions::{
    EntryStep, RECOVERY_HEADROOM_BYTES, RECOVERY_HEADROOM_RECORDS, RecordOrigin, RetainedKind,
};
/// The most records any retained state holds: the ordinary limit and the
/// recovery entries' headroom. Snapshot geometry admits this many.
pub(super) const MAX_RETAINED_WITH_HEADROOM: usize =
    MAX_RETAINED_RECORDS + RECOVERY_HEADROOM_RECORDS;

/// The most bytes a stream of `quota` retains: the quota and the recovery
/// entries' headroom.
pub(super) fn quota_with_headroom(quota: u64) -> u64 {
    quota.saturating_add(RECOVERY_HEADROOM_BYTES)
}

/// The writer of the fence an operator recovery installs. No client seals
/// as this UUID with an empty principal, so the fence admits no append or
/// trim, and ordinary seals are refused with `Recovered` until an
/// administrator acknowledges the recovery.
pub(super) const RECOVERY_WRITER: uuid::Uuid =
    uuid::Uuid::from_u128(0x7265_636f_7665_7279_2d66_656e_6365_0000);

use std::{
    collections::VecDeque,
    fs::File,
    io::{self, Read, Seek, SeekFrom},
    sync::Arc,
};

use bytes::Bytes;
use journal_contract::{
    CheckpointAnchor, CheckpointCustody, CheckpointHold, CheckpointInstallation, CheckpointReceipt,
    Epoch, JournalError, Lsn, Page, RecoveryEntry, RecoveryFence, Result, WriterSessionId,
};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use super::{
    Fence, Genesis, MAX_PAGE, MAX_RECORD, MAX_RECORDS_PER_PAGE, Sealed, Stage,
    authority::RecoveryRecord,
};
use crate::stream::keeper::record_charge;
use crate::stream::timed::{EVIDENCE_BYTES, TimedEvidence};

mod checkpoint;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Command {
    Create,
    Seal {
        expected: Epoch,
        writer: uuid::Uuid,
        owner: String,
    },
    Append {
        fence: Fence,
        owner: String,
        at: Lsn,
        payload: Bytes,
    },
    Trim {
        fence: Fence,
        owner: String,
        through: Lsn,
    },
    Delete,
    Stage(Stage),
    StageOwned(Stage),
    Admitted(
        uuid::Uuid,
        #[serde(deserialize_with = "unticketed_command")] Box<Command>,
    ),
    /// A contiguous group appended atomically from `at`. The payloads are the
    /// last field, so each record's retained extent ends a fixed distance
    /// before the end of the durable entry.
    AppendBatch {
        fence: Fence,
        owner: String,
        at: Lsn,
        payloads: Vec<Bytes>,
    },
    /// A timed original: its signed quorum-sync evidence followed by its
    /// payload, retained together as one record.
    AppendOriginal {
        fence: Fence,
        owner: String,
        at: Lsn,
        record: Bytes,
    },
    /// An operator recovery: the stage from the survivor's configuration to
    /// the survivor and two replacements, and the recovery fence above every
    /// epoch applied before it. The recovered membership entry follows it.
    /// Added after `AppendOriginal`, so older keepers refuse logs that hold
    /// it instead of misreading them.
    Recover(Stage),
    /// An administrator's acknowledgement that clears the recovery fence.
    AcknowledgeRecovery,
    /// Appends the consumer's marker and clears exactly this recovery fence.
    /// Keep the payload last so its retained extent ends with the entry.
    AcknowledgeRecoveryWithMarker {
        fence: RecoveryFence,
        at: Lsn,
        payload: Bytes,
    },
    SealSession {
        expected_writer_epoch: Epoch,
        writer_session_id: WriterSessionId,
        owner: String,
    },
    /// The leader uploaded the committed records through `through` under
    /// `lineage` to the offload store. Every voter advances its
    /// `offloaded_through` and drops its local copies of offloaded records
    /// below `retain_from`. Ignored under any other lineage. Added after
    /// `AcknowledgeRecovery` and proposed only once the cluster finalized
    /// `CLUSTER_VERSION_OFFLOAD`, so older keepers never meet it.
    Offloaded {
        lineage: u64,
        through: Lsn,
        retain_from: Lsn,
    },
    /// Starts a new offload lineage, and with `replace` makes the store's
    /// committed run the whole history: an operator recovery from object
    /// store plus survivor, or a restore into a fresh stream.
    Restore(Restore),
    /// A selected checkpoint and its announcement share one application entry.
    /// The installation ends in the announcement bytes, like `Append`.
    InstallCheckpoint {
        fence: Fence,
        owner: String,
        checkpoint: CheckpointInstallation,
    },
    /// Selects a previously committed announcement checked by the leader.
    SelectCheckpoint {
        fence: Fence,
        owner: String,
        anchor: CheckpointAnchor,
    },
    /// An operator recovery as `Recover`, which also records the catalog's
    /// record of it. The fence it installs clears only by writing the
    /// stream's typed recovery entry (`RecoveryEntry`). Added after
    /// `SelectCheckpoint` and written only once the cluster finalized
    /// `CLUSTER_VERSION_RECOVERY_ENTRY`, so older keepers never meet it.
    RecoverRecorded {
        stage: Stage,
        record: RecoveryRecord,
        /// Whether the record's loss point is exact (`RecoveryReport`).
        exact: bool,
    },
    /// Writes the typed recovery entry at `at`, `fence.head + 1`, and clears
    /// exactly that recorded fence. `entry` is the entry's canonical
    /// encoding; keep it last so its retained extent ends with the entry.
    /// Proposed only for a fence a `RecoverRecorded` installed.
    RecoveryEntry {
        fence: RecoveryFence,
        at: Lsn,
        entry: Bytes,
    },
    CheckpointCustody(CheckpointCustody),
}

/// A new offload lineage: see `Command::Restore`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Restore {
    pub lineage: u64,
    /// The lowest LSN the restored history holds.
    pub floor: Lsn,
    /// The last LSN the store holds under the previous lineages.
    pub head: Lsn,
    /// The highest writer epoch the restored records were written under.
    pub epoch: Epoch,
    /// Drop every local record and serve `floor..=head` from the store.
    pub replace: bool,
}

/// The most records one batch carries.
pub(super) const MAX_BATCH_RECORDS: usize = 256;
/// The most payload bytes one batch carries, so a batch entry is no larger
/// than one maximum record.
pub(super) const MAX_BATCH_BYTES: usize = MAX_RECORD;

/// Whether a batch fits its count and byte bounds and each record fits.
pub(super) fn valid_batch(payloads: &[Bytes]) -> bool {
    !payloads.is_empty()
        && payloads.len() <= MAX_BATCH_RECORDS
        && payloads.iter().all(|payload| payload.len() <= MAX_RECORD)
        && payloads
            .iter()
            .try_fold(0usize, |total, payload| total.checked_add(payload.len()))
            .is_some_and(|total| total <= MAX_BATCH_BYTES)
}

fn unticketed_command<'de, D: serde::Deserializer<'de>>(
    decoder: D,
) -> std::result::Result<Box<Command>, D::Error> {
    // A local proposal wraps exactly one unwrapped command (an application
    // command or a staging receipt). Keep the existing enum positions on disk
    // and reject recursive wrappers before the decoder can recurse through an
    // authenticated peer's frame.
    #[derive(Deserialize)]
    #[serde(remote = "Command")]
    enum Application {
        Create,
        Seal {
            expected: Epoch,
            writer: uuid::Uuid,
            owner: String,
        },
        Append {
            fence: Fence,
            owner: String,
            at: Lsn,
            payload: Bytes,
        },
        Trim {
            fence: Fence,
            owner: String,
            through: Lsn,
        },
        Delete,
        Stage(Stage),
        StageOwned(Stage),
        // Holds the wrapper's position. Its body is refused before decoding.
        Admitted(
            uuid::Uuid,
            #[serde(deserialize_with = "refuse_nested")] Box<Command>,
        ),
        AppendBatch {
            fence: Fence,
            owner: String,
            at: Lsn,
            payloads: Vec<Bytes>,
        },
        AppendOriginal {
            fence: Fence,
            owner: String,
            at: Lsn,
            record: Bytes,
        },
        Recover(Stage),
        AcknowledgeRecovery,
        AcknowledgeRecoveryWithMarker {
            fence: RecoveryFence,
            at: Lsn,
            payload: Bytes,
        },
        SealSession {
            expected_writer_epoch: Epoch,
            writer_session_id: WriterSessionId,
            owner: String,
        },
        Offloaded {
            lineage: u64,
            through: Lsn,
            retain_from: Lsn,
        },
        Restore(Restore),
        InstallCheckpoint {
            fence: Fence,
            owner: String,
            checkpoint: CheckpointInstallation,
        },
        SelectCheckpoint {
            fence: Fence,
            owner: String,
            anchor: CheckpointAnchor,
        },
        RecoverRecorded {
            stage: Stage,
            record: RecoveryRecord,
            exact: bool,
        },
        RecoveryEntry {
            fence: RecoveryFence,
            at: Lsn,
            entry: Bytes,
        },
        CheckpointCustody(CheckpointCustody),
    }
    Application::deserialize(decoder).map(Box::new)
}

fn refuse_nested<'de, D: serde::Deserializer<'de>>(
    _decoder: D,
) -> std::result::Result<Box<Command>, D::Error> {
    Err(serde::de::Error::custom("nested application ticket"))
}

impl Command {
    pub fn body(&self) -> &Self {
        match self {
            Self::Admitted(_, command) => command,
            command => command,
        }
    }

    pub fn into_body(self) -> Self {
        match self {
            Self::Admitted(_, command) => *command,
            command => command,
        }
    }
}

/// Names the command without its payloads, which may be megabytes.
impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Create => f.write_str("Create"),
            Self::Seal { expected, .. } => write!(f, "Seal({expected:?})"),
            Self::SealSession {
                expected_writer_epoch,
                ..
            } => {
                write!(f, "SealSession({expected_writer_epoch:?})")
            }
            Self::Append { at, payload, .. } => {
                write!(f, "Append({at:?}, {} bytes)", payload.len())
            }
            Self::Trim { through, .. } => write!(f, "Trim({through:?})"),
            Self::Delete => f.write_str("Delete"),
            Self::Stage(stage) => write!(f, "Stage({})", stage.source),
            Self::StageOwned(stage) => write!(f, "StageOwned({})", stage.source),
            Self::Admitted(ticket, command) => write!(f, "Admitted({ticket}, {command})"),
            Self::AppendBatch { at, payloads, .. } => {
                write!(f, "AppendBatch({at:?}, {} records)", payloads.len())
            }
            Self::AppendOriginal { at, record, .. } => {
                write!(f, "AppendOriginal({at:?}, {} bytes)", record.len())
            }
            Self::Recover(stage) => write!(f, "Recover({})", stage.source),
            Self::AcknowledgeRecovery => f.write_str("AcknowledgeRecovery"),
            Self::AcknowledgeRecoveryWithMarker { fence, .. } => {
                write!(f, "AcknowledgeRecoveryWithMarker({fence:?})")
            }
            Self::Offloaded {
                lineage, through, ..
            } => write!(f, "Offloaded({lineage}, {through:?})"),
            Self::Restore(restore) => write!(f, "Restore({}, {:?})", restore.lineage, restore.head),
            Self::InstallCheckpoint { checkpoint, .. } => {
                write!(f, "InstallCheckpoint({:?})", checkpoint.checkpoint_lsn)
            }
            Self::SelectCheckpoint { anchor, .. } => {
                write!(f, "SelectCheckpoint({:?})", anchor.announced_at)
            }
            Self::RecoverRecorded { stage, .. } => write!(f, "RecoverRecorded({})", stage.source),
            Self::RecoveryEntry { fence, .. } => write!(f, "RecoveryEntry({fence:?})"),
            Self::CheckpointCustody(custody) => write!(
                f,
                "CheckpointCustody({}, {})",
                custody.hold.operation_id, custody.released
            ),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Outcome {
    Unit,
    Sealed(Sealed),
    At(Lsn),
    Page(#[serde(with = "page_layout")] Page),
    Refused(JournalError),
    Configuration(super::Configuration),
    /// One keeper's signed sync sample for a staged original.
    OriginalSample(Vec<u8>),
    /// The retained evidence of a timed original record.
    OriginalEvidence(Vec<u8>),
    RecoveryFence(Option<RecoveryFence>),
    /// A stream's offload progress, answering `Request::OffloadStatus`.
    /// Added last; never an applied command's outcome.
    Offload(super::OffloadStatus),
    Checkpoint(Option<CheckpointReceipt>),
    /// A page that holds typed recovery entries, on the wire only: `Page`
    /// keeps the N-1 layout, which has no entry kinds, so `for_wire` sends a
    /// page with recovery entries as this and `from_wire` turns it back.
    /// Added last.
    RecoveryPage(Page),
    CheckpointCustody(Option<CheckpointCustody>),
}

impl Outcome {
    /// The outcome as the current wire carries it.
    pub(super) fn for_wire(self) -> Self {
        match self {
            Self::Page(page) if !page.recoveries.is_empty() => Self::RecoveryPage(page),
            outcome => outcome,
        }
    }

    /// The outcome as it arrived on the wire.
    pub(super) fn from_wire(self) -> Self {
        match self {
            Self::RecoveryPage(page) => Self::Page(page),
            outcome => outcome,
        }
    }
}

/// The N-1 layout of a page: no entry kinds. Only pages of client data use
/// it, so nothing is dropped (`Outcome::for_wire`).
pub(super) mod page_layout {
    use bytes::Bytes;
    use journal_contract::{Lsn, Page};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize)]
    struct Borrowed<'a> {
        floor: Lsn,
        records: &'a Vec<(Lsn, Bytes)>,
        head: Lsn,
    }

    #[derive(Deserialize)]
    struct Owned {
        floor: Lsn,
        records: Vec<(Lsn, Bytes)>,
        head: Lsn,
    }

    pub fn serialize<S: Serializer>(page: &Page, serializer: S) -> Result<S::Ok, S::Error> {
        if !page.recoveries.is_empty() {
            return Err(serde::ser::Error::custom(
                "a page with recovery entries needs the current wire",
            ));
        }
        Borrowed {
            floor: page.floor,
            records: &page.records,
            head: page.head,
        }
        .serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Page, D::Error> {
        let page = Owned::deserialize(deserializer)?;
        Ok(Page::new(page.floor, page.records, page.head))
    }
}

impl From<Result<Outcome>> for Outcome {
    fn from(result: Result<Outcome>) -> Self {
        result.unwrap_or_else(Self::Refused)
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub(super) enum State {
    #[default]
    Absent,
    Live(Live),
    Deleted,
    Immutable {
        live: Live,
        sealed_head_lsn: Lsn,
    },
    /// Appended as a separate snapshot variant to preserve the encoding of
    /// immutable histories selected before this release.
    Checkpointed {
        live: Live,
        sealed_head_lsn: Lsn,
        selected: checkpoint::Selection,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct Live {
    writer: Option<(Fence, String)>,
    head: Lsn,
    floor: Lsn,
    bytes: u64,
    #[serde(skip)]
    records: VecDeque<Payload>,
    /// The epochs the retained records were written under. Snapshots
    /// store them beside the image.
    #[serde(skip)]
    epochs: EpochRuns,
    /// Offload progress. Snapshots store it beside the image, like the
    /// epochs, so images without offload keep their format.
    #[serde(skip)]
    offload: Offload,
    /// The catalog's record of the recovery whose fence stands, until its
    /// typed entry is written. Snapshots store it beside the image.
    #[serde(skip)]
    recorded: Option<Recorded>,
    #[serde(skip)]
    checkpoint_custody: Option<CheckpointCustody>,
    /// What a retry's `Written` lookup needs of every operator recovery
    /// the stream had. Snapshots store it beside the image once the
    /// cluster finalized `CLUSTER_VERSION_RETRY_RECOVERY`.
    #[serde(skip)]
    recoveries: Option<Recoveries>,
}

/// The summary of every operator recovery of a stream that decides a
/// retry across them (`decisions::written_step`): unlike the typed entries,
/// it survives trims.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Recoveries {
    /// The fence epoch of the latest recovery. Every writer below it sealed
    /// before some recovery.
    pub epoch: Epoch,
    /// The lowest loss point of any recovery: records above it that a
    /// writer below `epoch` was acknowledged may have been erased.
    pub loss_point: Lsn,
}

impl Recoveries {
    /// The summary `held` after also absorbing a recovery fenced at `epoch`
    /// that kept the records through `loss_point`.
    pub fn absorb(held: Option<Self>, epoch: Epoch, loss_point: Lsn) -> Self {
        let (epoch, loss_point) = super::decisions::absorb_recovery(
            held.is_some(),
            held.map_or(0, |held| held.epoch.0),
            held.map_or(0, |held| held.loss_point.0),
            epoch.0,
            loss_point.0,
        );
        Self {
            epoch: Epoch(epoch),
            loss_point: Lsn(loss_point),
        }
    }
}

/// A recorded recovery waiting for its typed entry: the catalog's record and
/// whether its loss point is exact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Recorded {
    pub record: RecoveryRecord,
    pub exact: bool,
}

/// One stream's offload progress.
///
/// `Live::floor` is the first record this keeper holds. The logical floor,
/// below which the writer trimmed, is `floor` here when retention dropped
/// offloaded records above it, and `Live::floor` otherwise. Records from
/// the logical floor up to `Live::floor` are read from the store.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Offload {
    /// The last LSN durably uploaded, or 0.
    pub through: Lsn,
    /// The logical floor, when below the local one.
    pub floor: Option<Lsn>,
    /// The current lineage. Lineage 0 starts at LSN 1.
    pub lineage: u64,
    /// The lineages after the first, each with the first LSN its objects
    /// are authoritative for, ascending.
    pub lineages: Vec<(u64, Lsn)>,
}

impl Default for Offload {
    fn default() -> Self {
        Self {
            through: Lsn(0),
            floor: None,
            lineage: 0,
            lineages: Vec::new(),
        }
    }
}

impl Offload {
    /// Every lineage with the first LSN it is authoritative for.
    pub fn map(&self) -> Vec<(u64, Lsn)> {
        let mut map = vec![(0, Lsn(1))];
        map.extend(self.lineages.iter().copied());
        map
    }

    /// The lineage whose objects hold `at`, and the last LSN they are
    /// authoritative for.
    pub fn lineage_of(&self, at: Lsn) -> (u64, Lsn) {
        let map = self.map();
        let index = map
            .partition_point(|(_, from)| *from <= at)
            .saturating_sub(1);
        let end = map
            .get(index + 1)
            .map_or(Lsn(u64::MAX), |(_, next)| Lsn(next.0 - 1));
        (map[index].0, end)
    }

    fn valid(&self, floor: Lsn, head: Lsn) -> bool {
        self.through <= head
            && self
                .floor
                .is_none_or(|logical| logical >= Lsn(1) && logical < floor)
            && self.lineages.last().map_or(0, |(lineage, _)| *lineage) == self.lineage
            && self
                .map()
                .windows(2)
                .all(|pair| pair[0].0 < pair[1].0 && pair[0].1 <= pair[1].1)
    }
}

/// A read page of records this keeper no longer holds: they are read from
/// the offload store's `lineage` objects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Remote {
    pub lineage: u64,
    pub from: Lsn,
    /// The last LSN to read from the store: below the local floor and
    /// within the lineage.
    pub until: Lsn,
    pub floor: Lsn,
    pub head: Lsn,
}

pub(super) enum TimedRecord {
    Local(Payload),
    Offloaded(Remote),
}

/// What the uploader needs from a stream's applied state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct OffloadView {
    pub offload: Offload,
    pub logical_floor: Lsn,
    pub local_floor: Lsn,
    pub head: Lsn,
    pub epoch: Epoch,
}

/// The most epoch runs a stream retains. A writer that seals more often
/// than this between trims forgets the epochs of its oldest records.
pub(super) const MAX_EPOCH_RUNS: usize = 1024;

/// The epochs retained records were written under, as runs: the first LSN
/// of each run and the epoch of its writer. Records before the first run
/// have no known epoch: an image that predates the runs restored them, or
/// more than `MAX_EPOCH_RUNS` runs followed them.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct EpochRuns(VecDeque<(Lsn, Epoch)>);

impl EpochRuns {
    /// The epoch the record at `at` was written under, when known.
    pub fn epoch(&self, at: Lsn) -> Option<Epoch> {
        let runs = self.0.partition_point(|(first, _)| *first <= at);
        runs.checked_sub(1).map(|run| self.0[run].1)
    }

    /// The runs that cover `first..=last`, the first starting at `first`
    /// when its epoch is known.
    pub fn covering(&self, first: Lsn, last: Lsn) -> Vec<(Lsn, Epoch)> {
        let mut runs = Vec::new();
        if let Some(epoch) = self.epoch(first) {
            runs.push((first, epoch));
        }
        runs.extend(
            self.0
                .iter()
                .filter(|(start, _)| *start > first && *start <= last)
                .copied(),
        );
        runs
    }

    /// Notes records written from `at` under `epoch`.
    fn note(&mut self, at: Lsn, epoch: Epoch) {
        if self.0.back().is_some_and(|(_, last)| *last == epoch) {
            return;
        }
        self.0.push_back((at, epoch));
        if self.0.len() > MAX_EPOCH_RUNS {
            self.0.pop_front();
        }
    }

    /// Forgets runs that end below `floor`.
    fn trim(&mut self, floor: Lsn) {
        while self.0.len() > 1 && self.0[1].0 <= floor {
            self.0.pop_front();
        }
    }

    /// Whether these runs can describe records retained up to `head`.
    fn valid(&self, head: Lsn) -> bool {
        self.0.len() <= MAX_EPOCH_RUNS
            && self
                .0
                .iter()
                .all(|(first, _)| first.0 >= 1 && *first <= head)
            && self
                .0
                .iter()
                .zip(self.0.iter().skip(1))
                .all(|(run, next)| run.0 < next.0 && run.1 < next.1)
    }
}

#[derive(Clone, Debug)]
pub(super) enum Payload {
    Extent {
        object: Arc<super::storage::Object>,
        offset: u64,
        len: u32,
        crc: u32,
        kind: RecordKind,
    },
    Snapshot {
        file: Arc<Mutex<File>>,
        digest: [u8; 32],
        offset: u64,
        len: u32,
        crc: u32,
        kind: RecordKind,
    },
}

/// Marks a timed record in snapshot and wire record lengths. Records are at
/// most 4 MiB, so the bit is free, and an older reader refuses it as an
/// oversized record instead of reading evidence as payload.
pub(super) const TIMED_RECORD: u32 = 1 << 31;
/// Marks a typed recovery entry in the same lengths. An older reader
/// refuses it as an oversized record, so it never serves one as data.
pub(super) const RECOVERY_RECORD: u32 = 1 << 30;

/// What a retained record is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RecordKind {
    /// Client data.
    #[default]
    Data,
    /// A timed original: its evidence, then client data.
    Timed,
    /// A typed recovery entry's canonical encoding. Never client data.
    Recovery,
}

impl From<RetainedKind> for RecordKind {
    fn from(kind: RetainedKind) -> Self {
        match kind {
            RetainedKind::Data => Self::Data,
            RetainedKind::Timed => Self::Timed,
            RetainedKind::Recovery => Self::Recovery,
        }
    }
}

impl RecordKind {
    /// The bits this kind sets in a framed record length.
    pub(super) fn flag(self) -> u32 {
        match self {
            Self::Data => 0,
            Self::Timed => TIMED_RECORD,
            Self::Recovery => RECOVERY_RECORD,
        }
    }

    /// Splits a framed record length into the kind and the length. `None`
    /// when it sets more than one kind.
    pub(super) fn split(len: u32) -> Option<(Self, u32)> {
        let kind = match len & (TIMED_RECORD | RECOVERY_RECORD) {
            0 => Self::Data,
            TIMED_RECORD => Self::Timed,
            RECOVERY_RECORD => Self::Recovery,
            _ => return None,
        };
        Some((kind, len & !(TIMED_RECORD | RECOVERY_RECORD)))
    }

    /// Whether a record of `len` bytes can be of this kind.
    pub(super) fn fits(self, len: usize) -> bool {
        len <= MAX_RECORD
            && match self {
                Self::Data => true,
                Self::Timed => len > EVIDENCE_BYTES,
                Self::Recovery => len >= RecoveryEntry::HEADER_BYTES,
            }
    }
}

impl Payload {
    pub(super) fn kind(&self) -> RecordKind {
        match self {
            Self::Extent { kind, .. } | Self::Snapshot { kind, .. } => *kind,
        }
    }

    pub(super) fn timed(&self) -> bool {
        self.kind() == RecordKind::Timed
    }

    /// The application payload. A timed record drops its evidence prefix.
    pub fn contents(&self) -> io::Result<Bytes> {
        let record = self.load()?;
        if self.timed() {
            return record
                .get(EVIDENCE_BYTES..)
                .map(|payload| record.slice_ref(payload))
                .ok_or_else(|| super::invalid("short retained timed record"));
        }
        Ok(record)
    }

    pub(super) fn len(&self) -> usize {
        match self {
            Self::Extent { len, .. } | Self::Snapshot { len, .. } => *len as usize,
        }
    }

    pub fn load(&self) -> io::Result<Bytes> {
        let mut bytes = vec![0; self.len()];
        let crc = match self {
            Self::Extent {
                object,
                offset,
                crc,
                ..
            } => {
                object.read_range(*offset, &mut bytes)?;
                *crc
            }
            Self::Snapshot {
                file, offset, crc, ..
            } => {
                let mut file = file.lock();
                file.seek(SeekFrom::Start(*offset))?;
                file.read_exact(&mut bytes)?;
                *crc
            }
        };
        if crc32fast::hash(&bytes) != crc {
            return Err(super::invalid("retained record checksum changed"));
        }
        Ok(Bytes::from(bytes))
    }
}

pub(super) struct ReadPage {
    floor: Lsn,
    head: Lsn,
    records: Vec<(Lsn, Payload)>,
}

impl ReadPage {
    pub fn needs_disk(&self) -> bool {
        !self.records.is_empty()
    }

    pub fn load(self) -> io::Result<Page> {
        let mut recoveries = Vec::new();
        let records = self
            .records
            .into_iter()
            .map(|(lsn, payload)| {
                let bytes = payload.contents()?;
                if payload.kind() == RecordKind::Recovery {
                    recoveries.push((lsn, recovery_entry(&bytes)?));
                }
                Ok((lsn, bytes))
            })
            .collect::<io::Result<_>>()?;
        Ok(Page {
            floor: self.floor,
            records,
            head: self.head,
            recoveries,
        })
    }
}

/// Decodes a retained recovery entry; damaged bytes are corruption.
pub(super) fn recovery_entry(bytes: &Bytes) -> io::Result<RecoveryEntry> {
    RecoveryEntry::decode(bytes).ok_or_else(|| super::invalid("retained recovery entry is damaged"))
}

impl State {
    pub fn apply(
        &mut self,
        command: Command,
        genesis: &Genesis,
        segment: Arc<super::storage::Object>,
    ) -> io::Result<Outcome> {
        if let Command::CheckpointCustody(custody) = command {
            return Ok(self
                .change_checkpoint_custody(custody)
                .unwrap_or_else(Outcome::Refused));
        }
        if let Command::InstallCheckpoint {
            fence,
            owner,
            checkpoint,
        } = command
        {
            return self.install_checkpoint(fence, &owner, checkpoint, segment, genesis);
        }
        if let Command::RecoveryEntry { fence, at, entry } = command {
            if genesis.immutable {
                return Ok(Outcome::Refused(JournalError::Unsupported));
            }
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
            return live.write_recovery_entry(fence, at, entry, segment, genesis.quota_bytes);
        }
        if let Command::AcknowledgeRecoveryWithMarker { fence, at, payload } = command {
            if genesis.immutable {
                return Ok(Outcome::Refused(JournalError::Unsupported));
            }
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
            // A recorded recovery clears only by writing its typed entry.
            if live.recorded.is_some() {
                return Ok(Outcome::Refused(JournalError::Conflict { head: live.head }));
            }
            return live.acknowledge_with_marker(fence, at, payload, segment, genesis.quota_bytes);
        }
        if let Command::Append {
            fence,
            owner,
            at,
            payload,
        } = command
        {
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
            if let Err(error) = live.require_writer(fence, &owner) {
                return Ok(Outcome::Refused(error));
            }
            if at >= live.floor && at <= live.head {
                let retained = &live.records[(at.0 - live.floor.0) as usize];
                // An identical retry repeats this epoch's record; the same
                // bytes an earlier epoch wrote conflict, as in the contract.
                // A record of unknown epoch is judged by its bytes alone.
                return Ok(
                    if retained.kind() == RecordKind::Data
                        && match live.epochs.epoch(at) {
                            Some(epoch) => epoch == fence.epoch,
                            None => !genesis.immutable,
                        }
                        && retained.len() == payload.len()
                        && retained.load()? == payload
                    {
                        Outcome::At(at)
                    } else {
                        Outcome::Refused(JournalError::Conflict { head: live.head })
                    },
                );
            }
            let len = payload.len() as u32;
            let offset = segment.len().checked_sub(u64::from(len)).ok_or_else(|| {
                super::invalid("accepted WAL extent does not contain the payload")
            })?;
            let retained = Payload::Extent {
                object: segment,
                offset,
                len,
                crc: crc32fast::hash(&payload),
                kind: super::decisions::retained_kind(RecordOrigin::Append).into(),
            };
            return Ok(live.append(at, retained, genesis.quota_bytes).into());
        }
        if let Command::AppendOriginal {
            fence,
            owner,
            at,
            record,
        } = command
        {
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
            if let Err(error) = live.require_writer(fence, &owner) {
                return Ok(Outcome::Refused(error));
            }
            // The leader verified the signatures before proposing. The state
            // machine checks only what every replica derives identically.
            let structural = record.len() > EVIDENCE_BYTES
                && record.len() <= MAX_RECORD
                && TimedEvidence::decode(&record[..EVIDENCE_BYTES]).is_some_and(|evidence| {
                    let original = evidence.origin.original;
                    original.stream.0 == genesis.stream.0
                        && original.epoch.0 == fence.epoch.0
                        && original.at.0 == at.0
                        && original.matches(&record[EVIDENCE_BYTES..])
                });
            if !structural {
                return Ok(Outcome::Refused(JournalError::Unavailable));
            }
            if at >= live.floor && at <= live.head {
                let retained = &live.records[(at.0 - live.floor.0) as usize];
                return Ok(
                    if retained.timed()
                        && retained.len() == record.len()
                        && retained.load()? == record
                    {
                        Outcome::At(at)
                    } else {
                        Outcome::Refused(JournalError::Conflict { head: live.head })
                    },
                );
            }
            let len = record.len() as u32;
            let offset = segment
                .len()
                .checked_sub(u64::from(len))
                .ok_or_else(|| super::invalid("accepted WAL extent does not contain the record"))?;
            let retained = Payload::Extent {
                object: segment,
                offset,
                len,
                crc: crc32fast::hash(&record),
                kind: super::decisions::retained_kind(RecordOrigin::Timed).into(),
            };
            return Ok(live.append(at, retained, genesis.quota_bytes).into());
        }
        if let Command::AppendBatch {
            fence,
            owner,
            at,
            payloads,
        } = command
        {
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
            if let Err(error) = live.require_writer(fence, &owner) {
                return Ok(Outcome::Refused(error));
            }
            if !valid_batch(&payloads) {
                return Ok(Outcome::Refused(JournalError::TooLarge { max: MAX_RECORD }));
            }
            // The fixed-width encoding places an 8-byte length before each
            // payload, and the payloads end the durable entry.
            let mut end = segment.len();
            let mut extents = Vec::with_capacity(payloads.len());
            for payload in payloads.iter().rev() {
                let offset = end.checked_sub(payload.len() as u64).ok_or_else(|| {
                    super::invalid("accepted WAL extent does not contain the batch")
                })?;
                extents.push(offset);
                end = offset.checked_sub(8).ok_or_else(|| {
                    super::invalid("accepted WAL extent does not contain the batch")
                })?;
            }
            extents.reverse();
            return Ok(live
                .append_batch(at, payloads, &extents, &segment, genesis)?
                .into());
        }
        Ok(self.decide(command, genesis).into())
    }

    fn decide(&mut self, command: Command, genesis: &Genesis) -> Result<Outcome> {
        if matches!(command, Command::Create) {
            return match self {
                Self::Absent => {
                    let live = Live {
                        writer: None,
                        head: Lsn(0),
                        floor: Lsn(1),
                        bytes: 0,
                        records: VecDeque::new(),
                        epochs: EpochRuns::default(),
                        offload: Offload::default(),
                        recorded: None,
                        checkpoint_custody: None,
                        recoveries: None,
                    };
                    *self = if genesis.immutable {
                        Self::Immutable {
                            live,
                            sealed_head_lsn: Lsn(0),
                        }
                    } else {
                        Self::Live(live)
                    };
                    Ok(Outcome::Unit)
                }
                Self::Live(_) | Self::Immutable { .. } | Self::Checkpointed { .. } => {
                    Ok(Outcome::Unit)
                }
                Self::Deleted => Err(JournalError::Deleted),
            };
        }
        if matches!(command, Command::Delete) && matches!(self, Self::Deleted) {
            return Ok(Outcome::Unit);
        }
        if let Command::SealSession {
            expected_writer_epoch,
            writer_session_id,
            owner,
        } = command
        {
            return self.seal_session(expected_writer_epoch, writer_session_id, owner);
        }
        if let Command::SelectCheckpoint {
            fence,
            owner,
            anchor,
        } = command
        {
            return self.select_announcement(fence, &owner, anchor);
        }
        if matches!(
            (&*self, &command),
            (Self::Checkpointed { .. }, Command::Trim { .. })
        ) {
            return Err(JournalError::Unsupported);
        }
        let live = self.live_mut()?;
        if live.holds_checkpoint()
            && matches!(
                command,
                Command::Delete | Command::Trim { .. } | Command::Offloaded { .. }
            )
        {
            return Err(JournalError::Conflict { head: live.head });
        }
        match command {
            Command::Seal {
                expected,
                writer,
                owner,
            } if !genesis.immutable => live.seal(expected, writer, owner),
            Command::Seal { .. } => Err(JournalError::Unsupported),
            Command::Trim {
                fence,
                owner,
                through,
            } => {
                live.require_writer(fence, &owner)?;
                live.trim(through)
            }
            Command::Delete => {
                *self = Self::Deleted;
                Ok(Outcome::Unit)
            }
            // A recorded recovery clears only by writing its typed entry.
            Command::AcknowledgeRecovery if live.recorded.is_some() => {
                Err(JournalError::Conflict { head: live.head })
            }
            Command::AcknowledgeRecovery if !genesis.immutable => live.acknowledge_recovery(),
            Command::AcknowledgeRecovery => Err(JournalError::Unsupported),
            Command::Offloaded {
                lineage,
                through,
                retain_from,
            } => Ok(live.offloaded(lineage, through, retain_from)),
            // An immutable history is never rewritten, but a restore or
            // import into a fresh immutable stream, never sealed or
            // written, creates it with the source's records.
            Command::Restore(restore)
                if genesis.immutable && !(restore.replace && live.fresh()) =>
            {
                Err(JournalError::Unsupported)
            }
            Command::Restore(restore) => Ok(live.restore(restore)),
            Command::SealSession { .. }
            | Command::Create
            | Command::Append { .. }
            | Command::Stage(_)
            | Command::StageOwned(_)
            | Command::Recover(_)
            | Command::Admitted(..)
            | Command::AppendBatch { .. }
            | Command::AppendOriginal { .. }
            | Command::AcknowledgeRecoveryWithMarker { .. }
            | Command::InstallCheckpoint { .. }
            | Command::SelectCheckpoint { .. }
            | Command::RecoverRecorded { .. }
            | Command::RecoveryEntry { .. }
            | Command::CheckpointCustody(_) => unreachable!(),
        }
    }

    fn seal_session(
        &mut self,
        expected_writer_epoch: Epoch,
        writer_session_id: WriterSessionId,
        owner: String,
    ) -> Result<Outcome> {
        let (Self::Immutable {
            live,
            sealed_head_lsn,
        }
        | Self::Checkpointed {
            live,
            sealed_head_lsn,
            ..
        }) = self
        else {
            self.live()?;
            return Err(JournalError::Unsupported);
        };
        let current = live.epoch();
        let epoch = expected_writer_epoch
            .0
            .checked_add(1)
            .map(Epoch)
            .ok_or(JournalError::Fenced { current })?;
        let writer = uuid::Uuid::from_u128(writer_session_id.0);
        if !super::decisions::client_may_seal_as(writer.is_nil(), writer == RECOVERY_WRITER)
            || owner.is_empty()
        {
            return Err(JournalError::Fenced { current });
        }
        let fence = Fence { epoch, writer };
        if expected_writer_epoch == current {
            live.writer = Some((fence, owner));
            *sealed_head_lsn = live.head;
        } else {
            live.require_writer(fence, &owner)?;
        }
        Ok(Outcome::Sealed(Sealed {
            fence,
            head: *sealed_head_lsn,
        }))
    }

    pub fn head(&self) -> Result<Lsn> {
        Ok(self.live()?.head)
    }

    /// Installs the recovery fence above the current epoch.
    pub fn recover(&mut self) -> Result<Outcome> {
        if matches!(self, Self::Immutable { .. } | Self::Checkpointed { .. }) {
            return Err(JournalError::Unsupported);
        }
        let live = self.live_mut()?;
        let epoch = super::decisions::recovery_epoch(live.epoch().0)
            .map(Epoch)
            .ok_or(JournalError::Unavailable)?;
        let fence = Fence {
            epoch,
            writer: RECOVERY_WRITER,
        };
        live.writer = Some((fence, String::new()));
        live.recoveries = Some(Recoveries::absorb(live.recoveries, epoch, live.head));
        Ok(Outcome::Sealed(Sealed {
            fence,
            head: live.head,
        }))
    }

    /// Installs the recovery fence as `recover` and records the catalog's
    /// record of the recovery, which the fence's typed entry carries.
    pub fn recover_recorded(&mut self, recorded: Recorded) -> Result<Outcome> {
        let outcome = self.recover()?;
        let live = self.live_mut()?;
        live.recorded = Some(recorded);
        live.recoveries = Some(Recoveries::absorb(
            live.recoveries,
            live.epoch(),
            recorded.record.loss_point,
        ));
        Ok(outcome)
    }

    /// The summary of the stream's operator recoveries, if it had any.
    pub fn recoveries(&self) -> Option<Recoveries> {
        self.live().ok()?.recoveries
    }

    /// Restores the recovery summary a snapshot stored beside its image.
    pub fn restore_recoveries(&mut self, recoveries: Option<Recoveries>) -> io::Result<()> {
        match (self.live_mut(), recoveries) {
            (_, None) => Ok(()),
            (Ok(live), Some(recoveries)) if recoveries.loss_point <= live.head => {
                live.recoveries = Some(recoveries);
                Ok(())
            }
            _ => Err(super::invalid("invalid recovery summary")),
        }
    }

    /// Every retained typed recovery entry, for a `Written` lookup below
    /// the level that keeps the recovery summary durable.
    pub fn retained_recovery_entries(&self) -> Vec<Payload> {
        self.records()
            .filter(|record| record.kind() == RecordKind::Recovery)
            .cloned()
            .collect()
    }

    /// The standing recovery fence and the catalog's record of it, when a
    /// recorded recovery waits for its typed entry.
    pub fn recorded_recovery(&self) -> Option<(RecoveryFence, Recorded)> {
        let live = self.live().ok()?;
        let record = live.recorded?;
        live.recovering().then(|| {
            (
                RecoveryFence {
                    epoch: live.epoch(),
                    head: live.head,
                },
                record,
            )
        })
    }

    /// The recorded recovery, for a snapshot.
    pub fn recorded(&self) -> Option<Recorded> {
        self.live().ok()?.recorded
    }

    /// Restores the recorded recovery a snapshot stored beside its image.
    pub fn restore_recorded(&mut self, recorded: Option<Recorded>) -> io::Result<()> {
        match (self.live_mut(), recorded) {
            (_, None) => Ok(()),
            (Ok(live), Some(record)) if live.recovering() => {
                live.recorded = Some(record);
                Ok(())
            }
            _ => Err(super::invalid("recorded recovery without its fence")),
        }
    }

    /// Whether an unacknowledged operator recovery fences the stream.
    pub fn recovering(&self) -> bool {
        self.live().is_ok_and(Live::recovering)
    }

    pub fn recovery_fence(&self) -> Result<Option<RecoveryFence>> {
        let live = self.live()?;
        Ok(live.recovering().then(|| RecoveryFence {
            epoch: live.epoch(),
            head: live.head,
        }))
    }

    pub fn read(&self, from: Lsn, limit: usize) -> Result<ReadPage> {
        self.live()?.read(from, limit)
    }

    /// Where a read from `from` must go when this keeper no longer holds
    /// the record: the store's objects of its lineage. `None` when the
    /// record is held locally, trimmed, or past the head.
    pub fn remote(&self, from: Lsn) -> Option<Remote> {
        self.live().ok()?.remote(from)
    }

    /// The applied offload progress, for the uploader.
    pub fn offload_view(&self) -> Option<OffloadView> {
        let live = self.live().ok()?;
        Some(OffloadView {
            offload: live.offload.clone(),
            logical_floor: live.logical_floor(),
            local_floor: live.floor,
            head: live.head,
            epoch: live.epoch(),
        })
    }

    /// The retained records from `from`, at most `max_bytes` of them (at
    /// least one), with the epoch runs that cover them.
    pub fn offload_records(
        &self,
        from: Lsn,
        max_bytes: u64,
    ) -> Result<(Vec<(Lsn, Payload)>, Vec<(Lsn, Epoch)>)> {
        let live = self.live()?;
        if from < live.floor {
            return Err(JournalError::Trimmed { floor: live.floor });
        }
        let mut records = Vec::new();
        let mut bytes = 0u64;
        for (index, payload) in live
            .records
            .iter()
            .enumerate()
            .skip((from.0 - live.floor.0) as usize)
        {
            if !records.is_empty() && bytes + payload.len() as u64 > max_bytes {
                break;
            }
            bytes += payload.len() as u64;
            records.push((Lsn(live.floor.0 + index as u64), payload.clone()));
        }
        let epochs = match (records.first(), records.last()) {
            (Some((first, _)), Some((last, _))) => live.epochs.covering(*first, *last),
            _ => Vec::new(),
        };
        Ok((records, epochs))
    }

    /// About how many retained bytes lie from `from` through the head: the
    /// record count times the stream's average retained charge, in constant
    /// time, since the uploader asks every 100 ms for every stream it leads.
    pub fn waiting_bytes(&self, from: Lsn) -> u64 {
        self.live().ok().map_or(0, |live| {
            let from = from.max(live.floor);
            if from > live.head || live.records.is_empty() {
                return 0;
            }
            let count = live.head.0 - from.0 + 1;
            count.saturating_mul(live.bytes / live.records.len() as u64)
        })
    }

    /// The local floor that keeps at least the newest `bytes` retained
    /// bytes: the lowest LSN whose suffix through the head holds no more.
    pub fn retention_floor(&self, bytes: u64) -> Lsn {
        let Ok(live) = self.live() else {
            return Lsn(0);
        };
        let mut kept = 0u64;
        let mut floor = live.head.0 + 1;
        for payload in live.records.iter().rev() {
            kept += payload.len() as u64;
            if kept > bytes {
                break;
            }
            floor -= 1;
        }
        Lsn(floor)
    }

    /// The offload progress, for a snapshot.
    pub fn offload(&self) -> Offload {
        self.live()
            .ok()
            .map_or_else(Offload::default, |live| live.offload.clone())
    }

    /// Restores the offload progress a snapshot stored beside its image.
    pub fn restore_offload(&mut self, offload: Offload) -> io::Result<()> {
        if let Self::Live(live) = self {
            if !offload.valid(live.floor, live.head) {
                return Err(super::invalid("invalid offload progress"));
            }
            live.offload = offload;
        } else if offload != Offload::default() {
            return Err(super::invalid("offload progress without a live stream"));
        }
        Ok(())
    }

    /// The sealed writer fence and principal, when a writer holds the stream.
    pub fn writer(&self) -> Option<(Fence, &str)> {
        let (fence, owner) = self.live().ok()?.writer.as_ref()?;
        Some((*fence, owner))
    }

    /// Selects the proof's source and retention boundary from one applied image.
    pub fn timed_record(&self, at: Lsn) -> Result<TimedRecord> {
        let live = self.live()?;
        let floor = live.logical_floor();
        if at < floor {
            return Err(JournalError::Trimmed { floor });
        }
        if at > live.head {
            return Err(JournalError::Conflict { head: live.head });
        }
        if let Some(remote) = live.remote(at) {
            return Ok(TimedRecord::Offloaded(remote));
        }
        let record = &live.records[(at.0 - live.floor.0) as usize];
        if !record.timed() {
            return Err(JournalError::Unavailable);
        }
        Ok(TimedRecord::Local(record.clone()))
    }

    /// The bytes a new timed record of `payload_len` would charge, if the
    /// stream can still hold it.
    pub fn fits_timed(&self, payload_len: usize, quota_bytes: u64) -> bool {
        self.live().is_ok_and(|live| {
            super::decisions::retains_record(
                false,
                live.records.len(),
                MAX_RETAINED_RECORDS,
                live.bytes,
                record_charge(EVIDENCE_BYTES + payload_len),
                quota_bytes,
            )
        })
    }

    pub fn records(&self) -> impl Iterator<Item = &Payload> {
        self.live().ok().into_iter().flat_map(|live| &live.records)
    }

    pub fn snapshot_bytes(&self) -> u64 {
        self.live().ok().map_or(0, |live| {
            live.bytes
                .saturating_add((live.records.len() as u64).saturating_mul(8))
        })
    }

    pub fn retained_floor(&self) -> Lsn {
        self.live().ok().map_or(Lsn(1), |live| live.floor)
    }

    /// The last typed recovery entry this copy retains, with its position.
    pub fn last_recovery_entry(&self) -> io::Result<Option<(Lsn, RecoveryEntry)>> {
        let Ok(live) = self.live() else {
            return Ok(None);
        };
        let Some((index, record)) = live
            .records
            .iter()
            .enumerate()
            .rev()
            .find(|(_, record)| record.kind() == RecordKind::Recovery)
        else {
            return Ok(None);
        };
        let entry = RecoveryEntry::decode(&record.load()?)
            .ok_or_else(|| super::invalid("retained recovery entry does not decode"))?;
        Ok(Some((Lsn(live.floor.0 + index as u64), entry)))
    }

    /// Retained record count and byte charge for a live stream, or `(0, 0)`.
    pub fn retained_stats(&self) -> (u64, u64) {
        self.live()
            .ok()
            .map_or((0, 0), |live| (live.records.len() as u64, live.bytes))
    }

    pub fn matches_genesis(&self, genesis: &Genesis) -> bool {
        match self {
            Self::Absent | Self::Deleted => true,
            Self::Live(_) => !genesis.immutable,
            Self::Immutable {
                live,
                sealed_head_lsn,
            }
            | Self::Checkpointed {
                live,
                sealed_head_lsn,
                ..
            } => {
                genesis.immutable
                    && *sealed_head_lsn <= live.head
                    && self.selection().is_none_or(|selected| selected.valid(live))
                    && match &live.writer {
                        Some((fence, owner)) => {
                            fence.epoch != Epoch(0)
                                && !fence.writer.is_nil()
                                && fence.writer != RECOVERY_WRITER
                                && !owner.is_empty()
                        }
                        None => *sealed_head_lsn == Lsn(0) && live.head == Lsn(0),
                    }
            }
        }
    }

    pub fn is_deleted(&self) -> bool {
        matches!(self, Self::Deleted)
    }

    pub fn record_count(&self) -> io::Result<u64> {
        let Ok(live) = self.live() else { return Ok(0) };
        live.head
            .0
            .checked_add(1)
            .and_then(|end| end.checked_sub(live.floor.0))
            .filter(|_| live.floor.0 != 0)
            .ok_or_else(|| super::invalid("invalid retained snapshot interval"))
    }

    pub fn restore_records(&mut self, records: VecDeque<Payload>, quota: u64) -> io::Result<()> {
        if let Ok(live) = self.live_mut() {
            let bytes = records
                .iter()
                .map(|record| record_charge(record.len()))
                .sum::<u64>();
            if live.bytes != bytes
                || bytes > quota_with_headroom(quota)
                || records.len() > MAX_RETAINED_WITH_HEADROOM
            {
                return Err(super::invalid("invalid retained snapshot quota"));
            }
            live.records = records;
        }
        Ok(())
    }

    /// The retained records from `at` that a writer of `epoch` appended, for
    /// checking whether an append whose reply was lost took effect.
    /// `Conflict` when another writer's records, or none, hold one of those
    /// positions; `Unavailable` when a record is trimmed or of unknown
    /// epoch, so the outcome stays unknown.
    pub fn written(&self, epoch: Epoch, at: Lsn, count: usize) -> Result<Vec<Payload>> {
        let live = self.live()?;
        let conflict = JournalError::Conflict { head: live.head };
        let last =
            at.0.checked_add(count as u64)
                .and_then(|end| end.checked_sub(1))
                .ok_or(conflict.clone())?;
        if count == 0 || at.0 == 0 {
            return Err(conflict);
        }
        if at < live.floor {
            return Err(JournalError::Unavailable);
        }
        if last > live.head.0 {
            return Err(conflict);
        }
        let mut records = Vec::with_capacity(count);
        for lsn in at.0..=last {
            let record = &live.records[(lsn - live.floor.0) as usize];
            match live.epochs.epoch(Lsn(lsn)) {
                None => return Err(JournalError::Unavailable),
                Some(written) if written != epoch || record.kind() != RecordKind::Data => {
                    return Err(conflict);
                }
                Some(_) => records.push(record.clone()),
            }
        }
        Ok(records)
    }

    /// The epochs of the retained records, for a snapshot.
    pub fn epoch_runs(&self) -> EpochRuns {
        self.live()
            .ok()
            .map_or_else(EpochRuns::default, |live| live.epochs.clone())
    }

    /// Restores the epochs a snapshot stored beside its image.
    pub fn restore_epochs(&mut self, epochs: EpochRuns) -> io::Result<()> {
        if let Ok(live) = self.live_mut() {
            if !epochs.valid(live.head) {
                return Err(super::invalid("invalid retained epoch runs"));
            }
            live.epochs = epochs;
        } else if epochs != EpochRuns::default() {
            return Err(super::invalid("epoch runs without a live stream"));
        }
        Ok(())
    }

    fn live(&self) -> Result<&Live> {
        match self {
            Self::Absent => Err(JournalError::NotFound),
            Self::Live(live) | Self::Immutable { live, .. } | Self::Checkpointed { live, .. } => {
                Ok(live)
            }
            Self::Deleted => Err(JournalError::Deleted),
        }
    }

    fn live_mut(&mut self) -> Result<&mut Live> {
        match self {
            Self::Absent => Err(JournalError::NotFound),
            Self::Live(live) | Self::Immutable { live, .. } | Self::Checkpointed { live, .. } => {
                Ok(live)
            }
            Self::Deleted => Err(JournalError::Deleted),
        }
    }
}

impl Live {
    fn logical_floor(&self) -> Lsn {
        self.offload.floor.unwrap_or(self.floor)
    }

    /// Drops local records below `target`, which offload already holds.
    fn drop_local(&mut self, target: Lsn) {
        if target <= self.floor {
            return;
        }
        let logical = self.logical_floor();
        let count = (target.0 - self.floor.0) as usize;
        for payload in self.records.drain(..count) {
            self.bytes -= record_charge(payload.len());
        }
        if self.records.capacity() > self.records.len().saturating_mul(2).max(1024) {
            self.records.shrink_to_fit();
        }
        self.floor = target;
        self.epochs.trim(self.floor);
        self.offload.floor = Some(logical).filter(|logical| *logical < self.floor);
    }

    fn offloaded(&mut self, lineage: u64, through: Lsn, retain_from: Lsn) -> Outcome {
        if lineage != self.offload.lineage {
            return Outcome::Refused(JournalError::Conflict { head: self.head });
        }
        self.offload.through = Lsn(super::decisions::offloaded_through(
            self.offload.through.0,
            through.0,
            self.head.0,
        ));
        self.drop_local(Lsn(super::decisions::local_floor(
            self.floor.0,
            retain_from.0,
            self.offload.through.0,
            self.head.0,
        )));
        Outcome::At(self.offload.through)
    }

    fn restore(&mut self, restore: Restore) -> Outcome {
        if restore.lineage <= self.offload.lineage {
            return Outcome::Refused(JournalError::Conflict { head: self.head });
        }
        if restore.replace {
            let floor = restore.floor.max(Lsn(1)).min(Lsn(restore.head.0 + 1));
            self.records.clear();
            self.records.shrink_to_fit();
            self.bytes = 0;
            self.head = restore.head;
            self.floor = Lsn(restore.head.0 + 1);
            self.epochs = EpochRuns::default();
            self.offload.floor = Some(floor).filter(|floor| *floor < self.floor);
            self.offload.through = restore.head;
            // The store's run replaces the history: a writer of the epoch
            // it was taken at, or below, may have committed above its
            // head, so the restore counts as a recovery fenced just above.
            // A restore with no survivor knows only the epochs the store
            // holds: a writer sealed above all of them whose records never
            // reached the store keeps the lookup's earlier answer.
            self.recoveries = Some(Recoveries::absorb(
                self.recoveries,
                Epoch(restore.epoch.0.saturating_add(1)),
                restore.head,
            ));
            if restore.epoch > self.epoch() {
                self.writer = Some((
                    Fence {
                        epoch: restore.epoch,
                        writer: uuid::Uuid::nil(),
                    },
                    String::new(),
                ));
            }
        } else {
            self.offload.through = Lsn(super::decisions::offloaded_through(
                self.offload.through.0,
                restore.head.0,
                self.head.0,
            ));
        }
        self.offload.lineage = restore.lineage;
        self.offload
            .lineages
            .push((restore.lineage, Lsn(self.offload.through.0 + 1)));
        Outcome::At(self.head)
    }

    /// Whether nothing was ever sealed, written or restored here.
    fn fresh(&self) -> bool {
        self.writer.is_none() && self.head == Lsn(0) && self.offload.lineage == 0
    }

    fn epoch(&self) -> Epoch {
        self.writer
            .as_ref()
            .map_or(Epoch(0), |(fence, _)| fence.epoch)
    }

    fn recovering(&self) -> bool {
        self.writer
            .as_ref()
            .is_some_and(|(fence, _)| fence.writer == RECOVERY_WRITER)
    }

    /// Replaces the recovery fence with an ownerless fence at the same
    /// epoch, which the next ordinary seal of that epoch replaces. Returns
    /// the head, also when no recovery fence stands.
    fn acknowledge_recovery(&mut self) -> Result<Outcome> {
        if self.recovering() {
            let fence = Fence {
                epoch: self.epoch(),
                writer: uuid::Uuid::nil(),
            };
            self.writer = Some((fence, String::new()));
        }
        Ok(Outcome::At(self.head))
    }

    fn acknowledge_with_marker(
        &mut self,
        fence: RecoveryFence,
        at: Lsn,
        payload: Bytes,
        segment: Arc<super::storage::Object>,
        quota_bytes: u64,
    ) -> io::Result<Outcome> {
        let conflict = Outcome::Refused(JournalError::Conflict { head: self.head });
        if fence.head.0.checked_add(1) != Some(at.0) {
            return Ok(conflict);
        }
        if !self.recovering() {
            if at < self.floor {
                return Ok(Outcome::Refused(JournalError::Trimmed {
                    floor: self.floor,
                }));
            }
            // A transferred snapshot may have no epoch run for this record.
            // An exact retry can still return retained bytes without mutating
            // the stream, as with an ordinary append.
            if self.epoch() >= fence.epoch
                && self
                    .epochs
                    .epoch(at)
                    .is_none_or(|epoch| epoch == fence.epoch)
                && at <= self.head
                && let Some(record) = self.records.get((at.0 - self.floor.0) as usize)
                && record.kind() == RecordKind::Data
                && record.len() == payload.len()
                && record.load()? == payload
            {
                return Ok(Outcome::At(at));
            }
            return Ok(conflict);
        }
        if self.epoch() != fence.epoch || self.head != fence.head {
            return Ok(conflict);
        }
        let len = payload.len() as u32;
        let offset = segment.len().checked_sub(u64::from(len)).ok_or_else(|| {
            super::invalid("accepted WAL extent does not contain the recovery marker")
        })?;
        let record = Payload::Extent {
            object: segment,
            offset,
            len,
            crc: crc32fast::hash(&payload),
            kind: super::decisions::retained_kind(RecordOrigin::Marker).into(),
        };
        match self.append(at, record, quota_bytes) {
            Ok(_) => Ok(self.acknowledge_recovery().into()),
            Err(error) => Ok(Outcome::Refused(error)),
        }
    }

    /// Writes the typed entry of the recorded recovery at `at` and clears
    /// its fence. The entry must be exactly the one the record describes,
    /// with any consumer marker. An identical retry returns `at` while the
    /// entry is retained.
    fn write_recovery_entry(
        &mut self,
        fence: RecoveryFence,
        at: Lsn,
        entry: Bytes,
        segment: Arc<super::storage::Object>,
        quota_bytes: u64,
    ) -> io::Result<Outcome> {
        let decoded = RecoveryEntry::decode(&entry);
        let names_command = decoded
            .as_ref()
            .is_some_and(|decoded| decoded.fence == fence && decoded.at() == at);
        let pending = self.recorded.filter(|_| self.recovering());
        let matches_record = match (&decoded, pending) {
            (Some(decoded), Some(Recorded { record, exact })) => {
                decoded.configuration_epoch == record.epoch
                    && decoded.loss_point == record.loss_point
                    && decoded.exact == exact
                    && decoded.source == record.source
                    && decoded.time_unix_ms == record.time_unix_ms
            }
            _ => false,
        };
        // Only a retry after the fence cleared reads the retained bytes.
        let retained_identical = pending.is_none()
            && names_command
            && at >= self.floor
            && at <= self.head
            && match self.records.get((at.0 - self.floor.0) as usize) {
                Some(retained) => {
                    retained.kind() == RecordKind::Recovery
                        && retained.len() == entry.len()
                        && retained.load()? == entry
                }
                None => false,
            };
        let step = super::decisions::recovery_entry_step(
            names_command,
            fence.epoch.0,
            fence.head.0,
            at.0,
            pending.is_some(),
            self.epoch().0,
            self.head.0,
            self.floor.0,
            matches_record,
            retained_identical,
        );
        match step {
            EntryStep::Conflict => {
                return Ok(Outcome::Refused(JournalError::Conflict { head: self.head }));
            }
            EntryStep::Trimmed => {
                return Ok(Outcome::Refused(JournalError::Trimmed {
                    floor: self.floor,
                }));
            }
            EntryStep::Retry => return Ok(Outcome::At(at)),
            EntryStep::Write => (),
        }
        let len = entry.len() as u32;
        let offset = segment.len().checked_sub(u64::from(len)).ok_or_else(|| {
            super::invalid("accepted WAL extent does not contain the recovery entry")
        })?;
        let retained = Payload::Extent {
            object: segment,
            offset,
            len,
            crc: crc32fast::hash(&entry),
            kind: super::decisions::retained_kind(RecordOrigin::RecoveryEntry).into(),
        };
        // The entry must be written for the stream to make progress, so it
        // may use the recovery headroom past the quota and record limit.
        match self.retain(at, retained, quota_bytes, true) {
            Ok(_) => {
                self.recorded = None;
                let _ = self.acknowledge_recovery();
                Ok(Outcome::At(at))
            }
            Err(error) => Ok(Outcome::Refused(error)),
        }
    }

    fn seal(&mut self, expected: Epoch, writer: uuid::Uuid, owner: String) -> Result<Outcome> {
        let fence = match super::decisions::seal_step(self.recovering(), self.epoch().0, expected.0)
        {
            super::decisions::SealStep::Recovered => {
                return Err(JournalError::Recovered { head: self.head });
            }
            super::decisions::SealStep::Unavailable => return Err(JournalError::Unavailable),
            super::decisions::SealStep::Install(epoch) => {
                let fence = Fence {
                    epoch: Epoch(epoch),
                    writer,
                };
                self.writer = Some((fence, owner));
                fence
            }
            super::decisions::SealStep::Repeat(epoch) => {
                let fence = Fence {
                    epoch: Epoch(epoch),
                    writer,
                };
                self.require_writer(fence, &owner)?;
                fence
            }
        };
        Ok(Outcome::Sealed(Sealed {
            fence,
            head: self.head,
        }))
    }

    fn require_writer(&self, fence: Fence, owner: &str) -> Result<()> {
        if self
            .writer
            .as_ref()
            .is_some_and(|(current, principal)| *current == fence && principal == owner)
        {
            Ok(())
        } else {
            Err(JournalError::Fenced {
                current: self.epoch(),
            })
        }
    }

    fn append(&mut self, at: Lsn, payload: Payload, quota_bytes: u64) -> Result<Outcome> {
        self.retain(at, payload, quota_bytes, false)
    }

    /// Appends `payload` at `at` if the stream still retains it
    /// (`decisions::retains_record`): within `quota_bytes` and
    /// `MAX_RETAINED_RECORDS`, and for a typed recovery entry (`entry`)
    /// also within the recovery headroom.
    fn retain(
        &mut self,
        at: Lsn,
        payload: Payload,
        quota_bytes: u64,
        entry: bool,
    ) -> Result<Outcome> {
        let conflict = JournalError::Conflict { head: self.head };
        if at < self.floor {
            return Err(JournalError::Trimmed { floor: self.floor });
        }
        if self.head.0.checked_add(1) != Some(at.0) || at.0 == u64::MAX {
            return Err(conflict);
        }
        if payload.len() > MAX_RECORD {
            return Err(JournalError::TooLarge { max: MAX_RECORD });
        }
        let charge = record_charge(payload.len());
        if !super::decisions::retains_record(
            entry,
            self.records.len(),
            MAX_RETAINED_RECORDS,
            self.bytes,
            charge,
            quota_bytes,
        ) {
            return Err(JournalError::Full { floor: self.floor });
        }
        self.record_append(at, payload, self.bytes + charge);
        Ok(Outcome::At(at))
    }

    fn record_append(&mut self, at: Lsn, payload: Payload, used: u64) {
        self.records.push_back(payload);
        self.epochs.note(at, self.epoch());
        self.bytes = used;
        self.head = at;
    }

    /// Appends a contiguous group atomically. Records already retained must
    /// match exactly, and every new record must fit before any is applied.
    fn append_batch(
        &mut self,
        at: Lsn,
        payloads: Vec<Bytes>,
        extents: &[u64],
        segment: &Arc<super::storage::Object>,
        genesis: &Genesis,
    ) -> io::Result<Result<Outcome>> {
        let conflict = JournalError::Conflict { head: self.head };
        let Some(last) =
            at.0.checked_add(payloads.len() as u64 - 1)
                .filter(|last| *last != u64::MAX)
        else {
            return Ok(Err(conflict));
        };
        if at < self.floor {
            return Ok(Err(JournalError::Trimmed { floor: self.floor }));
        }
        if genesis.immutable && at <= self.head && last > self.head.0 {
            return Ok(Err(conflict));
        }
        let retained = self.head.0.min(last).saturating_sub(at.0.saturating_sub(1)) as usize;
        let retained = if at > self.head { 0 } else { retained };
        for (index, payload) in payloads.iter().take(retained).enumerate() {
            let record = &self.records[(at.0 - self.floor.0) as usize + index];
            let lsn = Lsn(at.0 + index as u64);
            if record.kind() != RecordKind::Data
                || match self.epochs.epoch(lsn) {
                    Some(epoch) => epoch != self.epoch(),
                    None => genesis.immutable,
                }
                || record.len() != payload.len()
                || record.load()? != *payload
            {
                return Ok(Err(conflict));
            }
        }
        let fresh = &payloads[retained..];
        if fresh.is_empty() {
            return Ok(Ok(Outcome::At(Lsn(last))));
        }
        if self.head.0.checked_add(1) != Some(at.0 + retained as u64) {
            return Ok(Err(conflict));
        }
        if self.records.len().saturating_add(fresh.len()) > MAX_RETAINED_RECORDS {
            return Ok(Err(JournalError::Full { floor: self.floor }));
        }
        let Some(used) = fresh
            .iter()
            .try_fold(self.bytes, |used, payload| {
                used.checked_add(record_charge(payload.len()))
            })
            .filter(|used| *used <= genesis.quota_bytes)
        else {
            return Ok(Err(JournalError::Full { floor: self.floor }));
        };
        for (payload, offset) in fresh.iter().zip(&extents[retained..]) {
            self.records.push_back(Payload::Extent {
                object: segment.clone(),
                offset: *offset,
                len: payload.len() as u32,
                crc: crc32fast::hash(payload),
                kind: super::decisions::retained_kind(RecordOrigin::Append).into(),
            });
        }
        self.epochs.note(Lsn(at.0 + retained as u64), self.epoch());
        self.bytes = used;
        self.head = Lsn(last);
        Ok(Ok(Outcome::At(Lsn(last))))
    }

    fn trim(&mut self, through: Lsn) -> Result<Outcome> {
        if through > self.head {
            return Err(JournalError::Conflict { head: self.head });
        }
        if through >= self.floor {
            let count = (through.0 - self.floor.0 + 1) as usize;
            for payload in self.records.drain(..count) {
                self.bytes -= record_charge(payload.len());
            }
            if self.records.capacity() > self.records.len().saturating_mul(2).max(1024) {
                self.records.shrink_to_fit();
            }
            self.floor = Lsn(through.0 + 1);
            self.epochs.trim(self.floor);
            self.offload.floor = None;
        } else if through >= self.logical_floor() {
            // Only offloaded records lie below the local floor.
            self.offload.floor = Some(Lsn(through.0 + 1)).filter(|floor| *floor < self.floor);
        }
        Ok(Outcome::Unit)
    }

    fn remote(&self, from: Lsn) -> Option<Remote> {
        let floor = self.logical_floor();
        if from < floor || from >= self.floor || from > self.head {
            return None;
        }
        let (lineage, end) = self.offload.lineage_of(from);
        Some(Remote {
            lineage,
            from,
            until: Lsn((self.floor.0 - 1).min(end.0).min(self.head.0)),
            floor,
            head: self.head,
        })
    }

    fn read(&self, from: Lsn, limit: usize) -> Result<ReadPage> {
        let logical = self.logical_floor();
        if from < logical {
            return Err(JournalError::Trimmed { floor: logical });
        }
        if from < self.floor {
            // Offloaded and dropped here: the caller reads the store.
            return Err(JournalError::Unavailable);
        }
        let mut records = Vec::new();
        if from <= self.head {
            let mut bytes = 0;
            for payload in self
                .records
                .iter()
                .skip((from.0 - self.floor.0) as usize)
                .take(limit.min(MAX_RECORDS_PER_PAGE))
            {
                bytes += payload.len();
                if bytes > MAX_PAGE {
                    break;
                }
                records.push((Lsn(from.0 + records.len() as u64), payload.clone()));
            }
        }
        Ok(ReadPage {
            floor: logical,
            records,
            head: self.head,
        })
    }
}
