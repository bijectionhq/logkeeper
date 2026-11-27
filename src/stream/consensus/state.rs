//! Deterministic decisions over the committed journal view.

pub(super) const MAX_RETAINED_RECORDS: usize = 262_144;

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
use journal_contract::{Epoch, JournalError, Lsn, Page, RecoveryFence, Result};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use super::{Fence, Genesis, MAX_PAGE, MAX_RECORD, MAX_RECORDS_PER_PAGE, Sealed, Stage};
use crate::stream::keeper::record_charge;
use crate::stream::timed::{EVIDENCE_BYTES, TimedEvidence};

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
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Outcome {
    Unit,
    Sealed(Sealed),
    At(Lsn),
    Page(Page),
    Refused(JournalError),
    Configuration(super::Configuration),
    /// One keeper's signed sync sample for a staged original.
    OriginalSample(Vec<u8>),
    /// The retained evidence of a timed original record.
    OriginalEvidence(Vec<u8>),
    RecoveryFence(Option<RecoveryFence>),
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
        timed: bool,
    },
    Snapshot {
        file: Arc<Mutex<File>>,
        digest: [u8; 32],
        offset: u64,
        len: u32,
        crc: u32,
        timed: bool,
    },
}

/// Marks a timed record in snapshot and wire record lengths. Records are at
/// most 4 MiB, so the bit is free, and an older reader refuses it as an
/// oversized record instead of reading evidence as payload.
pub(super) const TIMED_RECORD: u32 = 1 << 31;

impl Payload {
    pub(super) fn timed(&self) -> bool {
        match self {
            Self::Extent { timed, .. } | Self::Snapshot { timed, .. } => *timed,
        }
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
        let records = self
            .records
            .into_iter()
            .map(|(lsn, payload)| Ok((lsn, payload.contents()?)))
            .collect::<io::Result<_>>()?;
        Ok(Page {
            floor: self.floor,
            records,
            head: self.head,
        })
    }
}

impl State {
    pub fn apply(
        &mut self,
        command: Command,
        genesis: &Genesis,
        segment: Arc<super::storage::Object>,
    ) -> io::Result<Outcome> {
        if let Command::AcknowledgeRecoveryWithMarker { fence, at, payload } = command {
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
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
                    if !retained.timed()
                        && live
                            .epochs
                            .epoch(at)
                            .is_none_or(|epoch| epoch == fence.epoch)
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
                timed: false,
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
                timed: true,
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
                .append_batch(at, payloads, &extents, &segment, genesis.quota_bytes)?
                .into());
        }
        Ok(self.decide(command).into())
    }

    fn decide(&mut self, command: Command) -> Result<Outcome> {
        if matches!(command, Command::Create) {
            return match self {
                Self::Absent => {
                    *self = Self::Live(Live {
                        writer: None,
                        head: Lsn(0),
                        floor: Lsn(1),
                        bytes: 0,
                        records: VecDeque::new(),
                        epochs: EpochRuns::default(),
                    });
                    Ok(Outcome::Unit)
                }
                Self::Live(_) => Ok(Outcome::Unit),
                Self::Deleted => Err(JournalError::Deleted),
            };
        }
        if matches!(command, Command::Delete) && matches!(self, Self::Deleted) {
            return Ok(Outcome::Unit);
        }
        let live = self.live_mut()?;
        match command {
            Command::Seal {
                expected,
                writer,
                owner,
            } => live.seal(expected, writer, owner),
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
            Command::AcknowledgeRecovery => live.acknowledge_recovery(),
            Command::Create
            | Command::Append { .. }
            | Command::Stage(_)
            | Command::StageOwned(_)
            | Command::Recover(_)
            | Command::Admitted(..)
            | Command::AppendBatch { .. }
            | Command::AppendOriginal { .. }
            | Command::AcknowledgeRecoveryWithMarker { .. } => unreachable!(),
        }
    }

    pub fn head(&self) -> Result<Lsn> {
        Ok(self.live()?.head)
    }

    /// Installs the recovery fence above the current epoch.
    pub fn recover(&mut self) -> Result<Outcome> {
        let live = self.live_mut()?;
        let epoch = super::decisions::recovery_epoch(live.epoch().0)
            .map(Epoch)
            .ok_or(JournalError::Unavailable)?;
        let fence = Fence {
            epoch,
            writer: RECOVERY_WRITER,
        };
        live.writer = Some((fence, String::new()));
        Ok(Outcome::Sealed(Sealed {
            fence,
            head: live.head,
        }))
    }

    /// Whether an unacknowledged operator recovery fences the stream.
    pub fn recovering(&self) -> bool {
        self.live().is_ok_and(Live::recovering)
    }

    pub fn recovery_fence(&self) -> Result<Option<RecoveryFence>> {
        let live = self.live()?;
        Ok(live.recovering().then(|| RecoveryFence { epoch: live.epoch(), head: live.head }))
    }

    pub fn read(&self, from: Lsn, limit: usize) -> Result<ReadPage> {
        self.live()?.read(from, limit)
    }

    /// The sealed writer fence and principal, when a writer holds the stream.
    pub fn writer(&self) -> Option<(Fence, &str)> {
        let (fence, owner) = self.live().ok()?.writer.as_ref()?;
        Some((*fence, owner))
    }

    /// The retained timed record at `at`. A position below the floor is
    /// trimmed, and an ordinary or missing record has no original evidence.
    pub fn timed_record(&self, at: Lsn) -> Result<Payload> {
        let live = self.live()?;
        if at < live.floor {
            return Err(JournalError::Trimmed { floor: live.floor });
        }
        if at > live.head {
            return Err(JournalError::Conflict { head: live.head });
        }
        let record = &live.records[(at.0 - live.floor.0) as usize];
        if !record.timed() {
            return Err(JournalError::Unavailable);
        }
        Ok(record.clone())
    }

    /// The bytes a new timed record of `payload_len` would charge, if the
    /// stream can still hold it.
    pub fn fits_timed(&self, payload_len: usize, quota_bytes: u64) -> bool {
        self.live().is_ok_and(|live| {
            live.records.len() < MAX_RETAINED_RECORDS
                && live
                    .bytes
                    .checked_add(record_charge(EVIDENCE_BYTES + payload_len))
                    .is_some_and(|used| used <= quota_bytes)
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

    /// Retained record count and byte charge for a live stream, or `(0, 0)`.
    pub fn retained_stats(&self) -> (u64, u64) {
        self.live()
            .ok()
            .map_or((0, 0), |live| (live.records.len() as u64, live.bytes))
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
        if let Self::Live(live) = self {
            let bytes = records
                .iter()
                .map(|record| record_charge(record.len()))
                .sum::<u64>();
            if live.bytes != bytes || bytes > quota {
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
                Some(written) if written != epoch || record.timed() => return Err(conflict),
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
        if let Self::Live(live) = self {
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
            Self::Live(live) => Ok(live),
            Self::Deleted => Err(JournalError::Deleted),
        }
    }

    fn live_mut(&mut self) -> Result<&mut Live> {
        match self {
            Self::Absent => Err(JournalError::NotFound),
            Self::Live(live) => Ok(live),
            Self::Deleted => Err(JournalError::Deleted),
        }
    }
}

impl Live {
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
                return Ok(Outcome::Refused(JournalError::Trimmed { floor: self.floor }));
            }
            // A transferred snapshot may have no epoch run for this record.
            // An exact retry can still return retained bytes without mutating
            // the stream, as with an ordinary append.
            if self.epoch() >= fence.epoch
                && self.epochs.epoch(at).is_none_or(|epoch| epoch == fence.epoch)
                && at <= self.head
                && let Some(record) = self.records.get((at.0 - self.floor.0) as usize)
                && !record.timed()
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
            timed: false,
        };
        match self.append(at, record, quota_bytes) {
            Ok(_) => Ok(self.acknowledge_recovery().into()),
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
        if self.records.len() >= MAX_RETAINED_RECORDS {
            return Err(JournalError::Full { floor: self.floor });
        }
        let charge = record_charge(payload.len());
        let used = self
            .bytes
            .checked_add(charge)
            .filter(|used| *used <= quota_bytes)
            .ok_or(JournalError::Full { floor: self.floor })?;
        self.records.push_back(payload);
        self.epochs.note(at, self.epoch());
        self.bytes = used;
        self.head = at;
        Ok(Outcome::At(at))
    }

    /// Appends a contiguous group atomically. Records already retained must
    /// match exactly, and every new record must fit before any is applied.
    fn append_batch(
        &mut self,
        at: Lsn,
        payloads: Vec<Bytes>,
        extents: &[u64],
        segment: &Arc<super::storage::Object>,
        quota_bytes: u64,
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
        let retained = self.head.0.min(last).saturating_sub(at.0.saturating_sub(1)) as usize;
        let retained = if at > self.head { 0 } else { retained };
        for (index, payload) in payloads.iter().take(retained).enumerate() {
            let record = &self.records[(at.0 - self.floor.0) as usize + index];
            let lsn = Lsn(at.0 + index as u64);
            if record.timed()
                || self
                    .epochs
                    .epoch(lsn)
                    .is_some_and(|epoch| epoch != self.epoch())
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
            .filter(|used| *used <= quota_bytes)
        else {
            return Ok(Err(JournalError::Full { floor: self.floor }));
        };
        for (payload, offset) in fresh.iter().zip(&extents[retained..]) {
            self.records.push_back(Payload::Extent {
                object: segment.clone(),
                offset: *offset,
                len: payload.len() as u32,
                crc: crc32fast::hash(payload),
                timed: false,
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
        }
        Ok(Outcome::Unit)
    }

    fn read(&self, from: Lsn, limit: usize) -> Result<ReadPage> {
        if from < self.floor {
            return Err(JournalError::Trimmed { floor: self.floor });
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
            floor: self.floor,
            records,
            head: self.head,
        })
    }
}
