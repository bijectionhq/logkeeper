//! The segmented WAL.
//!
//! A round appends one frame per record to the active segment, syncs its data
//! once, then publishes (segment, offset, chain hash) in the next boundary
//! slot on the registry volume. Entries stay where their frame put them:
//! extents and snapshot spans hold slices of the segment.
//!
//! The per-stream index lives in memory. A checkpoint captures it with its
//! position off the hot path; recovery restores the checkpoint the boundary
//! names and replays the frames after it, which must end exactly at the
//! boundary with the same chain hash.
//!
//! Live extents are not copied forward: a segment before the published
//! checkpoint is deleted once its last slice is dropped, so one retained
//! record keeps its whole segment.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File, OpenOptions},
    io::{self, BufReader, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::Arc,
    thread::JoinHandle,
    time::{Duration, Instant},
};

use bincode::Options as _;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{
    CatalogEntry, Entry, Genesis, Log, LogId, Media, Record, Selected, State, StreamId, Vote,
    invalid, legacy, sync_directory, sync_file,
};
use crate::stream::{
    consensus::{
        decisions, options,
        storage::{
            media::{Boundaries, Boundary, CheckpointRef, Slot},
            objects::{Location, Object, Objects, Pins, Reference, Segment},
            segment::{self, FIRST, FRAME_HEADER, Frame, HEADER, MAX_FRAME, SalvageFrame},
            space::Space,
        },
    },
    keeper::durability::sync_data,
};

pub(super) const MAX_SCOPES: usize = 4096;
pub(super) const MAX_SUFFIX: usize = 1024;
pub(in crate::stream::consensus::storage) const CHECKPOINTS: &str = "raft-checkpoints";
/// N-1 checkpoint format; written until the cluster feature level is finalized
/// at `CLUSTER_VERSION_V2` so downgrade before finalize stays possible.
const CHECKPOINT_MAGIC: &[u8; 8] = b"LKRWAL04";
/// N checkpoint format carrying the finalized cluster feature level; gated by
/// `decisions::write_version_allows`.
const CHECKPOINT_MAGIC_V5: &[u8; 8] = b"LKRWAL05";
/// The format that also carries each stream's durable commit index
/// (`Record::Committed`); written once the cluster finalized
/// `CLUSTER_VERSION_LEASES`, the level that writes those frames.
const CHECKPOINT_MAGIC_V6: &[u8; 8] = b"LKRWAL06";
const MAX_CHECKPOINT: u64 = 1024 * 1024 * 1024;
#[cfg(not(test))]
const SEGMENT_BYTES: u64 = 64 * 1024 * 1024;
#[cfg(test)]
const SEGMENT_BYTES: u64 = 256 * 1024;
#[cfg(not(test))]
const CHECKPOINT_BYTES: u64 = 64 * 1024 * 1024;
#[cfg(test)]
const CHECKPOINT_BYTES: u64 = 256 * 1024;
const CHECKPOINT_INTERVAL: Duration = Duration::from_secs(30);

#[derive(Clone, Copy)]
pub(super) struct Tuning {
    pub segment_bytes: u64,
    pub checkpoint_bytes: u64,
    /// Publishes each checkpoint before the round that started it returns.
    #[cfg(test)]
    pub synchronous: bool,
}

impl Default for Tuning {
    fn default() -> Self {
        Self {
            segment_bytes: SEGMENT_BYTES,
            checkpoint_bytes: CHECKPOINT_BYTES,
            #[cfg(test)]
            synchronous: false,
        }
    }
}

/// Summary returned by offline `logkeeper keeper salvage`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SalvageReport {
    pub damaged_segments: BTreeSet<u64>,
    pub quarantined: BTreeSet<StreamId>,
    pub preserved: BTreeSet<StreamId>,
    /// False when no damage was found and the keeper media was left untouched.
    pub salvaged: bool,
}

impl std::fmt::Display for SalvageReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.salvaged {
            return write!(
                f,
                "WAL is healthy: {} stream(s) intact, no salvage needed.",
                self.preserved.len()
            );
        }
        write!(
            f,
            "salvaged WAL past {} damaged segment(s) {:?}: quarantined {} stream(s), preserved {} stream(s).",
            self.damaged_segments.len(),
            self.damaged_segments,
            self.quarantined.len(),
            self.preserved.len()
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub(in crate::stream::consensus::storage) struct Position {
    pub segment: u64,
    pub offset: u64,
}

#[derive(Serialize, Deserialize)]
pub(in crate::stream::consensus::storage) struct Checkpoint {
    pub position: Position,
    pub chain: [u8; 32],
    pub leaves: Vec<(StreamId, Leaf)>,
    pub segments: BTreeMap<u64, BTreeSet<StreamId>>,
    /// Each stream's durable commit index. Outside the earlier layouts:
    /// only `CheckpointV6` carries it.
    #[serde(skip)]
    pub committed: BTreeMap<StreamId, LogId>,
}

#[derive(Serialize, Deserialize)]
struct CheckpointV5 {
    cluster_version: u32,
    checkpoint: Checkpoint,
}

#[derive(Serialize, Deserialize)]
struct CheckpointV6 {
    cluster_version: u32,
    checkpoint: Checkpoint,
    committed: BTreeMap<StreamId, LogId>,
}

impl State {
    /// Restores the commit indexes a checkpoint carries, after its leaves.
    fn restore_committed(&mut self, committed: BTreeMap<StreamId, LogId>) {
        for (stream, id) in committed {
            if let Some(log) = self.logs.get_mut(&stream) {
                log.committed = Some(id);
            }
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub(in crate::stream::consensus::storage) struct Leaf {
    pub genesis: Option<Genesis>,
    pub catalog: Option<CatalogEntry>,
    pub vote: Option<Vote>,
    pub purged: Option<LogId>,
    pub snapshot: Option<Selected>,
    pub ownership: Option<crate::stream::consensus::ownership::Ownership>,
    pub entries: BTreeMap<u64, Reference>,
}

/// Buffers a round's frames for the active segment.
struct Writer {
    incarnation: Uuid,
    directory: PathBuf,
    id: u64,
    file: File,
    len: u64,
    chain: [u8; 32],
    buffer: Vec<u8>,
    limit: u64,
}

pub(super) struct Staged {
    start: usize,
    pub slices: Option<(StreamId, Vec<(u64, Arc<Object>)>)>,
    pub moved: Option<(Location, Location)>,
}

pub(super) struct Segmented {
    keeper: Uuid,
    writer: Writer,
    checkpoints: PathBuf,
    boundaries: Boundaries,
    published: Published,
    pending: Option<Pending>,
    since: u64,
    last: Instant,
    scopes: BTreeSet<StreamId>,
    tuning: Tuning,
    /// Segments that relocated slices left. The published checkpoint may
    /// still name their old copies, so they stay until a checkpoint
    /// captured after the move is published.
    retired: Vec<Arc<Segment>>,
    #[cfg(test)]
    cut: std::cell::Cell<u8>,
}

/// The checkpoint the boundary names. Its pins keep every object it refers
/// to until a newer checkpoint replaces it.
struct Published {
    reference: Option<CheckpointRef>,
    _pins: Pins,
}

struct Pending {
    handle: JoinHandle<io::Result<CheckpointRef>>,
    position: Position,
    pins: Pins,
    /// Segments retired before this checkpoint was captured, released once
    /// it is published.
    retired: Vec<Arc<Segment>>,
}

impl Writer {
    fn stage(&mut self, record: &Record, objects: &Objects) -> io::Result<Staged> {
        if self.buffer.is_empty() && self.len >= self.limit {
            self.roll()?;
        }
        let start = self.buffer.len();
        self.buffer.extend_from_slice(&[0; FRAME_HEADER as usize]);
        let body = start + FRAME_HEADER as usize;
        let staged = options()
            .with_limit(MAX_FRAME)
            .serialize_into(&mut self.buffer, record)
            .map_err(io::Error::other)
            .and_then(|()| segment::seal(&mut self.buffer, start))
            .and_then(|()| {
                let frame = &self.buffer[body..];
                let base = self.len + body as u64;
                Ok((
                    slices(record, frame, self.id, base, objects)?,
                    moved(record, frame, self.id, base)?,
                ))
            });
        match staged {
            Ok((slices, moved)) => Ok(Staged {
                start,
                slices,
                moved,
            }),
            Err(error) => {
                self.buffer.truncate(start);
                Err(error)
            }
        }
    }

    fn roll(&mut self) -> io::Result<()> {
        let id = self.id + 1;
        self.file = segment::create(&self.directory, id, self.incarnation)?;
        self.id = id;
        self.len = HEADER;
        Ok(())
    }

    fn end(&self) -> Position {
        Position {
            segment: self.id,
            offset: self.len + self.buffer.len() as u64,
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.file.write_all(&self.buffer)?;
        sync_data(&self.file)?;
        self.advance(segment::chain_frames(self.chain, &self.buffer));
        Ok(())
    }

    fn advance(&mut self, chain: [u8; 32]) {
        self.chain = chain;
        self.len += self.buffer.len() as u64;
        self.buffer.clear();
    }
}

/// The entries of an append are the last bytes of its frame body, each in
/// the encoding `encode(entry)` gives it.
fn slices(
    record: &Record,
    body: &[u8],
    segment: u64,
    base: u64,
    objects: &Objects,
) -> io::Result<Option<(StreamId, Vec<(u64, Arc<Object>)>)>> {
    let Some(entries) = record.entries() else {
        return Ok(None);
    };
    let scope = record.stream();
    let mut end = body.len();
    let mut slices = Vec::with_capacity(entries.len());
    for entry in entries.iter().rev() {
        let len = options().serialized_size(entry).map_err(io::Error::other)? as usize;
        let start = end
            .checked_sub(len)
            .ok_or_else(|| invalid("WAL frame does not end with its entries"))?;
        let location = Location {
            scope,
            segment,
            offset: base + start as u64,
            len: len as u64,
            crc: crc32fast::hash(&body[start..end]),
        };
        slices.push((entry.log_id.index, objects.slice(location)?));
        end = start;
    }
    if end < 8 || body[end - 8..end] != (entries.len() as u64).to_le_bytes() {
        return Err(invalid("WAL frame does not end with its entries"));
    }
    slices.reverse();
    Ok(Some((scope, slices)))
}

/// Where a relocated slice's copy lies: the last bytes of its frame body.
fn moved(
    record: &Record,
    body: &[u8],
    segment: u64,
    base: u64,
) -> io::Result<Option<(Location, Location)>> {
    let Record::Relocate(from, bytes) = record else {
        return Ok(None);
    };
    let start = body
        .len()
        .checked_sub(bytes.len())
        .filter(|start| body[*start..] == bytes[..])
        .ok_or_else(|| invalid("WAL frame does not end with its relocated slice"))?;
    if bytes.len() as u64 != from.len || crc32fast::hash(bytes) != from.crc {
        return Err(invalid("relocated slice differs from its source"));
    }
    Ok(Some((
        *from,
        Location {
            segment,
            offset: base + start as u64,
            ..*from
        },
    )))
}

impl Segmented {
    pub fn open(media: &Media, objects: &Objects, tuning: Tuning) -> io::Result<(Self, State)> {
        let (boundaries, slot) = media.boundaries()?;
        let incarnation = media.incarnation();
        let checkpoints = media.data().join(CHECKPOINTS);
        if !checkpoints.exists() {
            fs::create_dir(&checkpoints)?;
            sync_directory(media.data())?;
        }
        let directory = objects.segment_directory().to_owned();
        let (mut state, position, chain, pins) = match slot.checkpoint {
            Some(reference) => {
                let (mut checkpoint, cluster_version) = read_checkpoint(&checkpoints, reference)?;
                let mut state = State {
                    cluster_version,
                    ..State::default()
                };
                let committed = std::mem::take(&mut checkpoint.committed);
                for (scope, leaf) in checkpoint.leaves {
                    leaf.restore(scope, objects, &mut state)?;
                }
                state.restore_committed(committed);
                objects.restore_segment_scopes(checkpoint.segments);
                let pins = state
                    .logs
                    .values()
                    .flat_map(|log| log.segments.values().cloned())
                    .collect();
                (state, checkpoint.position, checkpoint.chain, pins)
            }
            None => (
                State::default(),
                Position {
                    segment: FIRST,
                    offset: HEADER,
                },
                segment::seed(incarnation),
                Vec::new(),
            ),
        };
        let boundary = Position {
            segment: slot.segment,
            offset: slot.offset,
        };
        if !decisions::checkpoint_within(
            position.segment,
            position.offset,
            boundary.segment,
            boundary.offset,
            HEADER,
        ) {
            return Err(invalid("WAL checkpoint lies past its trusted boundary"));
        }
        let replayed = replay(
            &directory,
            incarnation,
            &mut state,
            objects,
            position,
            chain,
            &slot,
        )?;
        state.check_hard_state()?;

        // Frames past the boundary, and segments a later unpublished round
        // created, were never acknowledged.
        let active = directory.join(segment::name(slot.segment));
        let file = OpenOptions::new().read(true).append(true).open(&active)?;
        if file.metadata()?.len() > slot.offset {
            file.set_len(slot.offset)?;
            sync_data(&file)?;
        }
        let mut removed = false;
        for item in fs::read_dir(&directory)? {
            let item = item?;
            if item
                .file_name()
                .to_str()
                .and_then(segment::parse)
                .is_some_and(|id| id > slot.segment)
            {
                fs::remove_file(item.path())?;
                removed = true;
            }
        }
        if removed {
            sync_directory(&directory)?;
        }
        let current = slot
            .checkpoint
            .map(|reference| checkpoint_name(reference.id));
        for item in fs::read_dir(&checkpoints)? {
            let item = item?;
            if current.as_deref() != item.file_name().to_str() {
                fs::remove_file(item.path())?;
            }
        }
        objects.set_floor(position.segment);
        let scopes = state.scope_ids();
        Ok((
            Self {
                keeper: media.keeper(),
                writer: Writer {
                    incarnation,
                    directory,
                    id: slot.segment,
                    file,
                    len: slot.offset,
                    chain: slot.chain,
                    buffer: Vec::new(),
                    limit: tuning.segment_bytes,
                },
                checkpoints,
                boundaries,
                published: Published {
                    reference: slot.checkpoint,
                    _pins: pins.into(),
                },
                pending: None,
                since: replayed,
                last: Instant::now(),
                scopes,
                tuning,
                retired: Vec::new(),
                #[cfg(test)]
                cut: Default::default(),
            },
            state,
        ))
    }

    /// Offline salvage: walks past damaged WAL spans, durably quarantines
    /// every stream with slices in a damaged segment or failing verification,
    /// writes a fresh checkpoint and boundary for the intact streams, and
    /// leaves strict startup (`Segmented::open`) unchanged.
    pub fn salvage(
        media: &Media,
        objects: &Objects,
        space: &Space,
        quarantine: &crate::stream::consensus::storage::media::QuarantineStore,
    ) -> io::Result<SalvageReport> {
        let (mut boundaries, slot) = media.boundaries()?;
        let incarnation = media.incarnation();
        let checkpoints = media.data().join(CHECKPOINTS);
        if !checkpoints.exists() {
            fs::create_dir(&checkpoints)?;
            sync_directory(media.data())?;
        }
        let directory = objects.segment_directory().to_owned();
        let mut damaged_segments = BTreeSet::new();
        let mut quarantined = BTreeSet::new();
        let mut segment_scopes: BTreeMap<u64, BTreeSet<StreamId>> = BTreeMap::new();

        let (mut state, from, mut chain) = match slot.checkpoint {
            Some(reference) => {
                let (mut checkpoint, cluster_version) = read_checkpoint(&checkpoints, reference)?;
                let committed = std::mem::take(&mut checkpoint.committed);
                segment_scopes = checkpoint.segments.clone();
                objects.restore_segment_scopes(checkpoint.segments.clone());
                // Check every segment header the checkpoint knows about.
                for (&seg_id, scopes) in &segment_scopes {
                    let ok = File::open(directory.join(segment::name(seg_id)))
                        .and_then(|mut file| segment::check_header(&mut file, seg_id, incarnation))
                        .is_ok();
                    if !ok {
                        damaged_segments.insert(seg_id);
                        quarantined.extend(scopes.iter().copied());
                    }
                }
                let mut state = State {
                    cluster_version,
                    ..State::default()
                };
                for (scope, leaf) in checkpoint.leaves {
                    let (leaf_bad, bad_segs) =
                        leaf.restore_salvage(scope, objects, &damaged_segments, &mut state)?;
                    if leaf_bad {
                        quarantined.insert(scope);
                        for seg in bad_segs {
                            damaged_segments.insert(seg);
                            if let Some(scopes) = segment_scopes.get(&seg) {
                                quarantined.extend(scopes.iter().copied());
                            }
                        }
                    }
                }
                state.restore_committed(committed);
                (state, checkpoint.position, checkpoint.chain)
            }
            None => (
                State::default(),
                Position {
                    segment: FIRST,
                    offset: HEADER,
                },
                segment::seed(incarnation),
            ),
        };

        // Replay segments from the checkpoint to the published boundary.
        // A frame that decodes names its stream. A frame that fails its
        // checksum, does not decode, or is missing could hold any stream's
        // vote, trim, deletion or registration, so its loss is attributed to
        // no stream in particular, and every stream is quarantined below:
        // guessing would let a lost record's stream serve without it.
        let mut unattributed = false;
        for id in from.segment..=slot.segment {
            let mut file = match File::open(directory.join(segment::name(id))) {
                Ok(file) => BufReader::with_capacity(1024 * 1024, file),
                Err(_) => {
                    damaged_segments.insert(id);
                    unattributed = true;
                    continue;
                }
            };
            if segment::check_header(&mut file, id, incarnation).is_err() {
                damaged_segments.insert(id);
                unattributed = true;
                continue;
            }
            let mut offset = HEADER;
            if id == from.segment && from.offset != HEADER {
                if file.seek(SeekFrom::Start(from.offset)).is_err() {
                    damaged_segments.insert(id);
                    unattributed = true;
                    continue;
                }
                offset = from.offset;
            }
            let end = (id == slot.segment).then_some(slot.offset);
            while Some(offset) != end {
                let remaining = end.map(|e| e.saturating_sub(offset));
                match segment::next_salvage(&mut file, remaining)? {
                    SalvageFrame::Complete { header, body } => {
                        let next = offset + FRAME_HEADER + body.len() as u64;
                        if !unattributed {
                            chain = segment::chain(&chain, &header, &body);
                        }
                        let decoded: io::Result<Record> = options()
                            .with_limit(MAX_FRAME)
                            .deserialize(&body)
                            .map_err(io::Error::other);
                        match decoded {
                            // Every record that decodes is applied, also for a
                            // stream already quarantined, so its votes stay
                            // current in the salvaged checkpoint.
                            Ok(record) => {
                                let scope = record.stream();
                                let applied =
                                    slices(&record, &body, id, offset + FRAME_HEADER, objects)
                                        .and_then(|built| {
                                            state.apply(record)?;
                                            if let Some((stream, slices)) = built {
                                                state.log_mut(stream)?.segments.extend(slices);
                                            }
                                            Ok(())
                                        });
                                if applied.is_err() {
                                    quarantined.insert(scope);
                                    damaged_segments.insert(id);
                                }
                            }
                            Err(_) => {
                                damaged_segments.insert(id);
                                unattributed = true;
                            }
                        }
                        offset = next;
                    }
                    SalvageFrame::BadCrc { len } => {
                        damaged_segments.insert(id);
                        unattributed = true;
                        offset += FRAME_HEADER + u64::from(len);
                    }
                    SalvageFrame::End if end.is_none() => break,
                    SalvageFrame::End | SalvageFrame::Torn => {
                        damaged_segments.insert(id);
                        unattributed = true;
                        break;
                    }
                }
            }
        }
        // Intact frames that do not chain to the published boundary mean a
        // frame is missing or was replaced.
        if !unattributed && chain != slot.chain {
            damaged_segments.extend(from.segment..=slot.segment);
            unattributed = true;
        }
        if unattributed {
            // A keeper that held the single catalog may have lost a claim or a
            // stage of a stream it does not host, which no quarantine covers.
            if !state.catalog.is_empty() {
                return Err(invalid(
                    "WAL salvage refused: frames past the checkpoint are damaged on a keeper \
                     that holds catalog records, so a lost claim or stage cannot be ruled out; \
                     replace this keeper",
                ));
            }
            quarantined.extend(state.genesis.keys().copied());
        }

        // Verify every surviving stream's retained slices and selected snapshot.
        let check_streams: Vec<StreamId> = state.genesis.keys().copied().collect();
        for stream in check_streams {
            if quarantined.contains(&stream) {
                continue;
            }
            if let Some(log) = state.logs.get(&stream) {
                let mut stream_bad = false;
                for object in log.segments.values() {
                    if let Reference::Segment(loc) = object.reference()
                        && damaged_segments.contains(&loc.segment)
                    {
                        stream_bad = true;
                    }
                    if object.read().is_err() {
                        stream_bad = true;
                        if let Reference::Segment(loc) = object.reference() {
                            damaged_segments.insert(loc.segment);
                        }
                    }
                }
                if let Some(selected) = log.snapshot
                    && let Some(generation) = log.ownership.generation()
                {
                    let snap_dir = crate::stream::consensus::ownership::directory(
                        media.data(),
                        stream,
                        generation,
                    );
                    let genesis = &state.genesis[&stream];
                    let snap_ok = File::open(selected.path(&snap_dir)).and_then(|file| {
                        crate::stream::consensus::storage::snapshot::verify_selected_file(
                            file, &snap_dir, genesis, selected, objects,
                        )
                    });
                    if snap_ok.is_err() {
                        stream_bad = true;
                    }
                }
                if stream_bad {
                    quarantined.insert(stream);
                }
            }
        }

        // Propagate every damaged segment to every stream the checkpoint knew
        // held slices in that segment.
        for seg in &damaged_segments {
            if let Some(scopes) = segment_scopes.get(seg) {
                quarantined.extend(scopes.iter().copied());
            }
        }
        // Only treat registered streams (nonzero) as quarantined streams.
        quarantined.retain(|stream| state.genesis.contains_key(stream));

        let preserved: BTreeSet<StreamId> = state
            .genesis
            .keys()
            .copied()
            .filter(|stream| !quarantined.contains(stream))
            .collect();

        if damaged_segments.is_empty() && quarantined.is_empty() && state.check_hard_state().is_ok()
        {
            return Ok(SalvageReport {
                damaged_segments,
                quarantined,
                preserved,
                salvaged: false,
            });
        }

        // Durably quarantine every affected stream in the registry and strip
        // its unreadable log suffix from the salvaged checkpoint so strict
        // startup succeeds for the preserved streams.
        let reason = format!(
            "WAL salvage skipped damaged segment(s) {:?}",
            damaged_segments
        );
        for &stream in &quarantined {
            quarantine.mark(stream, &reason)?;
            objects.protect(stream);
            if let Some(log) = state.logs.get_mut(&stream) {
                log.entries.clear();
                log.segments.clear();
                log.snapshot = None;
                log.purged = None;
            }
        }
        state.check_hard_state()?;

        // Remove any unpublished segments past `slot.segment`, then start a
        // clean segment and publish a fresh checkpoint + boundary.
        let mut removed = false;
        for item in fs::read_dir(&directory)? {
            let item = item?;
            if item
                .file_name()
                .to_str()
                .and_then(segment::parse)
                .is_some_and(|id| id > slot.segment)
            {
                fs::remove_file(item.path())?;
                removed = true;
            }
        }
        if removed {
            sync_directory(&directory)?;
        }

        let next_segment = slot.segment + 1;
        let _fresh = segment::create(&directory, next_segment, incarnation)?;
        let fresh_position = Position {
            segment: next_segment,
            offset: HEADER,
        };
        let fresh_chain = segment::seed(incarnation);
        let (checkpoint, _pins) = capture(&state, objects, fresh_position, fresh_chain)?;
        let reference = write_checkpoint(&checkpoints, &checkpoint, space, state.cluster_version)?;
        boundaries.write(next_segment, HEADER, fresh_chain, Some(reference))?;

        Ok(SalvageReport {
            damaged_segments,
            quarantined,
            preserved,
            salvaged: true,
        })
    }

    /// Rewrites media in the format before segments as one segment and a
    /// checkpoint, then commits the new format in the registry. Entries of
    /// an indexed WAL stay in their objects; framed entries move to frames.
    pub fn migrate(
        media: &Media,
        boundary: Boundary,
        objects: &Objects,
        space: &Space,
    ) -> io::Result<()> {
        let mut state = legacy::open(media, boundary, objects)?;
        let block = space.allocation_unit();
        let mut budget = 1024 * 1024
            + state.scope_ids().len() as u64 * (legacy::MAX_STREAM_INDEX_BYTES as u64 + 2 * block);
        for log in state.logs.values() {
            if log.segments.len() != log.entries.len() {
                for entry in log.entries.values() {
                    let size = bincode::serialized_size(entry).map_err(io::Error::other)?;
                    budget = budget.saturating_add(size).saturating_add(2 * block);
                }
            }
        }
        let _migration = space.reserve(budget)?;
        media.discard_unpublished_boundaries()?;
        let directory = objects.segment_directory().to_owned();
        let checkpoints = media.data().join(CHECKPOINTS);
        fs::create_dir_all(&checkpoints)?;
        sync_directory(media.data())?;
        for item in fs::read_dir(&directory)?.chain(fs::read_dir(&checkpoints)?) {
            fs::remove_file(item?.path())?;
        }
        sync_directory(&directory)?;
        sync_directory(&checkpoints)?;
        let incarnation = media.incarnation();
        let mut writer = Writer {
            incarnation,
            file: segment::create(&directory, FIRST, incarnation)?,
            directory,
            id: FIRST,
            len: HEADER,
            chain: segment::seed(incarnation),
            buffer: Vec::new(),
            limit: u64::MAX,
        };
        for (&stream, log) in &mut state.logs {
            if log.segments.len() == log.entries.len() {
                continue;
            }
            for entry in log.entries.values() {
                let record = Record::Append(stream, vec![entry.clone()]);
                if let Some((_, slices)) = writer.stage(&record, objects)?.slices {
                    log.segments.extend(slices);
                }
            }
        }
        writer.flush()?;
        let (checkpoint, _pins) = capture(&state, objects, writer.end(), writer.chain)?;
        let reference = write_checkpoint(
            &checkpoints,
            &checkpoint,
            space,
            crate::stream::consensus::CLUSTER_VERSION_V1,
        )?;
        media.migrate(&Slot {
            sequence: 1,
            segment: writer.id,
            offset: writer.len,
            chain: writer.chain,
            checkpoint: Some(reference),
        })
    }

    pub fn contains_scope(&self, scope: StreamId) -> bool {
        self.scopes.contains(&scope)
    }

    pub fn scope_count(&self) -> usize {
        self.scopes.len()
    }

    pub fn stage(&mut self, record: &Record, objects: &Objects) -> io::Result<Staged> {
        self.writer.stage(record, objects)
    }

    /// Keeps `segment` until a checkpoint captured from now on is
    /// published.
    pub fn retire(&mut self, segment: Arc<Segment>) {
        self.retired.push(segment);
    }

    pub fn discard(&mut self, staged: Staged) {
        self.writer.buffer.truncate(staged.start);
    }

    /// Makes the round's frames durable, then publishes them.
    pub fn commit(
        &mut self,
        objects: &Objects,
        scopes: &BTreeSet<StreamId>,
        metrics: &crate::stream::consensus::metrics::Metrics,
    ) -> io::Result<u64> {
        #[cfg(test)]
        let cut = self.cut.replace(0);
        if self.writer.buffer.is_empty() {
            return Ok(0);
        }
        let round_bytes = self.writer.buffer.len() as u64;
        #[cfg(test)]
        if cut == 6 {
            let half = self.writer.buffer.len() / 2;
            self.writer.file.write_all(&self.writer.buffer[..half])?;
            sync_data(&self.writer.file)?;
            return Err(io::Error::other("injected torn WAL frame"));
        }
        self.writer.file.write_all(&self.writer.buffer)?;
        #[cfg(test)]
        if cut == 5 {
            return Err(io::Error::other("injected WAL data sync failure"));
        }
        let segment_sync = Instant::now();
        sync_data(&self.writer.file)?;
        metrics
            .wal_fsync_segment_duration
            .observe(segment_sync.elapsed());
        #[cfg(test)]
        if cut == 2 {
            return Err(io::Error::other("interrupted before the WAL boundary"));
        }
        let end = self.writer.end();
        let chain = segment::chain_frames(self.writer.chain, &self.writer.buffer);
        let ready = self.ready_checkpoint();
        let boundary_sync = self.boundaries.write(
            end.segment,
            end.offset,
            chain,
            ready
                .as_ref()
                .map(|(reference, _)| *reference)
                .or(self.published.reference),
        )?;
        metrics.wal_fsync_boundary_duration.observe(boundary_sync);
        self.since += round_bytes;
        self.writer.advance(chain);
        self.scopes.extend(scopes);
        if let Some((reference, ready)) = ready {
            self.adopt(reference, ready, objects);
        }
        #[cfg(test)]
        if cut == 3 {
            return Err(io::Error::other("interrupted after the WAL boundary"));
        }
        Ok(round_bytes)
    }

    fn adopt(
        &mut self,
        reference: CheckpointRef,
        (position, pins, retired): (Position, Pins, Vec<Arc<Segment>>),
        objects: &Objects,
    ) {
        let old = self.published.reference.replace(reference);
        self.published._pins = pins;
        drop(retired);
        objects.set_floor(position.segment);
        if let Some(old) = old {
            // A name that survives a crash is removed on the next open.
            let _ = fs::remove_file(self.checkpoints.join(checkpoint_name(old.id)));
        }
    }

    #[allow(clippy::type_complexity)]
    fn ready_checkpoint(&mut self) -> Option<(CheckpointRef, (Position, Pins, Vec<Arc<Segment>>))> {
        let Pending {
            handle,
            position,
            pins,
            retired,
        } = self
            .pending
            .take_if(|pending| pending.handle.is_finished())?;
        match handle.join() {
            // The retired segments drop with the old checkpoint's pins
            // once the caller adopts the new one.
            Ok(Ok(reference)) => Some((reference, (position, pins, retired))),
            Ok(Err(error)) => {
                if let Some(dropped) =
                    crate::stream::consensus::logging::rate_limit("wal.checkpoint_deferred", None)
                {
                    tracing::warn!(
                        keeper = %self.keeper,
                        error = %error,
                        dropped = dropped,
                        "WAL checkpoint deferred"
                    );
                }
                self.since = self.since.max(self.tuning.checkpoint_bytes / 2);
                self.retired.extend(retired);
                None
            }
            Err(_) => {
                crate::stream::consensus::logging::critical!(
                    "keeper {} WAL checkpoint writer panicked",
                    self.keeper
                );
                self.retired.extend(retired);
                None
            }
        }
    }

    /// Starts a checkpoint of the installed state once enough frames or time
    /// passed since the last one.
    pub fn maybe_checkpoint(
        &mut self,
        state: &State,
        objects: &Objects,
        space: &Space,
        write_version: u32,
    ) {
        if self.pending.is_some()
            || self.since == 0
            || (self.since < self.tuning.checkpoint_bytes
                && self.last.elapsed() < CHECKPOINT_INTERVAL)
        {
            return;
        }
        if let Err(error) = self.start_checkpoint(state, objects, space, write_version) {
            if let Some(dropped) =
                crate::stream::consensus::logging::rate_limit("wal.checkpoint_start_deferred", None)
            {
                tracing::warn!(
                    keeper = %self.keeper,
                    error = %error,
                    dropped = dropped,
                    "WAL checkpoint deferred"
                );
            }
        }
        #[cfg(test)]
        if self.tuning.synchronous {
            self.publish_now(objects).unwrap();
        }
    }

    fn start_checkpoint(
        &mut self,
        state: &State,
        objects: &Objects,
        space: &Space,
        write_version: u32,
    ) -> io::Result<()> {
        let position = self.writer.end();
        let (checkpoint, pins) = capture(state, objects, position, self.writer.chain)?;
        let directory = self.checkpoints.clone();
        let space = space.clone();
        let handle = std::thread::Builder::new()
            .name("logkeeper-raft-checkpoint".into())
            .spawn(move || write_checkpoint(&directory, &checkpoint, &space, write_version))?;
        self.since = 0;
        self.last = Instant::now();
        self.pending = Some(Pending {
            handle,
            position,
            pins: pins.into(),
            retired: std::mem::take(&mut self.retired),
        });
        Ok(())
    }

    /// Waits for a checkpoint in flight, which stays unpublished.
    pub fn finish(&mut self) {
        if let Some(pending) = self.pending.take() {
            let _ = pending.handle.join();
        }
    }

    #[cfg(test)]
    pub fn interrupt(&self, cut: u8) {
        self.cut.set(cut);
    }

    #[cfg(test)]
    pub fn checkpoint_now(
        &mut self,
        state: &State,
        objects: &Objects,
        space: &Space,
    ) -> io::Result<()> {
        self.checkpoint_now_versioned(state, objects, space, state.cluster_version)
    }

    #[cfg(test)]
    pub fn checkpoint_now_versioned(
        &mut self,
        state: &State,
        objects: &Objects,
        space: &Space,
        write_version: u32,
    ) -> io::Result<()> {
        self.finish();
        self.start_checkpoint(state, objects, space, write_version)?;
        self.publish_now(objects)
    }

    /// Publishes the checkpoint in flight with a boundary of its own.
    #[cfg(test)]
    fn publish_now(&mut self, objects: &Objects) -> io::Result<()> {
        while self
            .pending
            .as_ref()
            .is_some_and(|pending| !pending.handle.is_finished())
        {
            std::thread::yield_now();
        }
        let Some((reference, ready)) = self.ready_checkpoint() else {
            return Err(io::Error::other("WAL checkpoint failed"));
        };
        let end = self.writer.end();
        self.boundaries
            .write(end.segment, end.offset, self.writer.chain, Some(reference))?;
        self.adopt(reference, ready, objects);
        Ok(())
    }

    #[cfg(test)]
    pub fn position(&self) -> Position {
        self.writer.end()
    }

    #[cfg(test)]
    pub fn replayed(&self) -> u64 {
        self.since
    }
}

fn replay(
    directory: &Path,
    incarnation: Uuid,
    state: &mut State,
    objects: &Objects,
    from: Position,
    mut chain: [u8; 32],
    slot: &Slot,
) -> io::Result<u64> {
    let mut replayed = 0;
    for id in from.segment..=slot.segment {
        let file = File::open(directory.join(segment::name(id))).map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                invalid("WAL lost a segment before its trusted boundary")
            } else {
                error
            }
        })?;
        let mut file = BufReader::with_capacity(1024 * 1024, file);
        segment::check_header(&mut file, id, incarnation)?;
        let mut offset = HEADER;
        if id == from.segment && from.offset != HEADER {
            file.seek(SeekFrom::Start(from.offset))?;
            offset = from.offset;
        }
        let end = (id == slot.segment).then_some(slot.offset);
        while Some(offset) != end {
            let frame = segment::next(&mut file)?;
            let (read, next) = match &frame {
                Frame::Complete { body, .. } => (
                    decisions::FrameRead::Complete,
                    offset + FRAME_HEADER + body.len() as u64,
                ),
                Frame::End => (decisions::FrameRead::End, offset),
                Frame::Torn => (decisions::FrameRead::Torn, offset),
            };
            match (decisions::replay_step(read, next, end), frame) {
                (decisions::ReplayStep::Apply, Frame::Complete { header, body }) => {
                    chain = segment::chain(&chain, &header, &body);
                    let record: Record = options()
                        .with_limit(MAX_FRAME)
                        .deserialize(&body)
                        .map_err(newer_record)?;
                    let slices = slices(&record, &body, id, offset + FRAME_HEADER, objects)?;
                    state.apply(record)?;
                    if let Some((stream, slices)) = slices {
                        state.log_mut(stream)?.segments.extend(slices);
                    }
                    replayed += next - offset;
                    offset = next;
                }
                (decisions::ReplayStep::Finish, _) => break,
                (decisions::ReplayStep::Split, _) => {
                    return Err(invalid("trusted WAL boundary splits a frame"));
                }
                (decisions::ReplayStep::Apply | decisions::ReplayStep::Lost, _) => {
                    return Err(invalid(
                        "WAL segment lost acknowledged frames before its trusted boundary",
                    ));
                }
            }
        }
    }
    if chain != slot.chain {
        return Err(invalid("WAL segments do not match their trusted boundary"));
    }
    Ok(replayed)
}

fn capture(
    state: &State,
    objects: &Objects,
    position: Position,
    chain: [u8; 32],
) -> io::Result<(Checkpoint, Vec<Arc<Object>>)> {
    let mut pins = Vec::new();
    let mut leaves = Vec::new();
    for scope in state.scope_ids() {
        leaves.push((scope, Leaf::capture(state, scope)?));
        if let Some(log) = state.logs.get(&scope) {
            pins.extend(log.segments.values().cloned());
        }
    }
    let segments = objects
        .segment_scopes()
        .into_iter()
        .filter(|(id, _)| *id <= position.segment)
        .collect();
    Ok((
        Checkpoint {
            position,
            chain,
            leaves,
            segments,
            committed: state
                .logs
                .iter()
                .filter_map(|(stream, log)| log.committed.map(|id| (*stream, id)))
                .collect(),
        },
        pins,
    ))
}

fn checkpoint_name(id: Uuid) -> String {
    format!("{id}.ckpt")
}

fn write_checkpoint(
    directory: &Path,
    checkpoint: &Checkpoint,
    space: &Space,
    write_version: u32,
) -> io::Result<CheckpointRef> {
    let copy = || Checkpoint {
        position: checkpoint.position,
        chain: checkpoint.chain,
        leaves: checkpoint.leaves.clone(),
        segments: checkpoint.segments.clone(),
        committed: BTreeMap::new(),
    };
    let body = if crate::stream::consensus::decisions::write_version_allows(
        write_version,
        crate::stream::consensus::CLUSTER_VERSION_LEASES,
    ) {
        let mut body = CHECKPOINT_MAGIC_V6.to_vec();
        options()
            .with_limit(MAX_CHECKPOINT)
            .serialize_into(
                &mut body,
                &CheckpointV6 {
                    cluster_version: write_version,
                    checkpoint: copy(),
                    committed: checkpoint.committed.clone(),
                },
            )
            .map_err(io::Error::other)?;
        body
    } else if crate::stream::consensus::decisions::write_version_allows(
        write_version,
        crate::stream::consensus::CLUSTER_VERSION_V2,
    ) {
        let mut body = CHECKPOINT_MAGIC_V5.to_vec();
        options()
            .with_limit(MAX_CHECKPOINT)
            .serialize_into(
                &mut body,
                &CheckpointV5 {
                    cluster_version: write_version,
                    checkpoint: copy(),
                },
            )
            .map_err(io::Error::other)?;
        body
    } else {
        let mut body = CHECKPOINT_MAGIC.to_vec();
        options()
            .with_limit(MAX_CHECKPOINT)
            .serialize_into(&mut body, checkpoint)
            .map_err(io::Error::other)?;
        body
    };
    // Checkpoints let segments be deleted, so they draw on the protected
    // protocol floor rather than the ordinary one.
    let _space = space.protocol(body.len() as u64 + space.allocation_unit())?;
    let reference = CheckpointRef {
        id: Uuid::new_v4(),
        len: body.len() as u64,
        digest: Sha256::digest(&body).into(),
    };
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(directory.join(checkpoint_name(reference.id)))?;
    file.write_all(&body)?;
    sync_file(&file)?;
    sync_directory(directory)?;
    Ok(reference)
}

/// Loads the segmented WAL state strictly read-only from `media`, verifying
/// the checkpoint and every frame up to the active boundary without mutating
/// or truncating any files.
pub(in crate::stream::consensus::storage) fn open_readonly(
    media: &Media,
    objects: &Objects,
) -> io::Result<(State, Slot)> {
    let (_, active) = media.read_boundary_slots()?;
    let slot = active.ok_or_else(|| invalid("WAL boundary has no intact slot"))?;
    let incarnation = media.incarnation();
    let checkpoints = media.data().join(CHECKPOINTS);
    let directory = objects.segment_directory().to_owned();
    let (mut state, position, chain) = match slot.checkpoint {
        Some(reference) => {
            let (mut checkpoint, cluster_version) = read_checkpoint(&checkpoints, reference)?;
            let mut state = State {
                cluster_version,
                ..State::default()
            };
            let committed = std::mem::take(&mut checkpoint.committed);
            for (scope, leaf) in checkpoint.leaves {
                leaf.restore(scope, objects, &mut state)?;
            }
            state.restore_committed(committed);
            (state, checkpoint.position, checkpoint.chain)
        }
        None => (
            State::default(),
            Position {
                segment: FIRST,
                offset: HEADER,
            },
            segment::seed(incarnation),
        ),
    };
    let boundary = Position {
        segment: slot.segment,
        offset: slot.offset,
    };
    if position > boundary || position.offset < HEADER || boundary.offset < HEADER {
        return Err(invalid("WAL checkpoint lies past its trusted boundary"));
    }
    replay(
        &directory,
        incarnation,
        &mut state,
        objects,
        position,
        chain,
        &slot,
    )?;
    state.check_hard_state()?;
    Ok((state, slot))
}

/// A frame that passed its checksum yet does not decode. An unknown record
/// variant is a record a newer release wrote after finalization.
fn newer_record(error: bincode::Error) -> io::Error {
    if error.to_string().contains("expected variant index") {
        invalid(format!(
            "WAL holds a record of a newer format: this media was written by a newer \
             Logkeeper release after the cluster version was finalized, and cannot be \
             opened by this one ({error})"
        ))
    } else {
        io::Error::other(error)
    }
}

pub(in crate::stream::consensus::storage) fn read_checkpoint(
    directory: &Path,
    reference: CheckpointRef,
) -> io::Result<(Checkpoint, u32)> {
    let mut bytes = Vec::new();
    File::open(directory.join(checkpoint_name(reference.id)))
        .map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                invalid("WAL lost the checkpoint its trusted boundary names")
            } else {
                error
            }
        })?
        .take(reference.len.min(MAX_CHECKPOINT) + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != reference.len
        || <[u8; 32]>::from(Sha256::digest(&bytes)) != reference.digest
    {
        return Err(invalid(
            "WAL checkpoint does not match its trusted boundary",
        ));
    }
    if bytes.starts_with(CHECKPOINT_MAGIC_V6) {
        let v6: CheckpointV6 = options()
            .with_limit(MAX_CHECKPOINT)
            .deserialize(&bytes[CHECKPOINT_MAGIC_V6.len()..])
            .map_err(io::Error::other)?;
        let mut checkpoint = v6.checkpoint;
        checkpoint.committed = v6.committed;
        return Ok((checkpoint, v6.cluster_version));
    }
    if bytes.starts_with(CHECKPOINT_MAGIC_V5) {
        let v5: CheckpointV5 = options()
            .with_limit(MAX_CHECKPOINT)
            .deserialize(&bytes[CHECKPOINT_MAGIC_V5.len()..])
            .map_err(io::Error::other)?;
        return Ok((v5.checkpoint, v5.cluster_version));
    }
    if !bytes.starts_with(CHECKPOINT_MAGIC) {
        // The digest matched, so the bytes are what was written: a format
        // this binary does not know, from a release finalized past it.
        return Err(invalid(if bytes.starts_with(b"LKRWAL") {
            "WAL checkpoint is in a newer format: this media was written by a newer Logkeeper \
             release after the cluster version was finalized, and cannot be opened by this one"
        } else {
            "WAL checkpoint does not match its trusted boundary"
        }));
    }
    let checkpoint: Checkpoint = options()
        .with_limit(MAX_CHECKPOINT)
        .deserialize(&bytes[CHECKPOINT_MAGIC.len()..])
        .map_err(io::Error::other)?;
    Ok((checkpoint, crate::stream::consensus::CLUSTER_VERSION_V1))
}

impl Leaf {
    fn capture(state: &State, stream: StreamId) -> io::Result<Self> {
        let log = state.logs.get(&stream);
        let entries = if let Some(log) = log {
            if log.entries.len() != log.segments.len() || log.entries.len() > MAX_SUFFIX {
                return Err(invalid("accepted WAL suffix exceeds its index geometry"));
            }
            log.segments
                .iter()
                .map(|(&index, object)| (index, object.reference()))
                .collect()
        } else {
            BTreeMap::new()
        };
        Ok(Self {
            genesis: state.genesis.get(&stream).cloned(),
            catalog: state.catalog.get(&stream).cloned(),
            vote: log.and_then(|log| log.vote),
            purged: log.and_then(|log| log.purged),
            snapshot: log.and_then(|log| log.snapshot),
            ownership: log.map(|log| log.ownership.clone()),
            entries,
        })
    }

    fn restore(self, scope: StreamId, objects: &Objects, state: &mut State) -> io::Result<()> {
        if let Some(genesis) = self.genesis {
            if genesis.stream != scope || self.entries.len() > MAX_SUFFIX {
                return Err(invalid("WAL leaf scope or suffix bound differs"));
            }
            let mut log = Log {
                vote: self.vote,
                purged: self.purged,
                snapshot: self.snapshot,
                ownership: self
                    .ownership
                    .ok_or_else(|| invalid("WAL leaf lacks replica ownership"))?,
                ..Log::default()
            };
            let mut next = self.purged.map_or(0, |purged| purged.index + 1);
            for (index, reference) in self.entries {
                let owner = match reference {
                    Reference::Object(key) => key.scope,
                    Reference::Segment(location) => location.scope,
                };
                if index != next || owner != scope {
                    return Err(invalid("noncontiguous or foreign WAL entry"));
                }
                let object = objects.resolve(reference)?;
                let entry: Entry = options()
                    .with_limit(MAX_FRAME)
                    .deserialize(&object.read()?)
                    .map_err(io::Error::other)?;
                if index != entry.log_id.index {
                    return Err(invalid("WAL entry log position differs"));
                }
                log.entries.insert(index, entry);
                log.segments.insert(index, object);
                next = next
                    .checked_add(1)
                    .ok_or_else(|| invalid("WAL index exhausted"))?;
            }
            state.genesis.insert(scope, genesis);
            state.logs.insert(scope, log);
        } else if !self.entries.is_empty()
            || self.vote.is_some()
            || self.purged.is_some()
            || self.snapshot.is_some()
        {
            return Err(invalid("unregistered WAL leaf contains hard state"));
        }
        if let Some(catalog) = self.catalog {
            if catalog.genesis.stream != scope {
                return Err(invalid("catalog leaf scope differs"));
            }
            state.catalog.insert(scope, catalog);
        }
        Ok(())
    }

    /// Best-effort leaf restore for offline salvage. Returns `(damaged,
    /// bad_segments)` where `damaged` is true if this stream's state could not
    /// be cleanly restored and `bad_segments` lists any WAL segments whose
    /// slices failed verification.
    fn restore_salvage(
        self,
        scope: StreamId,
        objects: &Objects,
        damaged_segments: &BTreeSet<u64>,
        state: &mut State,
    ) -> io::Result<(bool, BTreeSet<u64>)> {
        let mut bad = BTreeSet::new();
        let mut failed = false;
        if let Some(genesis) = self.genesis {
            if genesis.stream != scope || self.entries.len() > MAX_SUFFIX {
                return Err(invalid("WAL leaf scope or suffix bound differs"));
            }
            let ownership = self
                .ownership
                .ok_or_else(|| invalid("WAL leaf lacks replica ownership"))?;
            let mut log = Log {
                vote: self.vote,
                purged: self.purged,
                snapshot: self.snapshot,
                ownership,
                ..Log::default()
            };
            let mut next = self.purged.map_or(0, |purged| purged.index + 1);
            for (index, reference) in self.entries {
                let expected = next;
                next = next
                    .checked_add(1)
                    .ok_or_else(|| invalid("WAL index exhausted"))?;
                if let Reference::Segment(location) = reference
                    && damaged_segments.contains(&location.segment)
                {
                    bad.insert(location.segment);
                    failed = true;
                    continue;
                }
                let loaded = objects.resolve(reference).and_then(|object| {
                    let bytes = object.read()?;
                    let entry: Entry = options()
                        .with_limit(MAX_FRAME)
                        .deserialize(&bytes)
                        .map_err(io::Error::other)?;
                    if index != expected || index != entry.log_id.index {
                        return Err(invalid("WAL entry log position differs"));
                    }
                    Ok((object, entry))
                });
                match loaded {
                    Ok((object, entry)) => {
                        log.entries.insert(index, entry);
                        log.segments.insert(index, object);
                    }
                    Err(_) => {
                        failed = true;
                        if let Reference::Segment(location) = reference {
                            bad.insert(location.segment);
                        }
                    }
                }
            }
            if failed {
                log.entries.clear();
                log.segments.clear();
                log.snapshot = None;
                log.purged = None;
            }
            state.genesis.insert(scope, genesis);
            state.logs.insert(scope, log);
        }
        if let Some(catalog) = self.catalog {
            if catalog.genesis.stream != scope {
                return Err(invalid("catalog leaf scope differs"));
            }
            state.catalog.insert(scope, catalog);
        }
        Ok((failed, bad))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_record_of_a_newer_release_is_named_as_such() {
        let unknown = 1000u32.to_le_bytes();
        let error = options()
            .with_limit(MAX_FRAME)
            .deserialize::<Record>(&unknown)
            .map_err(newer_record)
            .err()
            .expect("an unknown record variant does not decode");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(
            error.to_string().contains("newer Logkeeper release"),
            "{error}"
        );
    }
}
