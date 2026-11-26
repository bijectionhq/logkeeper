//! Offline inspection, verification, and segment dump tools for a stopped
//! consensus keeper data directory. All operations are strictly read-only.

use std::{
    collections::BTreeMap,
    fmt,
    fs::{self, File},
    io::{self, BufReader},
    path::{Path, PathBuf},
};

use bincode::Options as _;
use journal_contract::StreamId;
use openraft::EntryPayload;
use serde::Serialize;
use uuid::Uuid;

use super::{
    Record,
    media::{Enrollment, Opened, Slot, hex},
    objects::Objects,
    segment::{self, FIRST, FRAME_HEADER, HEADER, MAX_FRAME, RawFrame},
    snapshot,
    wal::segmented::{self, Position},
};
use crate::stream::consensus::{
    LogId, invalid, logging::stream_uuid, options, placement::Placement,
};

#[derive(Clone, Debug, Serialize)]
pub struct LogIdInfo {
    pub term: u64,
    pub index: u64,
}

fn log_id_info(id: LogId) -> LogIdInfo {
    LogIdInfo {
        term: id.leader_id.term,
        index: id.index,
    }
}

impl fmt::Display for LogIdInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "term={} index={}", self.term, self.index)
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct VoteInfo {
    pub term: u64,
    pub voted_for: Uuid,
    pub committed: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct FenceInfo {
    pub epoch: u64,
    pub writer: Uuid,
    pub owner: String,
    pub recovery_fence: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct LogRangeInfo {
    pub purged: Option<LogIdInfo>,
    pub first_index: Option<u64>,
    pub last_index: Option<u64>,
    pub entries: usize,
    pub snapshot_log_id: Option<LogIdInfo>,
    pub snapshot_digest: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct MembershipInfo {
    pub revision: Option<u64>,
    pub voters: Vec<Uuid>,
    pub joint_voters: Option<Vec<Uuid>>,
    pub learners: Vec<Uuid>,
}

#[derive(Clone, Debug, Serialize)]
pub struct OwnershipInfo {
    pub generation: Option<u64>,
    pub installed: bool,
    pub high_water: u64,
    pub current_revision: Option<u64>,
    pub detached: Vec<u64>,
    pub retired: Option<(u64, u64)>,
    pub staged_target: Option<Vec<Uuid>>,
}

#[derive(Clone, Debug, Serialize)]
pub struct StreamInspection {
    pub stream: Uuid,
    pub genesis_voters: Vec<Uuid>,
    pub quota_bytes: u64,
    pub vote: Option<VoteInfo>,
    pub membership: MembershipInfo,
    pub log_range: LogRangeInfo,
    pub snapshot_applied: Option<LogIdInfo>,
    pub applied: Option<LogIdInfo>,
    pub fence: Option<FenceInfo>,
    pub head: Option<u64>,
    pub floor: Option<u64>,
    pub stream_state: String,
    pub retained_records: u64,
    pub retained_bytes: u64,
    pub ownership: OwnershipInfo,
    /// Parking is runtime-only and cleared across restarts, so always `false`
    /// on a stopped directory.
    pub parked: bool,
    pub quarantined: bool,
    pub quarantine_reason: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct InspectReport {
    pub keeper: Uuid,
    pub incarnation: Uuid,
    pub boundary_sequence: u64,
    pub boundary_segment: u64,
    pub boundary_offset: u64,
    pub boundary_chain: String,
    pub streams: Vec<StreamInspection>,
}

impl fmt::Display for InspectReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "keeper={} incarnation={} boundary=seq:{} seg:{} off:{} chain={} streams={}",
            self.keeper,
            self.incarnation,
            self.boundary_sequence,
            self.boundary_segment,
            self.boundary_offset,
            self.boundary_chain,
            self.streams.len()
        )?;
        for s in &self.streams {
            writeln!(f, "stream {}", s.stream)?;
            match &s.vote {
                Some(vote) => writeln!(
                    f,
                    "  vote: term={} voted_for={} committed={}",
                    vote.term, vote.voted_for, vote.committed
                )?,
                None => writeln!(f, "  vote: none")?,
            }
            writeln!(
                f,
                "  membership: rev={:?} voters={:?} joint={:?} learners={:?}",
                s.membership.revision,
                s.membership.voters,
                s.membership.joint_voters,
                s.membership.learners
            )?;
            writeln!(
                f,
                "  log_range: purged={:?} first={:?} last={:?} entries={} snapshot={:?}",
                s.log_range.purged.as_ref().map(|id| id.to_string()),
                s.log_range.first_index,
                s.log_range.last_index,
                s.log_range.entries,
                s.log_range
                    .snapshot_log_id
                    .as_ref()
                    .map(|id| id.to_string()),
            )?;
            writeln!(
                f,
                "  applied: replayed={:?} snapshot={:?}",
                s.applied.as_ref().map(|id| id.to_string()),
                s.snapshot_applied.as_ref().map(|id| id.to_string()),
            )?;
            match &s.fence {
                Some(fence) => writeln!(
                    f,
                    "  fence: epoch={} writer={} owner={:?} recovery={}",
                    fence.epoch, fence.writer, fence.owner, fence.recovery_fence
                )?,
                None => writeln!(f, "  fence: none")?,
            }
            writeln!(
                f,
                "  head: {:?} floor={:?} state={} retained_records={} retained_bytes={}/{}",
                s.head,
                s.floor,
                s.stream_state,
                s.retained_records,
                s.retained_bytes,
                s.quota_bytes
            )?;
            writeln!(
                f,
                "  ownership: gen={:?} installed={} high_water={} detached={:?} retired={:?}",
                s.ownership.generation,
                s.ownership.installed,
                s.ownership.high_water,
                s.ownership.detached,
                s.ownership.retired
            )?;
            writeln!(
                f,
                "  status: parked={} (not persisted across restarts) quarantined={} reason={:?}",
                s.parked, s.quarantined, s.quarantine_reason
            )?;
        }
        Ok(())
    }
}

/// Inspects every stream (or a single `filter` stream) in a stopped keeper's
/// data directory strictly read-only.
pub(in crate::stream::consensus) fn inspect(
    enrollment: Enrollment,
    placement: &Placement,
    filter: Option<StreamId>,
) -> io::Result<InspectReport> {
    let (media, _lock, opened) = enrollment.open_readonly()?;
    if !matches!(opened, Opened::Current) {
        return Err(invalid(
            "inspect requires migrated segmented WAL format (start keeper once to migrate legacy WAL)",
        ));
    }
    let objects = Objects::open_readonly(media.data());
    let (state, slot) = segmented::open_readonly(&media, &objects)?;
    let mut streams = Vec::new();
    for (&stream, genesis) in &state.genesis {
        if filter.is_some_and(|wanted| wanted != stream) {
            continue;
        }
        let log = &state.logs[&stream];
        let vote = log.vote.map(|vote| VoteInfo {
            term: vote.leader_id().term,
            voted_for: Uuid::from_u128(vote.leader_id().voted_for),
            committed: vote.is_committed(),
        });
        let log_range = LogRangeInfo {
            purged: log.purged.map(log_id_info),
            first_index: log.entries.first_key_value().map(|(&idx, _)| idx),
            last_index: log.entries.last_key_value().map(|(&idx, _)| idx),
            entries: log.entries.len(),
            snapshot_log_id: log.snapshot.map(|s| log_id_info(s.log_id)),
            snapshot_digest: log.snapshot.map(|s| hex(&s.digest)),
        };
        let ownership = OwnershipInfo {
            generation: log.ownership.generation(),
            installed: log.ownership.installed(),
            high_water: log.ownership.high_water(),
            current_revision: log.ownership.current_revision(),
            detached: log.ownership.detached().to_vec(),
            retired: log.ownership.retired_info(),
            staged_target: log
                .ownership
                .current_stage()
                .map(|stage| stage.target.to_vec()),
        };

        let inspection = if log.ownership.generation().is_none() {
            StreamInspection {
                stream: stream_uuid(stream),
                genesis_voters: genesis.voters.to_vec(),
                quota_bytes: genesis.quota_bytes,
                vote,
                membership: MembershipInfo {
                    revision: None,
                    voters: Vec::new(),
                    joint_voters: None,
                    learners: Vec::new(),
                },
                log_range,
                snapshot_applied: None,
                applied: None,
                fence: None,
                head: None,
                floor: None,
                stream_state: "detached".into(),
                retained_records: 0,
                retained_bytes: 0,
                ownership,
                parked: false,
                quarantined: false,
                quarantine_reason: None,
            }
        } else {
            match snapshot::inspect_stream_readonly(media.data(), &objects, genesis, log, placement)
            {
                Ok(view) => StreamInspection {
                    stream: stream_uuid(stream),
                    genesis_voters: genesis.voters.to_vec(),
                    quota_bytes: genesis.quota_bytes,
                    vote,
                    membership: MembershipInfo {
                        revision: view.configuration.map(|cfg| cfg.revision),
                        voters: if view.voters.is_empty() {
                            genesis.voters.to_vec()
                        } else {
                            view.voters
                        },
                        joint_voters: view.joint_voters,
                        learners: view.learners,
                    },
                    log_range,
                    snapshot_applied: view.snapshot_applied.map(log_id_info),
                    applied: view.applied.map(log_id_info),
                    fence: view.fence.map(|(fence, owner)| FenceInfo {
                        epoch: fence.epoch.0,
                        writer: fence.writer,
                        owner,
                        recovery_fence: view.recovering,
                    }),
                    head: view.head.map(|lsn| lsn.0),
                    floor: view.floor.map(|lsn| lsn.0),
                    stream_state: view.stream_state.into(),
                    retained_records: view.retained_records,
                    retained_bytes: view.retained_bytes,
                    ownership,
                    parked: false,
                    quarantined: false,
                    quarantine_reason: None,
                },
                Err(error) => StreamInspection {
                    stream: stream_uuid(stream),
                    genesis_voters: genesis.voters.to_vec(),
                    quota_bytes: genesis.quota_bytes,
                    vote,
                    membership: MembershipInfo {
                        revision: None,
                        voters: genesis.voters.to_vec(),
                        joint_voters: None,
                        learners: Vec::new(),
                    },
                    log_range,
                    snapshot_applied: None,
                    applied: None,
                    fence: None,
                    head: None,
                    floor: None,
                    stream_state: "quarantined".into(),
                    retained_records: 0,
                    retained_bytes: 0,
                    ownership,
                    parked: false,
                    quarantined: true,
                    quarantine_reason: Some(error.to_string()),
                },
            }
        };
        streams.push(inspection);
    }
    Ok(InspectReport {
        keeper: media.keeper(),
        incarnation: media.incarnation(),
        boundary_sequence: slot.sequence,
        boundary_segment: slot.segment,
        boundary_offset: slot.offset,
        boundary_chain: hex(&slot.chain),
        streams,
    })
}

#[derive(Clone, Debug, Serialize)]
pub struct BoundarySlotReport {
    pub slot_index: usize,
    pub valid: bool,
    pub sequence: Option<u64>,
    pub segment: Option<u64>,
    pub offset: Option<u64>,
    pub chain: Option<String>,
    pub checkpoint_id: Option<Uuid>,
}

impl BoundarySlotReport {
    fn from_slot(slot_index: usize, slot: Option<Slot>) -> Self {
        match slot {
            Some(slot) => Self {
                slot_index,
                valid: true,
                sequence: Some(slot.sequence),
                segment: Some(slot.segment),
                offset: Some(slot.offset),
                chain: Some(hex(&slot.chain)),
                checkpoint_id: slot.checkpoint.map(|ckpt| ckpt.id),
            },
            None => Self {
                slot_index,
                valid: false,
                sequence: None,
                segment: None,
                offset: None,
                chain: None,
                checkpoint_id: None,
            },
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct CheckpointReport {
    pub id: Uuid,
    pub segment: u64,
    pub offset: u64,
    pub chain: String,
    pub leaves: usize,
    pub references_checked: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct VerifyReport {
    pub ok: bool,
    pub keeper: Uuid,
    pub incarnation: Uuid,
    pub boundary_slots: [BoundarySlotReport; 2],
    pub active_sequence: Option<u64>,
    pub active_segment: Option<u64>,
    pub active_offset: Option<u64>,
    pub active_chain: Option<String>,
    pub checkpoint: Option<CheckpointReport>,
    pub checkpoint_chain_verified: bool,
    pub boundary_chain_verified: bool,
    pub segments_checked: usize,
    pub frames_checked: u64,
    pub bytes_checked: u64,
    pub unpublished_tail_bytes: u64,
    pub unpublished_segments: usize,
    pub errors: Vec<String>,
}

impl fmt::Display for VerifyReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "verify {}: keeper={} incarnation={} segments={} frames={} bytes={} checkpoint_chain={} boundary_chain={}",
            if self.ok { "OK" } else { "FAILED" },
            self.keeper,
            self.incarnation,
            self.segments_checked,
            self.frames_checked,
            self.bytes_checked,
            self.checkpoint_chain_verified,
            self.boundary_chain_verified
        )?;
        for slot in &self.boundary_slots {
            writeln!(
                f,
                "  boundary slot {}: valid={} seq={:?} seg={:?} off={:?} ckpt={:?}",
                slot.slot_index,
                slot.valid,
                slot.sequence,
                slot.segment,
                slot.offset,
                slot.checkpoint_id
            )?;
        }
        if let Some(ckpt) = &self.checkpoint {
            writeln!(
                f,
                "  checkpoint: id={} seg={} off={} leaves={} refs_checked={}",
                ckpt.id, ckpt.segment, ckpt.offset, ckpt.leaves, ckpt.references_checked
            )?;
        }
        if self.unpublished_tail_bytes > 0 || self.unpublished_segments > 0 {
            writeln!(
                f,
                "  unpublished tail: {} bytes, {} trailing segments past boundary",
                self.unpublished_tail_bytes, self.unpublished_segments
            )?;
        }
        for error in &self.errors {
            writeln!(f, "  ERROR: {error}")?;
        }
        Ok(())
    }
}

/// Walks every WAL segment frame CRC, the checkpoint digest and references,
/// and the running SHA-256 hash chain against the trusted boundary slots.
pub(in crate::stream::consensus) fn verify(enrollment: Enrollment) -> io::Result<VerifyReport> {
    let (media, _lock, opened) = enrollment.open_readonly()?;
    if !matches!(opened, Opened::Current) {
        return Err(invalid(
            "verify requires migrated segmented WAL format (start keeper once to migrate legacy WAL)",
        ));
    }
    let keeper = media.keeper();
    let incarnation = media.incarnation();
    let mut errors = Vec::new();
    let ([slot0, slot1], active) = match media.read_boundary_slots() {
        Ok(slots) => slots,
        Err(error) => {
            errors.push(format!("boundary slots unreadable: {error}"));
            ([None, None], None)
        }
    };
    let boundary_slots = [
        BoundarySlotReport::from_slot(0, slot0),
        BoundarySlotReport::from_slot(1, slot1),
    ];
    let Some(active) = active else {
        if errors.is_empty() {
            errors.push("WAL boundary has no intact slot".into());
        }
        return Ok(VerifyReport {
            ok: false,
            keeper,
            incarnation,
            boundary_slots,
            active_sequence: None,
            active_segment: None,
            active_offset: None,
            active_chain: None,
            checkpoint: None,
            checkpoint_chain_verified: false,
            boundary_chain_verified: false,
            segments_checked: 0,
            frames_checked: 0,
            bytes_checked: 0,
            unpublished_tail_bytes: 0,
            unpublished_segments: 0,
            errors,
        });
    };

    let objects = Objects::open_readonly(media.data());
    let checkpoints_dir = media.data().join(segmented::CHECKPOINTS);
    let segments_dir = objects.segment_directory().to_owned();

    // Verify checkpoint if referenced by the active boundary slot.
    let (ckpt_report, ckpt_pos, ckpt_chain) = match active.checkpoint {
        Some(reference) => match segmented::read_checkpoint(&checkpoints_dir, reference) {
            Ok((ckpt, _)) => {
                let mut refs_checked = 0usize;
                for (stream, leaf) in &ckpt.leaves {
                    for (&index, r) in &leaf.entries {
                        match objects.resolve(*r).and_then(|obj| obj.read()) {
                            Ok(_) => refs_checked += 1,
                            Err(error) => errors.push(format!(
                                "checkpoint reference for stream {} index {} failed: {error}",
                                stream_uuid(*stream),
                                index
                            )),
                        }
                    }
                }
                let boundary_pos = Position {
                    segment: active.segment,
                    offset: active.offset,
                };
                if ckpt.position > boundary_pos || ckpt.position.offset < HEADER {
                    errors.push(format!(
                        "checkpoint position ({}, {}) is invalid relative to boundary ({}, {})",
                        ckpt.position.segment, ckpt.position.offset, active.segment, active.offset
                    ));
                }
                let report = CheckpointReport {
                    id: reference.id,
                    segment: ckpt.position.segment,
                    offset: ckpt.position.offset,
                    chain: hex(&ckpt.chain),
                    leaves: ckpt.leaves.len(),
                    references_checked: refs_checked,
                };
                (Some(report), ckpt.position, ckpt.chain)
            }
            Err(error) => {
                errors.push(format!("checkpoint {} invalid: {error}", reference.id));
                (
                    None,
                    Position {
                        segment: FIRST,
                        offset: HEADER,
                    },
                    segment::seed(incarnation),
                )
            }
        },
        None => (
            None,
            Position {
                segment: FIRST,
                offset: HEADER,
            },
            segment::seed(incarnation),
        ),
    };

    // Discover all segment files on disk.
    let mut disk_segments = BTreeMap::<u64, PathBuf>::new();
    match fs::read_dir(&segments_dir) {
        Ok(entries) => {
            for item in entries {
                if let Ok(item) = item
                    && let Some(id) = item.file_name().to_str().and_then(segment::parse)
                {
                    disk_segments.insert(id, item.path());
                }
            }
        }
        Err(error) => errors.push(format!("could not list raft-segments: {error}")),
    }

    // Check if we can also verify the full hash chain from segment FIRST through the checkpoint.
    let can_verify_ckpt_chain = ckpt_report.is_some()
        && (FIRST..=ckpt_pos.segment).all(|id| disk_segments.contains_key(&id));

    let mut segments_checked = 0usize;
    let mut frames_checked = 0u64;
    let mut bytes_checked = 0u64;
    let mut unpublished_tail_bytes = 0u64;
    let mut unpublished_segments = 0usize;

    let mut pre_ckpt_chain = segment::seed(incarnation);
    let mut post_ckpt_chain = ckpt_chain;
    let mut checkpoint_chain_verified = ckpt_report.is_none();
    let mut reached_ckpt = ckpt_report.is_none();
    let mut reached_boundary = false;

    // Ensure every segment required from ckpt_pos.segment..=active.segment exists.
    for id in ckpt_pos.segment..=active.segment {
        if !disk_segments.contains_key(&id) {
            errors.push(format!(
                "missing required WAL segment {} before trusted boundary",
                segment::name(id)
            ));
        }
    }

    for (&id, path) in &disk_segments {
        if id > active.segment {
            unpublished_segments += 1;
            continue;
        }
        segments_checked += 1;
        let file = match File::open(path) {
            Ok(file) => file,
            Err(error) => {
                errors.push(format!(
                    "cannot open segment {}: {error}",
                    segment::name(id)
                ));
                continue;
            }
        };
        let file_len = file.metadata().map(|m| m.len()).unwrap_or(0);
        let mut reader = BufReader::with_capacity(1024 * 1024, file);
        if let Err(error) = segment::check_header(&mut reader, id, incarnation) {
            errors.push(format!(
                "segment {} header invalid: {error}",
                segment::name(id)
            ));
            continue;
        }
        let mut offset = HEADER;
        let boundary_end = (id == active.segment).then_some(active.offset);
        if id == ckpt_pos.segment && offset == ckpt_pos.offset {
            reached_ckpt = true;
            if can_verify_ckpt_chain {
                if pre_ckpt_chain == ckpt_chain {
                    checkpoint_chain_verified = true;
                } else {
                    errors.push(format!(
                        "hash chain at checkpoint ({}, {}) mismatch: expected {}, computed {}",
                        ckpt_pos.segment,
                        ckpt_pos.offset,
                        hex(&ckpt_chain),
                        hex(&pre_ckpt_chain)
                    ));
                }
            }
        }
        if boundary_end == Some(offset) {
            reached_boundary = true;
        }

        loop {
            if let Some(end) = boundary_end
                && offset >= end
            {
                if file_len > end {
                    unpublished_tail_bytes += file_len - end;
                }
                break;
            }
            match segment::next_raw(&mut reader)? {
                RawFrame::End => {
                    if let Some(end) = boundary_end
                        && offset < end
                    {
                        errors.push(format!(
                            "segment {} ended at offset {offset} before trusted boundary {end}",
                            segment::name(id)
                        ));
                    }
                    break;
                }
                RawFrame::Torn { reason } => {
                    errors.push(format!(
                        "segment {} torn frame at offset {offset}: {reason}",
                        segment::name(id)
                    ));
                    break;
                }
                RawFrame::Complete {
                    header,
                    body,
                    expected_crc,
                    actual_crc,
                } => {
                    let next = offset + FRAME_HEADER + body.len() as u64;
                    if let Some(end) = boundary_end
                        && next > end
                    {
                        errors.push(format!(
                            "segment {} frame at offset {offset}..{next} splits trusted boundary {end}",
                            segment::name(id)
                        ));
                        break;
                    }
                    if expected_crc != actual_crc {
                        errors.push(format!(
                            "segment {} frame at offset {offset} CRC mismatch: header={expected_crc:#010x} actual={actual_crc:#010x}",
                            segment::name(id)
                        ));
                    } else if let Err(error) =
                        options().with_limit(MAX_FRAME).deserialize::<Record>(&body)
                    {
                        errors.push(format!(
                            "segment {} frame at offset {offset} failed Record decode: {error}",
                            segment::name(id)
                        ));
                    }

                    frames_checked += 1;
                    bytes_checked += next - offset;

                    // Update pre-checkpoint chain if walking contiguously from FIRST.
                    if can_verify_ckpt_chain
                        && (id < ckpt_pos.segment
                            || (id == ckpt_pos.segment && next <= ckpt_pos.offset))
                    {
                        pre_ckpt_chain = segment::chain(&pre_ckpt_chain, &header, &body);
                    }
                    // Update post-checkpoint chain for frames after checkpoint position up to boundary.
                    if id > ckpt_pos.segment
                        || (id == ckpt_pos.segment && offset >= ckpt_pos.offset)
                    {
                        post_ckpt_chain = segment::chain(&post_ckpt_chain, &header, &body);
                    }

                    offset = next;
                    if id == ckpt_pos.segment && offset == ckpt_pos.offset {
                        reached_ckpt = true;
                        if can_verify_ckpt_chain {
                            if pre_ckpt_chain == ckpt_chain {
                                checkpoint_chain_verified = true;
                            } else {
                                errors.push(format!(
                                    "hash chain at checkpoint ({}, {}) mismatch: expected {}, computed {}",
                                    ckpt_pos.segment,
                                    ckpt_pos.offset,
                                    hex(&ckpt_chain),
                                    hex(&pre_ckpt_chain)
                                ));
                            }
                        }
                    }
                    if boundary_end == Some(offset) {
                        reached_boundary = true;
                    }
                }
            }
        }
    }

    if !reached_ckpt && ckpt_report.is_some() {
        errors.push(format!(
            "checkpoint position ({}, {}) did not land on a frame boundary",
            ckpt_pos.segment, ckpt_pos.offset
        ));
    }
    let boundary_chain_verified = if !reached_boundary {
        errors.push(format!(
            "did not reach active boundary ({}, {})",
            active.segment, active.offset
        ));
        false
    } else if post_ckpt_chain != active.chain {
        errors.push(format!(
            "hash chain at boundary ({}, {}) mismatch: boundary={}, computed={}",
            active.segment,
            active.offset,
            hex(&active.chain),
            hex(&post_ckpt_chain)
        ));
        false
    } else {
        true
    };

    Ok(VerifyReport {
        ok: errors.is_empty(),
        keeper,
        incarnation,
        boundary_slots,
        active_sequence: Some(active.sequence),
        active_segment: Some(active.segment),
        active_offset: Some(active.offset),
        active_chain: Some(hex(&active.chain)),
        checkpoint: ckpt_report,
        checkpoint_chain_verified,
        boundary_chain_verified,
        segments_checked,
        frames_checked,
        bytes_checked,
        unpublished_tail_bytes,
        unpublished_segments,
        errors,
    })
}

#[derive(Clone, Debug, Serialize)]
pub struct FrameDump {
    pub index: usize,
    pub offset: u64,
    pub length: u32,
    pub crc: String,
    pub crc_ok: bool,
    pub summary: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct SegmentDump {
    pub path: String,
    pub segment_id: u64,
    pub incarnation: Uuid,
    pub file_bytes: u64,
    pub frames: Vec<FrameDump>,
    pub truncated_tail_offset: Option<u64>,
    pub truncated_tail_reason: Option<String>,
}

impl fmt::Display for SegmentDump {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "segment={} incarnation={} file_bytes={} frames={} path={}",
            self.segment_id,
            self.incarnation,
            self.file_bytes,
            self.frames.len(),
            self.path
        )?;
        for frame in &self.frames {
            writeln!(
                f,
                "  #{:<5} off={:<10} len={:<8} crc={} crc_ok={} {}",
                frame.index, frame.offset, frame.length, frame.crc, frame.crc_ok, frame.summary
            )?;
        }
        if let Some(off) = self.truncated_tail_offset {
            writeln!(
                f,
                "  torn tail at offset {off}: {}",
                self.truncated_tail_reason.as_deref().unwrap_or("truncated")
            )?;
        }
        Ok(())
    }
}

/// Dumps a single WAL segment file by path, read-only.
pub fn dump_segment_file(path: &Path, limit: Option<usize>) -> io::Result<SegmentDump> {
    let file = File::open(path)?;
    let file_bytes = file.metadata()?.len();
    let mut reader = BufReader::with_capacity(1024 * 1024, file);
    let (segment_id, incarnation) = segment::read_header(&mut reader)?;
    let mut offset = HEADER;
    let mut frames = Vec::new();
    let mut truncated_tail_offset = None;
    let mut truncated_tail_reason = None;

    while limit.is_none_or(|max| frames.len() < max) {
        match segment::next_raw(&mut reader)? {
            RawFrame::End => break,
            RawFrame::Torn { reason } => {
                truncated_tail_offset = Some(offset);
                truncated_tail_reason = Some(reason);
                break;
            }
            RawFrame::Complete {
                body,
                expected_crc,
                actual_crc,
                ..
            } => {
                let crc_ok = expected_crc == actual_crc;
                let summary = if crc_ok {
                    match options().with_limit(MAX_FRAME).deserialize::<Record>(&body) {
                        Ok(record) => summarize_record(&record),
                        Err(error) => format!("DecodeError({error})"),
                    }
                } else {
                    format!("CorruptCrc(actual={actual_crc:#010x})")
                };
                let length = body.len() as u32;
                frames.push(FrameDump {
                    index: frames.len(),
                    offset,
                    length,
                    crc: format!("{expected_crc:#010x}"),
                    crc_ok,
                    summary,
                });
                offset += FRAME_HEADER + u64::from(length);
            }
        }
    }

    Ok(SegmentDump {
        path: path.display().to_string(),
        segment_id,
        incarnation,
        file_bytes,
        frames,
        truncated_tail_offset,
        truncated_tail_reason,
    })
}

/// Dumps segment `segment_id` from a stopped keeper's enrolled data directory.
pub(in crate::stream::consensus) fn dump_segment_for_keeper(
    enrollment: Enrollment,
    segment_id: u64,
    limit: Option<usize>,
) -> io::Result<SegmentDump> {
    let (media, _lock, _) = enrollment.open_readonly()?;
    let path = media
        .data()
        .join(segment::DIRECTORY)
        .join(segment::name(segment_id));
    let dump = dump_segment_file(&path, limit)?;
    if dump.segment_id != segment_id || dump.incarnation != media.incarnation() {
        return Err(invalid(
            "WAL segment header does not match this keeper's incarnation or segment ID",
        ));
    }
    Ok(dump)
}

fn summarize_record(record: &Record) -> String {
    match record {
        Record::Register(g) => format!(
            "Register(stream={}, voters={:?}, quota={})",
            stream_uuid(g.stream),
            g.voters,
            g.quota_bytes
        ),
        Record::Claim(g) => format!(
            "Claim(stream={}, voters={:?}, quota={})",
            stream_uuid(g.stream),
            g.voters,
            g.quota_bytes
        ),
        Record::Stage(s) => format!(
            "Stage(stream={}, source={}, old={:?} -> target={:?})",
            stream_uuid(s.stream),
            s.source,
            s.old,
            s.target
        ),
        Record::Vote(stream, vote) => format!(
            "Vote(stream={}, term={}, voted_for={}, committed={})",
            stream_uuid(*stream),
            vote.leader_id().term,
            Uuid::from_u128(vote.leader_id().voted_for),
            vote.is_committed()
        ),
        Record::Append(stream, entries) => {
            format!(
                "Append(stream={}, {})",
                stream_uuid(*stream),
                summarize_entries(entries)
            )
        }
        Record::Relocate(from, body) => format!(
            "Relocate(stream={}, bytes={})",
            stream_uuid(from.scope),
            body.len()
        ),
        Record::Truncate(stream, since) => {
            format!("Truncate(stream={}, since={since})", stream_uuid(*stream))
        }
        Record::ClusterVersion(version) => format!("ClusterVersion(version={version})"),
        Record::Purge(stream, log_id) => format!(
            "Purge(stream={}, term={}, index={})",
            stream_uuid(*stream),
            log_id.leader_id.term,
            log_id.index
        ),
        Record::Snapshot(stream, selected) => format!(
            "Snapshot(stream={}, term={}, index={}, digest={})",
            stream_uuid(*stream),
            selected.log_id.leader_id.term,
            selected.log_id.index,
            &hex(&selected.digest)[..16]
        ),
        Record::Contacts(stream, contacts) => format!(
            "Contacts(stream={}, count={})",
            stream_uuid(*stream),
            contacts.len()
        ),
        Record::Ownership(stream, change) => {
            format!("Ownership(stream={}, {change:?})", stream_uuid(*stream))
        }
        Record::Owned(generation, inner) => {
            format!("Owned(gen={generation}, {})", summarize_record(inner))
        }
        Record::Recover(stream, vote, entries) => format!(
            "Recover(stream={}, term={}, voted_for={}, {})",
            stream_uuid(*stream),
            vote.leader_id().term,
            Uuid::from_u128(vote.leader_id().voted_for),
            summarize_entries(entries)
        ),
    }
}

fn summarize_entries(entries: &[crate::stream::consensus::Entry]) -> String {
    if entries.is_empty() {
        return "0 entries".into();
    }
    let first = entries.first().unwrap().log_id.index;
    let last = entries.last().unwrap().log_id.index;
    let preview = entries
        .iter()
        .take(4)
        .map(|entry| match &entry.payload {
            EntryPayload::Blank => format!("{}:Blank", entry.log_id.index),
            EntryPayload::Normal(cmd) => format!("{}:{cmd}", entry.log_id.index),
            EntryPayload::Membership(m) => {
                format!(
                    "{}:Membership({:?})",
                    entry.log_id.index,
                    m.get_joint_config().len()
                )
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    if entries.len() > 4 {
        format!(
            "{} entries ({first}..={last}) [{preview}, ...]",
            entries.len()
        )
    } else {
        format!("{} entries ({first}..={last}) [{preview}]", entries.len())
    }
}
