//! Admission, classification and restart decisions for keeper-hosted
//! consensus. The keeper calls these functions directly, and Verus checks
//! them in `verification/verus/consensus_admission`.
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Verus checks these values directly, so each is written as a literal.

/// Disk bytes each reserved class keeps free for itself. The floors below
/// are sums of these budgets, and the Verus laws use all four.
#[allow(dead_code)]
pub const CONTROL_BYTES: u64 = 33_554_432; // 32 MiB
pub const MAINTENANCE_BYTES: u64 = 8_388_608; // 8 MiB
pub const SCRATCH_BYTES: u64 = 16_777_216; // 16 MiB
#[allow(dead_code)]
pub const EXTERNAL_BYTES: u64 = 8_388_608; // 8 MiB

/// Free space that must remain after each class of reservation.
pub const ORDINARY_FLOOR: u64 = 67_108_864; // control, maintenance, scratch and external
pub const PROTOCOL_FLOOR: u64 = 33_554_432; // maintenance, scratch and external
pub const MAINTENANCE_FLOOR: u64 = 58_720_256; // control, scratch and external
pub const COVERED_FLOOR: u64 = 41_943_040; // control and external
pub const SCRATCH_FLOOR: u64 = 50_331_648; // control, maintenance and external

/// Replication transport limits for one receiving keeper.
pub const RECEIVER_BYTES: usize = 268_435_456; // 256 MiB
pub const SENDER_BYTES: usize = 100_663_296; // 96 MiB
pub const RECEIVER_FRAMES: usize = 16;
pub const SENDER_FRAMES: usize = 4;
/// Each body is charged for its encoding, decoding and handoff copies.
pub const BODY_COPIES: usize = 4;
pub const BODY_OVERHEAD: usize = 65_536;

/// Control work limits for one receiving keeper.
pub const MAX_CONTROL_WORK: usize = 24;
pub const CONTROL_PER_SENDER: usize = 4;

/// Durable WAL lanes served in rotation.
pub const LANES: usize = 5;

/// What a decoded Raft entry carries.
pub(super) enum EntryKind {
    Blank,
    Membership,
    Staging,
    Application,
}

/// The decoded kind of a peer request.
pub(super) enum PeerKind {
    Vote,
    Append,
    Snapshot,
}

/// The peer lane a decoded request belongs to.
pub(super) enum PeerLane {
    Control,
    Replication,
    Bulk,
}

/// How a sender handles an AppendEntries batch for its lane.
pub(super) enum AppendFit {
    Fits,
    /// Ask OpenRaft to resend with at most this many entries.
    Split(usize),
    Unfit,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == exists|i: int| 0 <= i < kinds@.len()
        && #[trigger] kinds@[i] is Application
))]
pub(super) fn carries_application(kinds: &[EntryKind]) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= kinds@.len(),
            forall|i: int| 0 <= i < index ==> !(#[trigger] kinds@[i] is Application),
        decreases kinds@.len() - index,
    ))]
    while index < kinds.len() {
        if let EntryKind::Application = kinds[index] {
            return true;
        }
        index += 1;
    }
    false
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (kind is Snapshot) ==> (out is Bulk),
        (kind is Vote) ==> (out is Control),
        (kind is Append) ==> (if application { out is Replication } else { out is Control }),
))]
pub(super) fn peer_lane(kind: PeerKind, application: bool) -> PeerLane {
    match kind {
        PeerKind::Snapshot => PeerLane::Bulk,
        PeerKind::Vote => PeerLane::Control,
        PeerKind::Append => {
            if application {
                PeerLane::Replication
            } else {
                PeerLane::Control
            }
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out as int == if size as int * BODY_COPIES as int + BODY_OVERHEAD as int > usize::MAX as int {
        usize::MAX as int
    } else {
        size as int * BODY_COPIES as int + BODY_OVERHEAD as int
    }
))]
pub(super) fn body_charge(size: usize) -> usize {
    if size > (usize::MAX - BODY_OVERHEAD) / BODY_COPIES {
        usize::MAX
    } else {
        size * BODY_COPIES + BODY_OVERHEAD
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (total_frames < RECEIVER_FRAMES
        && total_bytes as int + charge as int <= RECEIVER_BYTES as int
        && sender_frames < SENDER_FRAMES
        && sender_bytes as int + charge as int <= SENDER_BYTES as int)
))]
pub(super) fn admits_body(
    total_frames: usize,
    total_bytes: usize,
    sender_frames: usize,
    sender_bytes: usize,
    charge: usize,
) -> bool {
    total_frames < RECEIVER_FRAMES
        && total_bytes <= RECEIVER_BYTES
        && charge <= RECEIVER_BYTES - total_bytes
        && sender_frames < SENDER_FRAMES
        && sender_bytes <= SENDER_BYTES
        && charge <= SENDER_BYTES - sender_bytes
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (total < MAX_CONTROL_WORK && sender < CONTROL_PER_SENDER)
))]
pub(super) fn admits_control(total: usize, sender: usize) -> bool {
    total < MAX_CONTROL_WORK && sender < CONTROL_PER_SENDER
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (pending as int + bytes as int + floor as int <= measured as int)
))]
pub(super) fn fits(measured: u64, pending: u64, bytes: u64, floor: u64) -> bool {
    pending <= measured && bytes <= measured - pending && floor <= measured - pending - bytes
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (new == 0 || occupied as int + new as int + slots as int <= limit as int)
))]
pub(super) fn suffix_admits(occupied: usize, new: usize, slots: usize, limit: usize) -> bool {
    new == 0 || (occupied <= limit && new <= limit - occupied && slots <= limit - occupied - new)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires next < LANES, step < LANES,
    ensures out == (next + step) % (LANES as int),
))]
pub(super) fn probe(next: usize, step: usize) -> usize {
    (next + step) % LANES
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires lane < LANES,
    ensures out == (lane + 1) % (LANES as int),
))]
pub(super) fn after(lane: usize) -> usize {
    (lane + 1) % LANES
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Fits) == (size <= limit && count <= max_entries),
        match out {
            AppendFit::Split(hint) => count > 1 && hint == count / 2 && 1 <= hint && hint < count,
            _ => true,
        },
        (out is Unfit) ==> !(size <= limit && count <= max_entries) && count <= 1,
))]
pub(super) fn fit_append(size: u64, limit: u64, count: usize, max_entries: usize) -> AppendFit {
    if size <= limit && count <= max_entries {
        AppendFit::Fits
    } else if count > 1 {
        AppendFit::Split(count / 2)
    } else {
        AppendFit::Unfit
    }
}

/// Whether startup must present the stored vote as uncommitted. A keeper
/// that led a term must not resume that term's leadership.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (committed && voted_for_self)
))]
pub(super) fn demotes_vote(committed: bool, voted_for_self: bool) -> bool {
    committed && voted_for_self
}

#[cfg(verus_keep_ghost)]
verus! {
    /// The limit relations the laws rely on.
    pub proof fn limits()
        ensures
            CONTROL_BYTES + PROTOCOL_FLOOR <= ORDINARY_FLOOR,
            MAINTENANCE_BYTES + MAINTENANCE_FLOOR <= ORDINARY_FLOOR,
            MAINTENANCE_BYTES + COVERED_FLOOR <= ORDINARY_FLOOR,
            SCRATCH_BYTES + SCRATCH_FLOOR <= ORDINARY_FLOOR,
            SENDER_BYTES < RECEIVER_BYTES,
            RECEIVER_BYTES - SENDER_BYTES == 167_772_160,
            SENDER_FRAMES < RECEIVER_FRAMES,
            CONTROL_PER_SENDER < MAX_CONTROL_WORK,
            MAX_CONTROL_WORK - CONTROL_PER_SENDER == 20,
            LANES == 5,
            BODY_COPIES == 4,
            BODY_OVERHEAD == 65_536,
    {
    }

    /// The first index the peer batch must start at.
    pub(super) open spec fn first_index(previous: Option<(u64, u64)>) -> int {
        match previous {
            Some(id) => id.0 as int + 1,
            None => 0,
        }
    }

    /// A consecutive batch: indices follow the previous entry, terms never
    /// decrease and never exceed the sender's vote term.
    pub(super) open spec fn consecutive(
        previous: Option<(u64, u64)>, ids: Seq<(u64, u64)>, vote_term: u64,
    ) -> bool {
        &&& forall|i: int| 0 <= i < ids.len() ==> (#[trigger] ids[i]).0 as int == first_index(previous) + i
        &&& forall|i: int| 0 <= i < ids.len() ==> (#[trigger] ids[i]).1 <= vote_term
        &&& forall|i: int| 0 < i < ids.len() ==> ids[i - 1].1 <= (#[trigger] ids[i]).1
        &&& (ids.len() > 0 && previous is Some) ==> previous->Some_0.1 <= ids[0].1
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == forall|i: int| 0 <= i < ids@.len()
        ==> (#[trigger] ids@[i]).0 as int == first_index(previous) + i
))]
pub(super) fn indices_follow(previous: Option<(u64, u64)>, ids: &[(u64, u64)]) -> bool {
    // A wider counter makes an index past `u64::MAX` unequal to every entry.
    let mut expected: u128 = match previous {
        Some((index, _)) => index as u128 + 1,
        None => 0,
    };
    let mut position = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            position <= ids@.len(),
            expected as int == first_index(previous) + position,
            forall|i: int| 0 <= i < position
                ==> (#[trigger] ids@[i]).0 as int == first_index(previous) + i,
        decreases ids@.len() - position,
    ))]
    while position < ids.len() {
        if ids[position].0 as u128 != expected {
            return false;
        }
        expected += 1;
        position += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (
        (forall|i: int| 0 <= i < ids@.len() ==> (#[trigger] ids@[i]).1 <= vote_term)
        && (forall|i: int| 0 < i < ids@.len() ==> ids@[i - 1].1 <= (#[trigger] ids@[i]).1)
        && ((ids@.len() > 0 && previous is Some) ==> previous->Some_0.1 <= ids@[0].1))
))]
pub(super) fn terms_ordered(
    previous: Option<(u64, u64)>,
    ids: &[(u64, u64)],
    vote_term: u64,
) -> bool {
    let mut position = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            position <= ids@.len(),
            forall|i: int| 0 <= i < position ==> (#[trigger] ids@[i]).1 <= vote_term,
            forall|i: int| 0 < i < position ==> ids@[i - 1].1 <= (#[trigger] ids@[i]).1,
            (position > 0 && previous is Some) ==> previous->Some_0.1 <= ids@[0].1,
        decreases ids@.len() - position,
    ))]
    while position < ids.len() {
        let term = ids[position].1;
        if term > vote_term {
            return false;
        }
        let floor = if position > 0 {
            ids[position - 1].1
        } else {
            match previous {
                Some((_, previous_term)) => previous_term,
                None => 0,
            }
        };
        if term < floor {
            return false;
        }
        position += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == consecutive(previous, ids@, vote_term)
))]
pub(super) fn consecutive_cut(
    previous: Option<(u64, u64)>,
    ids: &[(u64, u64)],
    vote_term: u64,
) -> bool {
    indices_follow(previous, ids) && terms_ordered(previous, ids, vote_term)
}
