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
pub const SCRATCH_BYTES: u64 = 41_943_040; // 40 MiB
#[allow(dead_code)]
pub const EXTERNAL_BYTES: u64 = 8_388_608; // 8 MiB

/// Free space that must remain after each class of reservation.
pub const ORDINARY_FLOOR: u64 = 92_274_688; // control, maintenance, scratch and external
pub const PROTOCOL_FLOOR: u64 = 58_720_256; // maintenance, scratch and external
pub const MAINTENANCE_FLOOR: u64 = 83_886_080; // control, scratch and external
pub const COVERED_FLOOR: u64 = 41_943_040; // control and external
pub const SCRATCH_FLOOR: u64 = 50_331_648; // control, maintenance and external

/// Replication transport limits for one receiving keeper. A frame is one
/// peer message in flight, whichever connection or batch carried it.
pub const RECEIVER_BYTES: usize = 268_435_456; // 256 MiB
pub const SENDER_BYTES: usize = 100_663_296; // 96 MiB
pub const RECEIVER_FRAMES: usize = 384;
pub const SENDER_FRAMES: usize = 128;
/// Each body is charged for its encoding, decoding and handoff copies.
pub const BODY_COPIES: usize = 4;
pub const BODY_OVERHEAD: usize = 65_536;

/// Control work limits for one receiving keeper, in peer messages.
pub const MAX_CONTROL_WORK: usize = 384;
pub const CONTROL_PER_SENDER: usize = 128;

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

/// A meter after it admits one message charged `charge` bytes.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires frames < usize::MAX, bytes as int + charge as int <= usize::MAX as int,
    ensures out.0 as int == frames as int + 1, out.1 as int == bytes as int + charge as int,
))]
pub(super) fn meter_admit(frames: usize, bytes: usize, charge: usize) -> (usize, usize) {
    (frames + 1, bytes + charge)
}

/// A meter after it releases one message charged `charge` bytes.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires 0 < frames, charge <= bytes,
    ensures out.0 as int == frames as int - 1, out.1 as int == bytes as int - charge as int,
))]
pub(super) fn meter_release(frames: usize, bytes: usize, charge: usize) -> (usize, usize) {
    (frames - 1, bytes - charge)
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

/// Whether an operator may recover a stream from its surviving voter. The
/// survivor must still vote in its stream's latest configuration, the
/// operator must acknowledge the data loss, and no other voter of that
/// configuration may answer with a healthy replica: together with the
/// survivor it would form a quorum that can still commit.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (acknowledged && survivor_votes && healthy_others == 0)
))]
pub(super) fn allows_recovery(
    acknowledged: bool,
    survivor_votes: bool,
    healthy_others: u64,
) -> bool {
    acknowledged && survivor_votes && healthy_others == 0
}

/// How far a recovery term jumps past the survivor's highest term. The lost
/// voters may have reached terms the survivor never saw; with pre-vote they
/// would need billions more elections than it saw to reach this one.
pub const RECOVERY_TERM_GAP: u64 = 4_294_967_296; // 2^32

/// Whether an operator recovery's stage replaces the recovery stage an
/// earlier attempt left on a replacement, at the same revision. A recovery
/// stages its replacements before the survivor writes anything, and a
/// survivor that wrote its recovery never stages again, so a copy staged by
/// an attempt from the same survivor, source revision and lost
/// configuration was never written to. Any other stage at that revision is
/// refused: it may come from another survivor of a split history.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (staged_recovery && retried_recovery && same_origin)
))]
pub(super) fn restages_recovery(
    staged_recovery: bool,
    retried_recovery: bool,
    same_origin: bool,
) -> bool {
    staged_recovery && retried_recovery && same_origin
}

/// The term of a recovery write: far above the survivor's vote and every
/// term in its log, so no ballot or entry of the lost history can outrank it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out matches Some(term) ==> term > vote_term && term > log_term
            && term as int >= vote_term as int + RECOVERY_TERM_GAP as int
            && term as int >= log_term as int + RECOVERY_TERM_GAP as int,
        out is None ==> vote_term as int + RECOVERY_TERM_GAP as int > u64::MAX as int
            || log_term as int + RECOVERY_TERM_GAP as int > u64::MAX as int,
))]
pub(super) fn recovery_term(vote_term: u64, log_term: u64) -> Option<u64> {
    let highest = if vote_term > log_term {
        vote_term
    } else {
        log_term
    };
    if highest > u64::MAX - RECOVERY_TERM_GAP {
        None
    } else {
        Some(highest + RECOVERY_TERM_GAP)
    }
}

/// The epoch of the recovery fence: above every epoch the survivor applied.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out matches Some(epoch) ==> epoch > current,
        out is None ==> current == u64::MAX,
))]
pub(super) fn recovery_epoch(current: u64) -> Option<u64> {
    if current == u64::MAX {
        None
    } else {
        Some(current + 1)
    }
}

/// Whether a replica refuses a peer's vote or append without answering it:
/// the sender is outside the replica's effective membership and campaigns
/// or leads in a term below the replica's vote. It belongs to a history
/// this replica superseded, such as a voter an operator recovery lost, and
/// an answer would teach it the newer term. The refusal tells the sender to
/// check whether it was removed.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (configured && !known && sender_term < own_term)
))]
pub(super) fn excludes_sender(
    configured: bool,
    known: bool,
    sender_term: u64,
    own_term: u64,
) -> bool {
    configured && !known && sender_term < own_term
}

/// Whether a replica answers vote-class requests. An installed replica
/// votes in its effective configuration, and before it holds one only as a
/// genesis voter. A replacement an operator recovery installed also votes
/// until it holds the recovered membership, which names it: `recovering`
/// holds while its configuration is absent or still the lost one.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (installed && (recovering || if configured { member } else { genesis_voter }))
))]
pub(super) fn votes(
    installed: bool,
    configured: bool,
    member: bool,
    genesis_voter: bool,
    recovering: bool,
) -> bool {
    installed && (recovering || if configured { member } else { genesis_voter })
}

/// Whether a peer's media incarnation shows its keeper ID reused: this
/// keeper first saw the peer under another incarnation. The first contact
/// records the incarnation and is never a reuse.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        recorded is None ==> !out,
        recorded matches Some(first) ==> out == (first != reported),
))]
pub(super) fn reincarnated(recorded: Option<u128>, reported: u128) -> bool {
    match recorded {
        Some(first) => first != reported,
        None => false,
    }
}

/// Whether a keeper registers a replica it does not hold because a peer or
/// a bootstrap named it. Only a genesis voter does, only once a peer
/// confirmed its identity, and never once a peer knows it under another
/// incarnation: its media was installed again under its old ID, and an
/// empty replica would vote as if it had never acknowledged anything.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (genesis_voter && confirmed && !reused)
))]
pub(super) fn registers(genesis_voter: bool, confirmed: bool, reused: bool) -> bool {
    genesis_voter && confirmed && !reused
}

/// Whether a campaign counts a peer's vote or pre-vote grant: never one
/// from a peer this keeper saw under another incarnation.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (granted && !reincarnated)
))]
pub(super) fn counts_grant(granted: bool, reincarnated: bool) -> bool {
    granted && !reincarnated
}

/// Whether a keeper's media keeps up: its current WAL round, `running_ms`
/// long or zero when none runs, is within `soft_ms`, and the hold after the
/// last slow round has passed. A keeper whose media does not keep up hands
/// off the streams it leads, refuses votes and accepts no streams.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (running_ms <= soft_ms && now_ms >= slow_until_ms)
))]
pub(super) fn media_responsive(
    running_ms: u64,
    slow_until_ms: u64,
    now_ms: u64,
    soft_ms: u64,
) -> bool {
    running_ms <= soft_ms && now_ms >= slow_until_ms
}

/// Whether a keeper silent for `silent_ms` is dead: it has not answered a
/// liveness ping for the repair delay. Repair replaces a dead keeper's
/// voters, parked streams that name it wake, and parking no longer waits
/// for it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (silent_ms >= repair_after_ms)
))]
pub(super) fn keeper_dead(silent_ms: u64, repair_after_ms: u64) -> bool {
    silent_ms >= repair_after_ms
}

/// The wait after `failures` failed attempts: `base_ms` doubled once per
/// failure, never above `cap_ms`. Repair and the wake sweep use it so that
/// one stream that keeps failing yields to the others.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out as int == grown(if base_ms < cap_ms { base_ms as int } else { cap_ms as int },
        cap_ms as int, failures as nat)
))]
pub(super) fn backoff(failures: u32, base_ms: u64, cap_ms: u64) -> u64 {
    let mut wait = if base_ms < cap_ms { base_ms } else { cap_ms };
    let mut step = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            step <= failures,
            wait <= cap_ms,
            grown(wait as int, cap_ms as int, (failures - step) as nat)
                == grown(if base_ms < cap_ms { base_ms as int } else { cap_ms as int },
                    cap_ms as int, failures as nat),
        decreases failures - step,
    ))]
    while step < failures && wait < cap_ms {
        wait = if wait > cap_ms - wait {
            cap_ms
        } else {
            wait * 2
        };
        step += 1;
    }
    wait
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
            RECEIVER_FRAMES - SENDER_FRAMES == 256,
            CONTROL_PER_SENDER < MAX_CONTROL_WORK,
            MAX_CONTROL_WORK - CONTROL_PER_SENDER == 256,
            LANES == 5,
            BODY_COPIES == 4,
            BODY_OVERHEAD == 65_536,
    {
    }

    /// `wait` doubled `n` times, never above `cap`.
    pub(super) open spec fn grown(wait: int, cap: int, n: nat) -> int
        decreases n,
    {
        if wait >= cap {
            cap
        } else if n == 0 {
            wait
        } else {
            grown(if 2 * wait > cap { cap } else { 2 * wait }, cap, (n - 1) as nat)
        }
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
