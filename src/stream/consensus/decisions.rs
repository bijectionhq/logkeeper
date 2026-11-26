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

/// Whether an ordinary move's stage replaces the copy another ordinary move
/// staged on this keeper at the same revision, from the same source
/// configuration. The caller holds the authority's committed placement
/// proof that names the new stage at that source with no joint
/// configuration, so the other move's joint configuration can never commit
/// and nothing the copy acknowledged under it can count toward a quorum. The
/// stream's durable vote is kept across generations, so the restage loses no
/// vote. A recovery stage on either side stays refused: it may belong to
/// another survivor of a split history.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!staged_recovery && !stage_recovery && same_source && !same_stage)
))]
pub(super) fn restages_replacement(
    staged_recovery: bool,
    stage_recovery: bool,
    same_source: bool,
    same_stage: bool,
) -> bool {
    !staged_recovery && !stage_recovery && same_source && !same_stage
}

/// Whether a copy's applied pages may be served to a reader. A voter of its
/// applied membership serves them only once this keeper process certified
/// its placement (`keeper/certify.rs`): an operator recovery may have left
/// the copy's applied suffix behind, and a lost voter that restarted with a
/// snapshot holds that suffix before anything tells it so.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (member && certified)
))]
pub(super) fn serves_reads(member: bool, certified: bool) -> bool {
    member && certified
}

/// Whether the catalog's latest staged move fences a copy whose effective
/// configuration is described by the flags. An ordinary move leaves both of
/// its sides and its joint configuration alone: any older configuration
/// belongs to a copy that missed a committed move. A recovery goes on only
/// from its target, so its lost configuration is fenced. A copy without a
/// configuration cannot campaign or serve, and is never fenced.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (configured && (if recovery { !at_target } else {
        !(at_old || at_target || joint_of_move)
    }))
))]
pub(super) fn fences_copy(
    configured: bool,
    recovery: bool,
    at_old: bool,
    at_target: bool,
    joint_of_move: bool,
) -> bool {
    configured
        && if recovery {
            !at_target
        } else {
            !(at_old || at_target || joint_of_move)
        }
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

/// Whether a keeper triggers automatic voter repair. A keeper that answered
/// with a protocol version mismatch is alive on another version and must
/// never trigger mass repair.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!version_mismatch && silent_ms >= repair_after_ms)
))]
pub(super) fn triggers_repair(
    silent_ms: u64,
    repair_after_ms: u64,
    version_mismatch: bool,
) -> bool {
    !version_mismatch && keeper_dead(silent_ms, repair_after_ms)
}

/// Whether the finalized cluster feature level allows writing a format or
/// command that requires `required`. New binaries keep writing old formats
/// until the cluster finalizes at least `required`, so rollback stays safe.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (finalized >= required)
))]
pub(super) fn write_version_allows(finalized: u32, required: u32) -> bool {
    finalized >= required
}

/// Whether a peer advertising `peer_features` supports every feature bit in
/// `required`.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == ((peer_features & required) == required)
))]
pub(super) fn peer_supports(peer_features: u64, required: u64) -> bool {
    (peer_features & required) == required
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

/// Whether two optional log indices name the same position.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (a == b)
))]
pub(super) fn same_index(a: Option<u64>, b: Option<u64>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        (None, None) => true,
        _ => false,
    }
}

/// Whether a replica's group is idle enough to park, apart from the
/// replicated catalog, which never parks: it served no client and grew no
/// log for the park delay, it applied its whole log, its membership is
/// uniform, and it receives no snapshot.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (quiet_log_ns >= park_after_ns && unused_ns >= park_after_ns
        && applied == last_log && uniform && !receiving)
))]
pub(super) fn idle(
    quiet_log_ns: u128,
    unused_ns: u128,
    park_after_ns: u128,
    applied: Option<u64>,
    last_log: Option<u64>,
    uniform: bool,
    receiving: bool,
) -> bool {
    quiet_log_ns >= park_after_ns
        && unused_ns >= park_after_ns
        && same_index(applied, last_log)
        && uniform
        && !receiving
}

/// Whether a leader asks its followers to park: it leads, it applied its
/// whole log and every live voter matched it, and it is idle itself.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (leader && settled && idle)
))]
pub(super) fn leader_parks(leader: bool, settled: bool, idle: bool) -> bool {
    leader && settled && idle
}

/// Whether a follower parks at a leader's request: it follows under the
/// leader's vote, it applied exactly the leader's applied log and holds no
/// entry past it, and it is idle itself.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (follower && same_vote && same_applied && last_log == leader_applied && idle)
))]
pub(super) fn accepts_park(
    follower: bool,
    same_vote: bool,
    same_applied: bool,
    last_log: Option<u64>,
    leader_applied: Option<u64>,
    idle: bool,
) -> bool {
    follower && same_vote && same_applied && same_index(last_log, leader_applied) && idle
}

/// A peer request that reaches a parked replica.
pub(super) enum ParkedRequest {
    /// An AppendEntries with no entries.
    Heartbeat,
    /// A repeated park request.
    Park,
    /// Entries, a vote, a pre-vote, a snapshot or a leader transfer.
    Other,
}

/// How a parked replica handles a peer request.
pub(super) enum ParkedAnswer {
    /// Answer busy without opening the group.
    Busy,
    /// Confirm the park without opening the group.
    Parked,
    /// Reopen the group and serve the request.
    Reopen,
}

/// A parked replica answers an empty heartbeat busy only within
/// `heartbeat_window_ns` of parking: heartbeats that go on past the park
/// round come from a leader that stayed open because another follower
/// declined, so they reopen the group.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Busy) == (request is Heartbeat && parked_ns < heartbeat_window_ns),
        (out is Parked) == (request is Park),
        (out is Reopen) == (request is Other
            || (request is Heartbeat && parked_ns >= heartbeat_window_ns)),
))]
pub(super) fn parked_answer(
    request: ParkedRequest,
    parked_ns: u128,
    heartbeat_window_ns: u128,
) -> ParkedAnswer {
    match request {
        ParkedRequest::Heartbeat if parked_ns < heartbeat_window_ns => ParkedAnswer::Busy,
        ParkedRequest::Park => ParkedAnswer::Parked,
        _ => ParkedAnswer::Reopen,
    }
}

/// Whether a leader counts a voter silent: its keeper is dead, or it has
/// not acknowledged this leader for the repair delay, measured from this
/// leader's term when it never acknowledged.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (dead || match acked_ns {
        Some(acked) => acked >= repair_after_ns,
        None => led_ns >= repair_after_ns,
    })
))]
pub(super) fn silent(
    dead: bool,
    acked_ns: Option<u128>,
    led_ns: u128,
    repair_after_ns: u128,
) -> bool {
    dead || match acked_ns {
        Some(acked) => acked >= repair_after_ns,
        None => led_ns >= repair_after_ns,
    }
}

/// Whether a learner the leader has seen for `seen_ns` belongs to an
/// aborted replacement.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (seen_ns >= stale_ns)
))]
pub(super) fn learner_stale(seen_ns: u128, stale_ns: u128) -> bool {
    seen_ns >= stale_ns
}

/// The order in which a repair pass starts queued work: higher priority
/// (lower rank) first; within one rank, the streams after the one the
/// last pass started last, then the rest, each in stream order.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out.0 == rank,
        out.1 == (cursor matches Some(last) && stream <= last),
        out.2 == stream,
))]
pub(super) fn repair_key(rank: u8, stream: u128, cursor: Option<u128>) -> (u8, bool, u128) {
    let wrapped = match cursor {
        Some(last) => stream <= last,
        None => false,
    };
    (rank, wrapped, stream)
}

/// What a repair pass does with the next queued stream.
pub(super) enum RepairStart {
    Start,
    /// The stream already repairs or waits out its backoff.
    Skip,
    /// Every repair slot is taken.
    Full,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Full) == (running >= max_repairs),
        (out is Start) == (running < max_repairs && !repairing && !backed_off),
))]
pub(super) fn starts_repair(
    running: usize,
    max_repairs: usize,
    repairing: bool,
    backed_off: bool,
) -> RepairStart {
    if running >= max_repairs {
        RepairStart::Full
    } else if repairing || backed_off {
        RepairStart::Skip
    } else {
        RepairStart::Start
    }
}

/// Whether a voter roster may move: a membership change needs a quorum,
/// so at least two of the three current voters must be live.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (live >= 2)
))]
pub(super) fn repair_allowed(live: usize) -> bool {
    live >= 2
}

/// The stream count above which an eligible keeper takes no new voter:
/// a quarter above the rounded-up average of the `count` known keepers,
/// and at least one above it. `None` when no load is known.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        count == 0 ==> out is None,
        count > 0 ==> (out matches Some(ceiling)
            && ceiling as int == ceiling_of(rounded_average(sum as int, count as int))),
))]
pub(super) fn load_ceiling(sum: u64, count: u64) -> Option<u32> {
    if count == 0 {
        return None;
    }
    // The quotient is below `u64::MAX` whenever a remainder is left.
    let quotient = sum / count;
    let average = if sum % count != 0 && quotient < u64::MAX {
        quotient + 1
    } else {
        quotient
    };
    let bump = if average / 4 > 1 { average / 4 } else { 1 };
    let ceiling = if average > u64::MAX - bump {
        u64::MAX
    } else {
        average + bump
    };
    Some(if ceiling > u32::MAX as u64 {
        u32::MAX
    } else {
        ceiling as u32
    })
}

/// Whether a keeper with `streams` open groups is under the load ceiling.
/// A keeper of unknown load, or a view with no known load, counts as roomy.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match (ceiling, streams) {
        (Some(ceiling), Some(streams)) => streams <= ceiling,
        _ => true,
    }
))]
pub(super) fn roomy(ceiling: Option<u32>, streams: Option<u32>) -> bool {
    match (ceiling, streams) {
        (Some(ceiling), Some(streams)) => streams <= ceiling,
        _ => true,
    }
}

/// Whether a leader hands leadership to a writer's preferred voter: it is
/// another voter, it matched the leader's whole log, and no handoff
/// reached or left this group within the hold-down.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!to_self && matched is Some && matched == last && !recent)
))]
pub(super) fn hands_off(
    to_self: bool,
    matched: Option<u64>,
    last: Option<u64>,
    recent: bool,
) -> bool {
    !to_self && matched.is_some() && same_index(matched, last) && !recent
}

/// Whether a replica looks for a placement proof that would retire its
/// copy: a peer refused it as outside its placement, or it does not lead
/// and has heard from no leader for the repair delay.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (excluded || (!leader && unheard_ns >= repair_after_ns))
))]
pub(super) fn orphaned(
    excluded: bool,
    leader: bool,
    unheard_ns: u128,
    repair_after_ns: u128,
) -> bool {
    excluded || (!leader && unheard_ns >= repair_after_ns)
}

/// Whether a voter refuses to vote in a stream because another keeper
/// certified a newer configuration that names it neither as a voter nor as
/// the target of a joint change. A voter lost to an operator recovery, or
/// replaced while it was down, holds an older configuration; with another
/// such voter it would still form a quorum of that configuration, so it
/// takes part in no election until it has checked.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (proof_revision > local_revision && !named_voter && !named_joint)
))]
pub(super) fn refuses_stale_vote(
    local_revision: u64,
    proof_revision: u64,
    named_voter: bool,
    named_joint: bool,
) -> bool {
    proof_revision > local_revision && !named_voter && !named_joint
}

/// Whether a certified placement proof retires this keeper's copy: the
/// proof is of the revision the copy was asked to leave, and neither its
/// configuration nor the target of its joint change names this keeper.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (same_revision && !named_voter && !named_joint)
))]
pub(super) fn certifies_exclusion(
    same_revision: bool,
    named_voter: bool,
    named_joint: bool,
) -> bool {
    same_revision && !named_voter && !named_joint
}

/// How the stream state machine decides a seal.
pub(super) enum SealStep {
    /// An unacknowledged operator recovery fences the stream.
    Recovered,
    /// The next epoch would overflow.
    Unavailable,
    /// Install a new fence at this epoch.
    Install(u64),
    /// Only the writer already holding a fence at this epoch may repeat it.
    Repeat(u64),
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        recovering ==> out is Recovered,
        !recovering && expected == u64::MAX ==> out is Unavailable,
        out matches SealStep::Install(epoch) ==> !recovering && current == expected
            && epoch == expected + 1 && epoch > current,
        out matches SealStep::Repeat(epoch) ==> !recovering && current != expected
            && epoch == expected + 1,
        !recovering && expected < u64::MAX ==> (if current == expected {
            out is Install } else { out is Repeat }),
))]
pub(super) fn seal_step(recovering: bool, current: u64, expected: u64) -> SealStep {
    if recovering {
        SealStep::Recovered
    } else if expected == u64::MAX {
        SealStep::Unavailable
    } else if current == expected {
        SealStep::Install(expected + 1)
    } else {
        SealStep::Repeat(expected + 1)
    }
}

/// The boundary slot a restart trusts: the intact slot with the higher
/// sequence, 0 or 1, preferring the second on a tie. `None` when neither
/// slot is intact.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (first is None && second is None) <==> out is None,
        out matches Some(index) ==> index <= 1,
        out matches Some(0) ==> first matches Some(a)
            && (second matches Some(b) ==> a > b),
        out matches Some(1) ==> second matches Some(b)
            && (first matches Some(a) ==> a <= b),
))]
pub(super) fn newest_slot(first: Option<u64>, second: Option<u64>) -> Option<usize> {
    match (first, second) {
        (None, None) => None,
        (Some(_), None) => Some(0),
        (None, Some(_)) => Some(1),
        (Some(a), Some(b)) => Some(if a > b { 0 } else { 1 }),
    }
}

/// Whether a WAL checkpoint lies within the trusted boundary: at or before
/// it, and neither inside a segment header.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == ((checkpoint_segment < boundary_segment
            || (checkpoint_segment == boundary_segment && checkpoint_offset <= boundary_offset))
        && checkpoint_offset >= header && boundary_offset >= header)
))]
pub(super) fn checkpoint_within(
    checkpoint_segment: u64,
    checkpoint_offset: u64,
    boundary_segment: u64,
    boundary_offset: u64,
    header: u64,
) -> bool {
    (checkpoint_segment < boundary_segment
        || (checkpoint_segment == boundary_segment && checkpoint_offset <= boundary_offset))
        && checkpoint_offset >= header
        && boundary_offset >= header
}

/// What WAL replay finds at its offset in a segment.
pub(super) enum FrameRead {
    /// A whole frame whose end is at `next`.
    Complete,
    /// Clean end of the segment's frames.
    End,
    /// A short or damaged frame.
    Torn,
}

/// What WAL replay does with a frame. `end` is the trusted boundary offset
/// in the boundary's own segment, and `None` in an earlier segment.
pub(super) enum ReplayStep {
    Apply,
    /// The segment ended cleanly before the boundary's segment.
    Finish,
    /// The boundary falls inside this frame.
    Split,
    /// The data volume lost frames the boundary acknowledged.
    Lost,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out is Apply ==> frame is Complete && (end matches Some(end) ==> next <= end),
        out is Finish ==> frame is End && end is None,
        out is Split ==> frame is Complete && (end matches Some(end) && next > end),
        out is Lost ==> !(frame is Complete) && !(frame is End && end is None),
        frame is Complete ==> (out is Apply || out is Split),
))]
pub(super) fn replay_step(frame: FrameRead, next: u64, end: Option<u64>) -> ReplayStep {
    match frame {
        FrameRead::Complete => match end {
            Some(end) if next > end => ReplayStep::Split,
            _ => ReplayStep::Apply,
        },
        FrameRead::End => match end {
            None => ReplayStep::Finish,
            Some(_) => ReplayStep::Lost,
        },
        FrameRead::Torn => ReplayStep::Lost,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    /// A quarter above `average`, at least one above it, capped at
    /// `u32::MAX`.
    pub(super) open spec fn rounded_average(sum: int, count: int) -> int {
        if sum % count != 0 && sum / count < u64::MAX as int { sum / count + 1 } else { sum / count }
    }

    pub(super) open spec fn ceiling_of(average: int) -> int {
        let bump = if average / 4 > 1 { average / 4 } else { 1 };
        if average + bump > u32::MAX as int { u32::MAX as int } else { average + bump }
    }
}
