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

/// Whether an operator may recover a stream of `voters` voters from a
/// surviving voter. The survivor must still vote in its stream's latest
/// configuration, the operator must acknowledge the data loss, and the
/// other voters of that configuration that answer with a healthy replica
/// must not form a quorum with the survivor, which could still commit:
/// none of three, at most one other of five.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (acknowledged && survivor_votes && (voters == 3 || voters == 5)
        && healthy_others + 1 < (voters / 2 + 1) as u64)
))]
pub(super) fn allows_recovery(
    acknowledged: bool,
    survivor_votes: bool,
    healthy_others: u64,
    voters: usize,
) -> bool {
    acknowledged
        && survivor_votes
        && replication_factor(voters)
        && healthy_others < quorum(voters) as u64 - 1
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

/// The offloaded prefix after a leader reports an upload through
/// `proposed`: it never moves back and never passes the applied head, so
/// it stays a prefix of the committed log.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out >= current,
        out <= head || out == current,
        out == current || out == proposed,
))]
pub(super) fn offloaded_through(current: u64, proposed: u64, head: u64) -> u64 {
    if proposed > current && proposed <= head {
        proposed
    } else {
        current
    }
}

/// The first record a keeper keeps after retention asks to drop records
/// below `requested`: only offloaded records, never past the head, and
/// the local floor never moves back.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out >= floor,
        out == floor || out as int <= offloaded as int + 1,
        out == floor || out as int <= head as int + 1,
        out == floor || out <= requested,
))]
pub(super) fn local_floor(floor: u64, requested: u64, offloaded: u64, head: u64) -> u64 {
    let mut cap = requested;
    if offloaded < u64::MAX && cap > offloaded + 1 {
        cap = offloaded + 1;
    }
    if head < u64::MAX && cap > head + 1 {
        cap = head + 1;
    }
    if cap > floor { cap } else { floor }
}

/// The head an operator recovery keeps: everything at or below the larger
/// of the survivor's committed head and the end of the committed run the
/// offload store holds, exactly. `survivor` is the head of the survivor's
/// log through its commit index, never its uncommitted tail, which the lost
/// voters may have overwritten with other committed records (Lean
/// `OffloadPrefix.restore_exact`). Records above it that a writer was
/// acknowledged are lost.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out >= survivor,
        out >= uploaded,
        out == survivor || out == uploaded,
))]
pub(super) fn recovered_head(survivor: u64, uploaded: u64) -> u64 {
    if uploaded > survivor {
        uploaded
    } else {
        survivor
    }
}

/// The first log index an operator recovery writes its entries at, which
/// truncates every entry of the survivor's log from it. With `exact`, once
/// the cluster finalized leases and so writes commit indexes, it is right
/// after the survivor's durable commit index: an entry past it may be one
/// the lost voters overwrote. Before, the survivor does not know its commit
/// index and keeps its whole log. Never past the log.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out <= tip_next,
        exact ==> out <= committed_next,
        exact && committed_next <= tip_next ==> out == committed_next,
        !exact ==> out == tip_next,
))]
pub(super) fn recovery_cut(exact: bool, committed_next: u64, tip_next: u64) -> u64 {
    if exact && committed_next < tip_next {
        committed_next
    } else {
        tip_next
    }
}

/// The loss point an operator recovery reports and the catalog records:
/// every record at or below it is one the stream committed. With `exact`,
/// it is the head the recovery keeps. Without, the kept head may count
/// records the survivor never knew committed, so it is the head the
/// survivor knew committed, its snapshot or offloaded point, and records
/// between it and the kept head may differ from what writers were
/// acknowledged.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out <= kept,
        exact ==> out == kept,
        !exact ==> out == known || out == kept,
        !exact ==> out <= known,
))]
pub(super) fn reported_loss_point(exact: bool, kept: u64, known: u64) -> u64 {
    if exact || known > kept { kept } else { known }
}

/// Whether a leader refuses an append because offload fell too far behind.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (enforced && waiting > limit)
))]
pub(super) fn offload_backpressure(enforced: bool, waiting: u64, limit: u64) -> bool {
    enforced && waiting > limit
}

/// Whether a replica refuses a peer's vote, pre-vote, append, snapshot or
/// hand-off without answering it. Either an operator recovery this copy
/// holds fenced the sender (`recovery_excludes`), whatever its term and
/// even while the copy's own configuration still names it, or the sender is
/// outside the replica's effective membership and campaigns or leads in a
/// term below the replica's vote. Either way it belongs to a history this
/// replica superseded, and an answer would teach it the newer term. With
/// five voters and two survivors a lost leader may run terms past the
/// recovery's, so only its identity tells it apart; and the second
/// survivor, still in the configuration the recovery leaves, refuses the
/// lost voters from before the recovery reads its last entry. The refusal
/// tells the sender to check whether it was removed.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (recovery_fenced || (configured && !known && sender_term < own_term))
))]
pub(super) fn excludes_sender(
    configured: bool,
    known: bool,
    recovery_fenced: bool,
    sender_term: u64,
    own_term: u64,
) -> bool {
    recovery_fenced || (configured && !known && sender_term < own_term)
}

/// Whether a recovery's identity fence on a keeper still holds for a copy:
/// the keeper voted in the configuration the recovery left, the recovered
/// configuration does not name it, and no later ordinary move the copy
/// applied names it again (a staged move that targets it, or a finalized
/// revision above the recovery's).
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (fenced && !restaged && finalized_revision <= recovery_revision)
))]
pub(super) fn exclusion_holds(
    fenced: bool,
    restaged: bool,
    finalized_revision: u64,
    recovery_revision: u64,
) -> bool {
    fenced && !restaged && finalized_revision <= recovery_revision
}

/// Whether a copy that holds an operator recovery refuses a keeper by
/// identity: the keeper voted in the configuration the recovery left and
/// the recovered configuration does not name it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (in_old && !in_target)
))]
pub(super) fn recovery_excludes(in_old: bool, in_target: bool) -> bool {
    in_old && !in_target
}

/// Whether an operator recovery's catalog transaction fences its stream for
/// a keeper below the recovered revision: every voter of the configuration
/// it leaves, and every other survivor than the one that writes the
/// recovery. A survivor that keeps running through the wait-out may follow
/// a lost leader there, so its copy campaigns, leads and serves again only
/// once it finalized the recovered configuration from the writer. The
/// writer finalizes that configuration only by leading it, so it is never
/// fenced.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (in_old && !(in_target && writer))
))]
pub(super) fn recovery_fences(in_old: bool, in_target: bool, writer: bool) -> bool {
    in_old && !(in_target && writer)
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

/// Whether a lease configuration bounds clock drift: the drift margin is
/// positive and below half the lease, so the holder's validity, a lease less
/// the margin, stays positive and the recovery wait, a lease plus the
/// margin, stays longer than it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (0 < margin && margin < duration && margin < duration - margin)
))]
pub(super) fn lease_bounds(duration: u64, margin: u64) -> bool {
    0 < margin && margin < duration && margin < duration - margin
}

/// Whether a keeper's liveness lease is valid at `now`, all on the holder's
/// monotonic clock: it runs from the moment the holder sent the renewal the
/// authority granted, for the lease duration less the drift margin. So the
/// holder always counts its lease expired before the authority does. A
/// clock reading before the send time is not trusted: the lease is invalid.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (margin < duration && sent <= now
        && (now as int) < sent as int + duration as int - margin as int)
))]
pub(super) fn lease_valid(sent: u64, duration: u64, margin: u64, now: u64) -> bool {
    margin < duration && sent <= now && now - sent < duration - margin
}

/// Whether a keeper may campaign, lead or serve reads for a stream: its
/// liveness lease is valid, its epoch is the catalog's current one, and the
/// catalog does not fence its copy of the stream. Until the cluster
/// finalizes leases they are advisory, and the defences that predate them
/// stay authoritative.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!enforced || (lease_valid && epoch_current && !fenced))
))]
pub(super) fn holds_authority(
    enforced: bool,
    lease_valid: bool,
    epoch_current: bool,
    fenced: bool,
) -> bool {
    !enforced || (lease_valid && epoch_current && !fenced)
}

/// Whether the catalog fences a keeper's copy of a stream: the keeper's
/// liveness record fences the stream below configuration revision `below`,
/// and the copy has finalized an older one. A copy that finalized nothing
/// counts as revision 0. A copy that a later move placed on the keeper again
/// finalizes the newer revision and is not fenced.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (below matches Some(floor) && revision < floor)
))]
pub(super) fn copy_fenced(below: Option<u64>, revision: u64) -> bool {
    match below {
        Some(floor) => revision < floor,
        None => false,
    }
}

/// How long a recovered configuration waits after the catalog committed the
/// recovery before it serves: a whole lease plus the drift margin, so every
/// lease a lost keeper held when the recovery committed has ended on that
/// keeper's own clock, whether or not anyone can reach it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out matches Some(wait) ==> wait as int == duration as int + margin as int,
        out is None ==> duration as int + margin as int > u64::MAX as int,
))]
pub(super) fn recovery_wait(duration: u64, margin: u64) -> Option<u64> {
    if duration > u64::MAX - margin {
        None
    } else {
        Some(duration + margin)
    }
}

/// Whether the catalog grants a keeper's lease renewal: the media
/// incarnation it renews under is not one the keeper's record replaced, and
/// it asks under the record's current epoch, or under zero when a new
/// keeper process joins and adopts the current epoch.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!replaced && (requested == 0 || requested == current))
))]
pub(super) fn grants_lease(replaced: bool, requested: u64, current: u64) -> bool {
    !replaced && (requested == 0 || requested == current)
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
/// so a majority of the current voters must be live: two of three, or
/// three of five.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (live >= voters / 2 + 1)
))]
pub(super) fn repair_allowed(live: usize, voters: usize) -> bool {
    live >= voters / 2 + 1
}

/// Whether a stream may have `voters` voters: three or five.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (voters == 3 || voters == 5)
))]
pub(super) fn replication_factor(voters: usize) -> bool {
    voters == 3 || voters == 5
}

/// The votes that commit an entry, elect a leader or change the
/// membership of a roster of `voters`: a majority.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires voters < usize::MAX,
    ensures out == voters / 2 + 1, out * 2 > voters,
))]
pub(super) fn quorum(voters: usize) -> usize {
    voters / 2 + 1
}

/// Whether a roster of `voters` voters, of which at most `most_in_domain`
/// share a failure domain, is spread enough for a new stream or a move's
/// target: losing any one domain leaves a quorum. Three voters therefore
/// take three domains, and five voters at least three, at most two in any
/// one (2+2+1 over three domains, 2+1+1+1 over four, one each over five).
/// Placement prefers distinct domains whenever there are enough.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == ((voters == 3 || voters == 5) && most_in_domain >= 1
        && most_in_domain <= voters - (voters / 2 + 1))
))]
pub(super) fn spread_allows(voters: usize, most_in_domain: usize) -> bool {
    replication_factor(voters) && most_in_domain >= 1 && most_in_domain <= voters - quorum(voters)
}

/// Whether a create may give a stream `voters` voters. Three always works.
/// Five-voter rosters use a record layout older keepers cannot read, so
/// they need the finalized cluster version that every keeper reads.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (voters == 3 || (voters == 5 && finalized >= required))
))]
pub(super) fn creates_replication(voters: usize, finalized: u32, required: u32) -> bool {
    voters == 3 || (voters == 5 && write_version_allows(finalized, required))
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

/// Whether a client may seal as `writer`: never as the nil writer, and
/// never as the reserved writer of an operator recovery's fence, so no
/// client stands in that fence or writes as the recovery.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!nil && !reserved)
))]
pub(super) fn client_may_seal_as(nil: bool, reserved: bool) -> bool {
    !nil && !reserved
}

/// The command a retained record comes from.
pub(super) enum RecordOrigin {
    /// An append or an append batch of client bytes.
    Append,
    /// A timed original: its evidence, then client bytes.
    Timed,
    /// The opaque marker an acknowledgement below the typed entry's level
    /// writes, which is client bytes.
    Marker,
    /// `Command::RecoveryEntry`, the typed entry of a recorded recovery.
    RecoveryEntry,
}

/// What a retained record is (`state::RecordKind`).
pub(super) enum RetainedKind {
    Data,
    Timed,
    Recovery,
}

/// The kind a record from `origin` is retained as. Only the typed entry's
/// own command retains the recovery kind, so no append, batch, timed
/// record or marker of client bytes can forge one, whatever its bytes.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Recovery) == (origin is RecoveryEntry),
        (out is Timed) == (origin is Timed),
))]
pub(super) fn retained_kind(origin: RecordOrigin) -> RetainedKind {
    match origin {
        RecordOrigin::Append | RecordOrigin::Marker => RetainedKind::Data,
        RecordOrigin::Timed => RetainedKind::Timed,
        RecordOrigin::RecoveryEntry => RetainedKind::Recovery,
    }
}

/// How far typed recovery entries may take a stream past its byte quota.
/// A stream exactly at its quota must still take the one entry that clears
/// its recovery fence, or the fence never clears; ordinary records stay
/// within the quota, so only recovery entries, one per recovery, ever use
/// this headroom.
pub const RECOVERY_HEADROOM_BYTES: u64 = 65_536; // 64 KiB
/// How far typed recovery entries may take a stream past its retained
/// record limit, as `RECOVERY_HEADROOM_BYTES` for bytes.
pub const RECOVERY_HEADROOM_RECORDS: usize = 16;

/// Whether a stream holding `records` records that charge `bytes` retains
/// one more record charging `charge`. Ordinary records stay within
/// `max_records` and `quota`. A typed recovery entry (`entry`), which must
/// be written for the stream to make progress, may also use the recovery
/// headroom, and nothing more.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out ==> (records as int) < max_records as int
                + (if entry { RECOVERY_HEADROOM_RECORDS as int } else { 0 })
            && bytes as int + charge as int <= quota as int
                + (if entry { RECOVERY_HEADROOM_BYTES as int } else { 0 }),
        (records as int) < max_records as int
                + (if entry { RECOVERY_HEADROOM_RECORDS as int } else { 0 })
            && bytes as int + charge as int <= quota as int
                + (if entry { RECOVERY_HEADROOM_BYTES as int } else { 0 })
            && max_records as int + RECOVERY_HEADROOM_RECORDS as int <= usize::MAX as int
            && quota as int + RECOVERY_HEADROOM_BYTES as int <= u64::MAX as int ==> out,
        RECOVERY_HEADROOM_RECORDS == 16 && RECOVERY_HEADROOM_BYTES == 65_536,
))]
pub(super) fn retains_record(
    entry: bool,
    records: usize,
    max_records: usize,
    bytes: u64,
    charge: u64,
    quota: u64,
) -> bool {
    let (extra_records, extra_bytes) = if entry {
        (RECOVERY_HEADROOM_RECORDS, RECOVERY_HEADROOM_BYTES)
    } else {
        (0, 0)
    };
    let records_limit = if max_records > usize::MAX - extra_records {
        usize::MAX
    } else {
        max_records + extra_records
    };
    let bytes_limit = if quota > u64::MAX - extra_bytes {
        u64::MAX
    } else {
        quota + extra_bytes
    };
    records < records_limit && bytes <= bytes_limit && charge <= bytes_limit - bytes
}

/// How the stream state machine decides `Command::RecoveryEntry`.
pub(super) enum EntryStep {
    /// Write the entry at the position asked and clear the recorded fence.
    Write,
    /// The same entry is already retained there: return its position and
    /// change nothing.
    Retry,
    /// The position is below the retained floor.
    Trimmed,
    /// Refuse with `Conflict`.
    Conflict,
}

/// Decides a typed recovery entry for a fence of `fence_epoch` that kept
/// the records through `fence_head`, asked at `at`. `names_command` says
/// the entry's encoding names that fence and position; `pending` that a
/// recorded recovery's fence stands; `epoch` and `head` are the stream's;
/// `matches_record` says the entry carries that recorded recovery's
/// fields; `retained_identical` that a recovery record with exactly these
/// bytes is retained at `at`.
///
/// The entry is written only as the first entry of the recovery epoch,
/// right after the last record kept, while that recovery's fence stands
/// and with that recovery's fields, so it clears exactly that fence. Once
/// the fence is gone an identical retry returns the position and nothing
/// else is written.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out is Write <==> names_command && fence_head < u64::MAX && at == fence_head + 1
            && pending && epoch == fence_epoch && head == fence_head && matches_record,
        out is Retry <==> names_command && fence_head < u64::MAX && at == fence_head + 1
            && !pending && floor <= at && at <= head && retained_identical,
        out is Trimmed <==> names_command && fence_head < u64::MAX && at == fence_head + 1
            && !pending && at < floor,
))]
pub(super) fn recovery_entry_step(
    names_command: bool,
    fence_epoch: u64,
    fence_head: u64,
    at: u64,
    pending: bool,
    epoch: u64,
    head: u64,
    floor: u64,
    matches_record: bool,
    retained_identical: bool,
) -> EntryStep {
    if !names_command || fence_head == u64::MAX || at != fence_head + 1 {
        EntryStep::Conflict
    } else if !pending {
        if at < floor {
            EntryStep::Trimmed
        } else if at <= head && retained_identical {
            EntryStep::Retry
        } else {
            EntryStep::Conflict
        }
    } else if epoch == fence_epoch && head == fence_head && matches_record {
        EntryStep::Write
    } else {
        EntryStep::Conflict
    }
}

/// A stream's recovery summary after it also absorbs a recovery whose fence
/// is at `epoch` and which kept the records through `loss_point`: the
/// latest fence epoch and the lowest loss point of any recovery. `held`
/// says a summary exists, of `held_epoch` and `held_loss_point`.
///
/// These two numbers decide `written_step` for every recovery the stream
/// ever had (`summary_covers_every_erasing_recovery` in
/// JournalContract.lean), so they survive trims and snapshots where the
/// typed recovery entries do not.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        !held ==> out.0 == epoch && out.1 == loss_point,
        held ==> out.0 >= held_epoch && out.1 <= held_loss_point,
        out.0 >= epoch && out.1 <= loss_point,
        out.0 == epoch || (held && out.0 == held_epoch),
        out.1 == loss_point || (held && out.1 == held_loss_point),
))]
pub(super) fn absorb_recovery(
    held: bool,
    held_epoch: u64,
    held_loss_point: u64,
    epoch: u64,
    loss_point: u64,
) -> (u64, u64) {
    let latest = if held && held_epoch > epoch {
        held_epoch
    } else {
        epoch
    };
    let lowest = if held && held_loss_point < loss_point {
        held_loss_point
    } else {
        loss_point
    };
    (latest, lowest)
}

/// How the keeper answers `Request::Written` for an attempt of a writer of
/// `writer_epoch` whose last position is `last`.
pub(super) enum WrittenStep {
    /// Answer what the retained history says.
    Lookup,
    /// Answer `Recovered` with the summary's loss point: a recovery since
    /// the writer's epoch kept less than the attempt, so the attempt may
    /// have committed and been erased.
    Recovered,
    /// Answer `Unavailable` for the same case below
    /// `CLUSTER_VERSION_RETRY_RECOVERY`, whose summary is not yet durable.
    Unavailable,
}

/// Decides `Request::Written`. `missing` says the retained history alone
/// holds none of the attempt's records (the lookup's `Conflict`);
/// `summarized` that the stream knows a recovery summary of
/// `recovery_epoch`, the latest recovery's fence epoch, and `loss_point`,
/// the lowest loss point of any recovery; `durable` that the cluster
/// finalized the level that keeps the summary in snapshots.
///
/// Without a recovery since the writer's epoch the history the attempt ran
/// against is the retained one, so a miss is conclusive and the refusal of
/// the retry stands. A recovery fenced at an epoch above the writer's that
/// kept less than the attempt may have erased a committed attempt, so the
/// answer is never a definite refusal (`committed_attempt_retry_is_indefinite`
/// in JournalContract.lean).
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out is Lookup <==> !(missing && summarized && writer_epoch < recovery_epoch
            && loss_point < last),
        out is Recovered <==> missing && summarized && writer_epoch < recovery_epoch
            && loss_point < last && durable,
        out is Unavailable <==> missing && summarized && writer_epoch < recovery_epoch
            && loss_point < last && !durable,
))]
pub(super) fn written_step(
    missing: bool,
    summarized: bool,
    recovery_epoch: u64,
    loss_point: u64,
    writer_epoch: u64,
    last: u64,
    durable: bool,
) -> WrittenStep {
    if !missing || !summarized || writer_epoch >= recovery_epoch || loss_point >= last {
        WrittenStep::Lookup
    } else if durable {
        WrittenStep::Recovered
    } else {
        WrittenStep::Unavailable
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

/// Lease samples use zero for no grant and otherwise store the send sample plus one.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (encoded_sent > 0 && (now matches Some(sample) && margin < duration
        && (encoded_sent as int - 1) <= sample as int
        && (sample as int - (encoded_sent as int - 1)) < duration as int - margin as int)),
))]
pub(super) fn sampled_lease_valid(
    encoded_sent: u64,
    duration: u64,
    margin: u64,
    now: Option<u64>,
) -> bool {
    match now {
        Some(sample) if encoded_sent > 0 => lease_valid(encoded_sent - 1, duration, margin, sample),
        _ => false,
    }
}

/// Recovery waits on the slower of its two measured elapsed times. The
/// continuous sample is already in nanoseconds and bounds the result.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out as int == if continuous as int <= running as int {
        continuous as int
    } else {
        running as int
    },
))]
pub(super) fn recovery_elapsed(continuous: u64, running: u128) -> u64 {
    if (continuous as u128) <= running {
        continuous
    } else {
        running as u64
    }
}

/// Keep the maximum of each grant parameter, including across epoch bumps.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out >= prior && out >= granted && (out == prior || out == granted),
))]
pub(super) fn longest_grant(prior: u64, granted: u64) -> u64 {
    if prior > granted { prior } else { granted }
}

/// Include one fenced keeper's persisted lease bound in the wait-out.
/// The legacy reducer skips an unrepresentable sum.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out >= accumulated,
        (duration as int + margin as int <= u64::MAX) ==> (
            out as int >= duration as int + margin as int
            && (out == accumulated || out as int == duration as int + margin as int)
        ),
        (duration as int + margin as int > u64::MAX) ==> out == accumulated,
))]
pub(super) fn include_recovery_wait(accumulated: u64, duration: u64, margin: u64) -> u64 {
    match recovery_wait(duration, margin) {
        Some(wait) => longest_grant(accumulated, wait),
        None => accumulated,
    }
}

/// Apply offload progress only within the lineage that uploaded it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures (out is None) == (lineage != uploaded_lineage),
        out matches Some(new) ==> new >= current && (new <= head || new == current)
            && (new == current || new == proposed),
))]
pub(super) fn lineage_offload(
    lineage: u64,
    uploaded_lineage: u64,
    current: u64,
    proposed: u64,
    head: u64,
) -> Option<u64> {
    if lineage == uploaded_lineage {
        Some(offloaded_through(current, proposed, head))
    } else {
        None
    }
}

/// Extend the maximum population used by the placement check.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out >= largest && out >= count && (out == largest || out == count),
))]
pub(super) fn largest_domain(largest: usize, count: usize) -> usize {
    if largest > count { largest } else { count }
}
