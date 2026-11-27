use crate::production::*;
use vstd::prelude::*;

verus! {

// PeerBudget.control_header_cannot_dispatch_payload: an AppendEntries batch
// with one application entry belongs to replication, so a frame received on
// the control lane cannot dispatch it.
fn payload_append_is_never_control(kinds: &[EntryKind], index: usize)
    requires index < kinds@.len(), kinds@[index as int] is Application,
{
    let application = carries_application(kinds);
    assert(application);
    let lane = peer_lane(PeerKind::Append, application);
    assert(lane is Replication);
}

// PeerBudget.vote_and_empty_append_are_control.
fn vote_and_metadata_only_append_are_control(kinds: &[EntryKind], application: bool)
    requires forall|i: int| 0 <= i < kinds@.len() ==> !(#[trigger] kinds@[i] is Application),
{
    let vote = peer_lane(PeerKind::Vote, application);
    assert(vote is Control);
    let carries = carries_application(kinds);
    assert(!carries);
    let append = peer_lane(PeerKind::Append, carries);
    assert(append is Control);
    let empty: [EntryKind; 0] = [];
    let carries_none = carries_application(&empty);
    assert(!carries_none);
}

fn snapshots_use_bulk(application: bool) {
    let lane = peer_lane(PeerKind::Snapshot, application);
    assert(lane is Bulk);
}

// PeerBudget.reserve_body_preserves_budget: an admitted body keeps the
// receiver and the sender within their byte and frame caps.
fn admitted_body_preserves_budgets(
    total_frames: usize, total_bytes: usize, sender_frames: usize, sender_bytes: usize, size: usize,
) {
    let charge = body_charge(size);
    if admits_body(total_frames, total_bytes, sender_frames, sender_bytes, charge) {
        assert(total_frames + 1 <= RECEIVER_FRAMES);
        assert(sender_frames + 1 <= SENDER_FRAMES);
        assert(total_bytes as int + charge as int <= RECEIVER_BYTES as int);
        assert(sender_bytes as int + charge as int <= SENDER_BYTES as int);
        assert(size as int * BODY_COPIES as int + BODY_OVERHEAD as int <= usize::MAX as int
            ==> charge as int == size as int * BODY_COPIES as int + BODY_OVERHEAD as int);
    }
}

// PeerBudget.one_sender_cannot_spend_others_remaining_body_capacity. When
// the receiver's bytes are the sender's plus everyone else's, an admitted
// body leaves the others at least `RECEIVER_BYTES - SENDER_BYTES` minus
// what they already hold.
fn one_sender_leaves_the_others_their_share(
    total_frames: usize, others: usize, sender_frames: usize, sender_bytes: usize, size: usize,
)
    requires others as int + sender_bytes as int <= usize::MAX as int,
{
    let charge = body_charge(size);
    let total_bytes = others + sender_bytes;
    if admits_body(total_frames, total_bytes, sender_frames, sender_bytes, charge) {
        assert(RECEIVER_BYTES as int - (total_bytes as int + charge as int)
            >= RECEIVER_BYTES as int - SENDER_BYTES as int - others as int);
        proof { limits(); }
        assert(RECEIVER_BYTES as int - SENDER_BYTES as int == 167_772_160);
    }
}

// The frame share of the same theorem, where a frame is one peer message in
// flight: an admitted message leaves the others at least
// `RECEIVER_FRAMES - SENDER_FRAMES` slots minus what they already hold,
// however many messages share a batch or a connection.
fn one_sender_leaves_the_others_their_frames(
    others: usize, sender_frames: usize, total_bytes: usize, sender_bytes: usize, size: usize,
)
    requires others as int + sender_frames as int <= usize::MAX as int,
{
    let charge = body_charge(size);
    let total_frames = others + sender_frames;
    if admits_body(total_frames, total_bytes, sender_frames, sender_bytes, charge) {
        proof { limits(); }
        assert(RECEIVER_FRAMES as int - (total_frames as int + 1)
            >= RECEIVER_FRAMES as int - SENDER_FRAMES as int - others as int);
        assert(RECEIVER_FRAMES - SENDER_FRAMES == 256);
    }
}

// Releasing an admitted message restores its meter exactly, so a sender's
// share and the receiver's budget return to what they were before.
fn release_is_exact(
    total_frames: usize, total_bytes: usize, sender_frames: usize, sender_bytes: usize, size: usize,
) {
    let charge = body_charge(size);
    if admits_body(total_frames, total_bytes, sender_frames, sender_bytes, charge) {
        proof { limits(); }
        let (frames, bytes) = meter_admit(total_frames, total_bytes, charge);
        let (from_frames, from_bytes) = meter_admit(sender_frames, sender_bytes, charge);
        assert(frames <= RECEIVER_FRAMES && bytes <= RECEIVER_BYTES);
        assert(from_frames <= SENDER_FRAMES && from_bytes <= SENDER_BYTES);
        let (frames, bytes) = meter_release(frames, bytes, charge);
        let (from_frames, from_bytes) = meter_release(from_frames, from_bytes, charge);
        assert(frames == total_frames && bytes == total_bytes);
        assert(from_frames == sender_frames && from_bytes == sender_bytes);
    }
}

// Control work: one sender's cap leaves aggregate control work for others,
// and releasing admitted work restores both counts.
fn one_sender_leaves_control_work_for_others(total: usize, sender: usize)
    requires sender <= total,
{
    if admits_control(total, sender) {
        assert(total + 1 <= MAX_CONTROL_WORK);
        assert(sender + 1 <= CONTROL_PER_SENDER);
        let (work, _) = meter_admit(total, 0, 0);
        let (from, _) = meter_admit(sender, 0, 0);
        let (work, _) = meter_release(work, 0, 0);
        let (from, _) = meter_release(from, 0, 0);
        assert(work == total && from == sender);
    }
    proof { limits(); }
    assert(MAX_CONTROL_WORK - CONTROL_PER_SENDER == 256);
}

// PeerBudget.saturated_data_admits_control_and_maintenance and
// Headroom.Follower.replication_preserves_maintenance_and_control. After an
// ordinary or follower reservation, one request of each reserved class
// within its own budget still fits.
fn ordinary_admission_keeps_reserved_classes_feasible(
    measured: u64, pending: u64, bytes: u64, control: u64, maintenance: u64, scratch: u64,
)
    requires control <= CONTROL_BYTES, maintenance <= MAINTENANCE_BYTES, scratch <= SCRATCH_BYTES,
{
    proof { limits(); }
    if fits(measured, pending, bytes, ORDINARY_FLOOR) {
        let held = pending + bytes;
        let protocol = fits(measured, held, control, PROTOCOL_FLOOR);
        let reclaim = fits(measured, held, maintenance, MAINTENANCE_FLOOR);
        let covered = fits(measured, held, maintenance, COVERED_FLOOR);
        let building = fits(measured, held, scratch, SCRATCH_FLOOR);
        assert(protocol && reclaim && covered && building);
    }
}

fn suffix_admission_respects_the_limit(occupied: usize, new: usize, slots: usize, limit: usize) {
    if suffix_admits(occupied, new, slots, limit) && new > 0 {
        assert(occupied as int + new as int + slots as int <= limit as int);
    }
}

spec fn distance(from: int, to: int) -> int {
    (to - from + 5) % 5
}

// PeerBudget.persistent_lane_served_within_five. The scan from `next`
// reaches a continuously ready lane within five probes. When the scan
// serves an earlier ready lane instead, the next scan starts strictly
// closer to it. A ready lane is therefore served within five turns.
fn rotation_serves_a_ready_lane_within_five(next: usize, lane: usize, served: usize)
    requires next < LANES, lane < LANES, served < LANES,
        distance(next as int, served as int) < distance(next as int, lane as int),
{
    proof { limits(); }
    let reach = ((lane + LANES - next) % LANES) as usize;
    assert(reach < LANES);
    let probed = probe(next, reach);
    assert(probed == lane);
    let following = after(served);
    assert(distance(following as int, lane as int) < distance(next as int, lane as int));
}

// A sender's split always makes progress and never loses the batch.
fn oversized_batches_shrink(size: u64, limit: u64, count: usize, max_entries: usize) {
    match fit_append(size, limit, count, max_entries) {
        AppendFit::Split(hint) => assert(1 <= hint && hint < count),
        AppendFit::Unfit => assert(count <= 1 && !(size <= limit && count <= max_entries)),
        AppendFit::Fits => assert(size <= limit && count <= max_entries),
    }
}

// RestartRead: the presented vote keeps its term and ballot and is
// committed only when it does not name this keeper.
spec fn restores_leader(committed: bool, voted_for_self: bool) -> bool {
    committed && voted_for_self
}

fn restart_never_restores_leadership(committed: bool, voted_for_self: bool) {
    let demoted = demotes_vote(committed, voted_for_self);
    let presented = committed && !demoted;
    assert(!restores_leader(presented, voted_for_self));
    assert(!voted_for_self ==> presented == committed);
}

// Recovery admission: a recovery runs only with the operator's
// acknowledgement and a survivor that votes in the latest configuration,
// and only when no other voter answers with a healthy replica. The
// survivor alone is then fewer than the two voters a quorum of three needs,
// so no live quorum can commit beside the recovered log.
fn recovery_needs_acknowledgement_and_no_live_quorum(
    acknowledged: bool, survivor_votes: bool, healthy_others: u64,
) {
    if allows_recovery(acknowledged, survivor_votes, healthy_others) {
        assert(acknowledged && survivor_votes);
        assert(1 + healthy_others < 2);
    }
    let unacknowledged = allows_recovery(false, survivor_votes, healthy_others);
    assert(!unacknowledged);
    if healthy_others >= 1 {
        let alive = allows_recovery(acknowledged, survivor_votes, healthy_others);
        assert(!alive);
    }
}

// The recovery's vote and entries carry a term above every ballot and
// entry of the survivor's history, and its fence an epoch above every
// applied epoch, or the recovery is refused.
fn recovery_outranks_the_lost_history(vote_term: u64, log_term: u64, epoch: u64) {
    match recovery_term(vote_term, log_term) {
        Some(term) => {
            assert(term > vote_term && term > log_term);
            assert(term as int - RECOVERY_TERM_GAP as int >= vote_term as int);
        }
        None => assert(vote_term > u64::MAX - RECOVERY_TERM_GAP
            || log_term > u64::MAX - RECOVERY_TERM_GAP),
    }
    match recovery_epoch(epoch) {
        Some(fence) => assert(fence > epoch),
        None => assert(epoch == u64::MAX),
    }
}

// A replica refuses a peer without a Raft answer only when the peer is
// outside its effective membership and below its term: a member, or a peer
// at or above its term, always gets an answer, so the refusal never hides a
// newer history from this replica.
fn only_superseded_outsiders_are_excluded(
    configured: bool, known: bool, sender_term: u64, own_term: u64,
) {
    let excluded = excludes_sender(configured, known, sender_term, own_term);
    assert(excluded ==> configured && !known && sender_term < own_term);
    assert(known ==> !excluded);
    assert(sender_term >= own_term ==> !excluded);
}

// Only installed replicas vote. Outside a recovery, a configured replica
// votes only as a member and an unconfigured one only as a genesis voter.
fn only_installed_members_vote(
    installed: bool, configured: bool, member: bool, genesis_voter: bool, recovering: bool,
) {
    let vote = votes(installed, configured, member, genesis_voter, recovering);
    assert(!installed ==> !vote);
    assert(vote && configured && !recovering ==> member);
    assert(vote && !configured && !recovering ==> genesis_voter);
}

// An accepted peer batch continues exactly after its previous entry, with
// strictly increasing indices and terms bounded by the sender's vote.
fn accepted_batches_are_consecutive(
    previous: Option<(u64, u64)>, ids: &[(u64, u64)], vote_term: u64, i: usize,
)
    requires 0 < i < ids@.len(),
{
    if consecutive_cut(previous, ids, vote_term) {
        assert(ids@[i as int].0 as int == ids@[i as int - 1].0 as int + 1);
        assert(ids@[i as int - 1].1 <= ids@[i as int].1);
        assert(ids@[i as int].1 <= vote_term);
    }
}


// A keeper ID reused on new media is recognized: a first contact is never a
// reuse, the incarnation first seen is never one, and any other is.
fn only_another_incarnation_is_a_reuse(first: u128, reported: u128) {
    let unknown = reincarnated(None, reported);
    assert(!unknown);
    let same = reincarnated(Some(reported), reported);
    assert(!same);
    let other = reincarnated(Some(first), reported);
    assert(other == (first != reported));
}

// A keeper registers a replica it does not hold only as a genesis voter
// whose identity a peer confirmed, and never once its ID was reused, so a
// keeper with reinstalled media never votes with an empty log.
fn a_reused_keeper_never_registers(genesis_voter: bool, confirmed: bool, reused: bool) {
    let registered = registers(genesis_voter, confirmed, reused);
    assert(registered ==> genesis_voter && confirmed);
    assert(reused ==> !registered);
    let unconfirmed = registers(genesis_voter, false, reused);
    assert(!unconfirmed);
    let fresh = registers(true, true, false);
    assert(fresh);
}

// A grant from a peer seen under another incarnation never counts toward a
// campaign; any other grant does.
fn a_reused_keeper_grants_nothing(granted: bool, reincarnated: bool) {
    let counted = counts_grant(granted, reincarnated);
    assert(reincarnated ==> !counted);
    assert(!granted ==> !counted);
    let honest = counts_grant(granted, false);
    assert(honest == granted);
}

// A keeper counts as dead only once its silence reaches the repair delay, so
// a keeper that answered within the delay is never repaired away, parked
// past or woken for.
fn dead_only_after_the_repair_delay(silent_ms: u64, repair_after_ms: u64) {
    let dead = keeper_dead(silent_ms, repair_after_ms);
    assert(silent_ms < repair_after_ms ==> !dead);
    assert(silent_ms >= repair_after_ms ==> dead);
}

// A keeper whose WAL round runs past the soft limit, or whose last slow
// round is still held, never counts its media responsive; one with no slow
// round in progress or held does.
fn slow_media_is_never_responsive(running_ms: u64, slow_until_ms: u64, now_ms: u64, soft_ms: u64) {
    let responsive = media_responsive(running_ms, slow_until_ms, now_ms, soft_ms);
    assert(running_ms > soft_ms ==> !responsive);
    assert(now_ms < slow_until_ms ==> !responsive);
    let idle = media_responsive(0, now_ms, now_ms, soft_ms);
    assert(idle);
}

proof fn grown_is_bounded(wait: int, cap: int, n: nat)
    requires 0 <= wait <= cap,
    ensures wait <= grown(wait, cap, n) <= cap,
    decreases n,
{
    if wait < cap && n > 0 {
        let next = if 2 * wait > cap { cap } else { 2 * wait };
        grown_is_bounded(next, cap, (n - 1) as nat);
    }
}

proof fn grown_never_shrinks(wait: int, cap: int, n: nat)
    requires 0 <= wait <= cap,
    ensures grown(wait, cap, n) <= grown(wait, cap, n + 1),
    decreases n,
{
    if wait < cap {
        let next = if 2 * wait > cap { cap } else { 2 * wait };
        if n == 0 {
            grown_is_bounded(next, cap, 0);
        } else {
            grown_never_shrinks(next, cap, (n - 1) as nat);
        }
    }
}

// A repair or wake backoff never exceeds its cap, never undercuts its base
// below the cap, and never shrinks after another failure: a stream that
// keeps failing waits longer each time, up to the cap.
fn backoff_is_bounded_and_grows(failures: u32, base_ms: u64, cap_ms: u64)
    requires failures < u32::MAX,
{
    let wait = backoff(failures, base_ms, cap_ms);
    let next = backoff(failures + 1, base_ms, cap_ms);
    proof {
        let start = if base_ms < cap_ms { base_ms as int } else { cap_ms as int };
        grown_is_bounded(start, cap_ms as int, failures as nat);
        grown_never_shrinks(start, cap_ms as int, failures as nat);
    }
    assert(wait <= cap_ms);
    assert(wait >= base_ms || wait == cap_ms);
    assert(next >= wait);
}

}
