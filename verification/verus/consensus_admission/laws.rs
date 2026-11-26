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

// Control work: one sender's cap leaves aggregate control work for others.
fn one_sender_leaves_control_work_for_others(total: usize, sender: usize)
    requires sender <= total,
{
    if admits_control(total, sender) {
        assert(total + 1 <= MAX_CONTROL_WORK);
        assert(sender + 1 <= CONTROL_PER_SENDER);
    }
    proof { limits(); }
    assert(MAX_CONTROL_WORK - CONTROL_PER_SENDER == 32);
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

}
