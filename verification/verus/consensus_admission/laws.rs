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

// A replacement restages a recovery copy at the revision it already holds
// only for a retry of the same survivor's recovery, which never wrote to
// that copy; any other stage at that revision stays refused.
fn a_recovery_restages_only_its_own_aborted_copy(
    staged_recovery: bool, retried_recovery: bool, same_origin: bool,
) {
    let restages = restages_recovery(staged_recovery, retried_recovery, same_origin);
    assert(restages ==> staged_recovery && retried_recovery && same_origin);
    assert(!same_origin ==> !restages);
}

// An ordinary move restages a copy at the revision it already holds only
// when another ordinary move from the same source staged it: a recovery
// copy, a copy of another source configuration and the same stage are
// never restaged.
fn an_aborted_move_restages_only_for_the_same_source(
    staged_recovery: bool, stage_recovery: bool, same_source: bool, same_stage: bool,
) {
    let restages = restages_replacement(staged_recovery, stage_recovery, same_source, same_stage);
    assert(restages ==> same_source && !same_stage);
    assert(staged_recovery || stage_recovery ==> !restages);
    assert(!staged_recovery && !stage_recovery && same_source && !same_stage ==> restages);
}

// A copy serves applied pages only once its placement is certified, so a
// lost voter never serves a suffix an operator recovery left behind.
fn only_certified_members_serve_reads(member: bool, certified: bool) {
    let serves = serves_reads(member, certified);
    assert(serves ==> member && certified);
    assert(!certified ==> !serves);
}

// The catalog's latest move fences the lost configuration of a recovery and
// any configuration older than an ordinary move, but never the configuration
// a stream goes on from, so certification never wedges a healthy copy.
fn the_catalog_fences_only_superseded_configurations(
    configured: bool, recovery: bool, at_old: bool, at_target: bool, joint_of_move: bool,
) {
    let fenced = fences_copy(configured, recovery, at_old, at_target, joint_of_move);
    assert(fenced ==> configured);
    assert(configured && recovery && !at_target ==> fenced);
    assert(at_target ==> !fenced);
    assert(!recovery && (at_old || joint_of_move) ==> !fenced);
    assert(configured && !recovery && !at_old && !at_target && !joint_of_move ==> fenced);
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


// Parking.accept_requires_exact_log: a follower parks only while it follows
// under the leader's vote and holds exactly the leader's applied log, with
// no entry past it, so a parked follower never freezes a suffix the leader
// lacks.
fn a_parked_follower_holds_the_leaders_applied_log(
    follower: bool, same_vote: bool, same_applied: bool, last_log: Option<u64>,
    leader_applied: Option<u64>, idle: bool,
) {
    let parked = accepts_park(follower, same_vote, same_applied, last_log, leader_applied, idle);
    assert(parked ==> follower && same_vote && same_applied && last_log == leader_applied && idle);
    if last_log != leader_applied {
        assert(!parked);
    }
    let leading = accepts_park(false, same_vote, same_applied, last_log, leader_applied, idle);
    assert(!leading);
}

// A group is idle only when it applied its whole log, its membership is
// uniform, it receives no snapshot, and neither a client nor a new entry
// touched it within the park delay.
fn only_a_quiet_applied_uniform_group_is_idle(
    quiet_log_ns: u128, unused_ns: u128, park_after_ns: u128, applied: Option<u64>,
    last_log: Option<u64>, uniform: bool, receiving: bool,
) {
    let parks = idle(quiet_log_ns, unused_ns, park_after_ns, applied, last_log, uniform, receiving);
    assert(parks ==> applied == last_log && uniform && !receiving);
    assert(quiet_log_ns < park_after_ns || unused_ns < park_after_ns ==> !parks);
}

// Parking.leader_parks_only_settled: a leader asks for parks only when it
// leads, is idle, and has applied its log with every live voter matched.
fn only_a_settled_idle_leader_parks(leader: bool, settled: bool, idle: bool) {
    let parks = leader_parks(leader, settled, idle);
    assert(parks == (leader && settled && idle));
}

// Parking.parked_answers_preserve_state: a parked replica answers an empty
// heartbeat busy within the park round and a repeated park without opening
// its group, and reopens for entries, votes, pre-votes, snapshots,
// transfers and heartbeats that go on past the park round.
fn a_parked_replica_reopens_only_for_work(parked_ns: u128, window_ns: u128) {
    let heartbeat = parked_answer(ParkedRequest::Heartbeat, parked_ns, window_ns);
    assert(parked_ns < window_ns ==> heartbeat is Busy);
    assert(parked_ns >= window_ns ==> heartbeat is Reopen);
    let repeated = parked_answer(ParkedRequest::Park, parked_ns, window_ns);
    assert(repeated is Parked);
    let work = parked_answer(ParkedRequest::Other, parked_ns, window_ns);
    assert(work is Reopen);
}

// A voter whose keeper is alive and that acknowledged this leader within
// the repair delay is never repaired away; nor is one that never
// acknowledged while this leader has led for less than the delay.
fn a_recently_heard_voter_is_not_silent(
    dead: bool, acked_ns: Option<u128>, led_ns: u128, repair_after_ns: u128,
) {
    let quiet = silent(dead, acked_ns, led_ns, repair_after_ns);
    assert(dead ==> quiet);
    if let Some(acked) = acked_ns {
        assert(!dead && acked < repair_after_ns ==> !quiet);
        assert(acked >= repair_after_ns ==> quiet);
    } else {
        assert(!dead && led_ns < repair_after_ns ==> !quiet);
    }
}

// A learner leaves only after the stale delay.
fn learners_leave_only_after_the_stale_delay(seen_ns: u128, stale_ns: u128) {
    let stale = learner_stale(seen_ns, stale_ns);
    assert(seen_ns < stale_ns ==> !stale);
    assert(seen_ns >= stale_ns ==> stale);
}

spec fn key_less(a: (u8, bool, u128), b: (u8, bool, u128)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && ((!a.1 && b.1) || (a.1 == b.1 && a.2 < b.2)))
}

// Repair order: higher priority work starts first; within one priority,
// a stream after the one the last pass started last goes before every
// stream at or before it, so each stream gets its turn.
fn repair_order_prefers_priority_then_rotation(
    rank_a: u8, a: u128, rank_b: u8, b: u128, cursor: Option<u128>,
) {
    let key_a = repair_key(rank_a, a, cursor);
    let key_b = repair_key(rank_b, b, cursor);
    assert(rank_a < rank_b ==> key_less(key_a, key_b));
    if let Some(last) = cursor {
        assert(rank_a == rank_b && b <= last && last < a ==> key_less(key_a, key_b));
    }
    assert(rank_a == rank_b && cursor is None && a < b ==> key_less(key_a, key_b));
}

// A pass over queued work starts at most `max_repairs` repairs in all,
// never a stream that already repairs or waits out its backoff, and
// stops at the first stream it finds with every slot taken.
fn a_repair_pass_respects_its_slots(
    queued: &[(bool, bool)], running: usize, max_repairs: usize,
) -> (started: usize)
    requires running <= max_repairs,
    ensures running + started <= max_repairs,
{
    let mut started: usize = 0;
    let mut index = 0;
    while index < queued.len()
        invariant
            index <= queued@.len(),
            running + started <= max_repairs,
        decreases queued@.len() - index,
    {
        let (repairing, backed_off) = queued[index];
        match starts_repair(running + started, max_repairs, repairing, backed_off) {
            RepairStart::Full => break,
            RepairStart::Skip => {}
            RepairStart::Start => {
                assert(!repairing && !backed_off);
                started += 1;
            }
        }
        index += 1;
    }
    started
}

// Nothing moves unless two of three voters are live: a membership change
// needs a quorum.
fn a_roster_moves_only_with_two_live_voters(live: usize) {
    let moves = repair_allowed(live);
    assert(live < 2 ==> !moves);
    assert(live >= 2 ==> moves);
}

// Placement never refuses an eligible keeper at or below the average load,
// and the ceiling exceeds the average by at least one stream.
fn average_keepers_stay_roomy(sum: u64, count: u64, streams: u32)
    requires count > 0,
{
    let ceiling = load_ceiling(sum, count);
    let ghost average = rounded_average(sum as int, count as int);
    assert(average >= sum as int / count as int);
    match ceiling {
        Some(ceiling) => {
            assert(ceiling as int > average || ceiling == u32::MAX);
            if streams as u64 <= sum / count {
                let room = roomy(Some(ceiling), Some(streams));
                assert(room);
            }
        }
        None => assert(false),
    }
    let unknown = roomy(ceiling, None);
    assert(unknown);
    let none = load_ceiling(sum, 0);
    assert(none is None);
}

// LeaderPreference: leadership moves only to another voter that matched
// the leader's whole log, and never within the hold-down.
fn leadership_moves_only_to_a_matched_voter(
    to_self: bool, matched: Option<u64>, last: Option<u64>, recent: bool,
) {
    let moves = hands_off(to_self, matched, last, recent);
    assert(moves ==> !to_self && !recent && matched is Some && matched == last);
    assert(recent ==> !moves);
}

// A copy looks for a retiring proof only when a peer excluded it or it
// heard no leader for the repair delay without leading.
fn only_orphaned_copies_seek_retirement(
    excluded: bool, leader: bool, unheard_ns: u128, repair_after_ns: u128,
) {
    let seeks = orphaned(excluded, leader, unheard_ns, repair_after_ns);
    assert(!excluded && leader ==> !seeks);
    assert(!excluded && unheard_ns < repair_after_ns ==> !seeks);
    assert(excluded ==> seeks);
}

// A voter refuses to vote only when another keeper finalized a newer
// configuration that names it neither as a voter nor as a joint target,
// so a voter the newer configuration keeps always votes.
fn a_named_voter_never_refuses_a_vote(
    local_revision: u64, proof_revision: u64, named_voter: bool, named_joint: bool,
) {
    let refuses = refuses_stale_vote(local_revision, proof_revision, named_voter, named_joint);
    assert(refuses ==> proof_revision > local_revision);
    assert(named_voter || named_joint ==> !refuses);
    assert(proof_revision <= local_revision ==> !refuses);
}

// RetireOnProof.retired_copy_outside_every_quorum: a certified proof
// retires a copy only at the asked revision and only when neither the
// configuration nor its joint target names the keeper, so no quorum of
// the certified configuration counts the retired copy.
fn retirement_never_removes_a_named_copy(same_revision: bool, named_voter: bool, named_joint: bool) {
    let retires = certifies_exclusion(same_revision, named_voter, named_joint);
    assert(retires ==> same_revision && !named_voter && !named_joint);
    assert(named_voter || named_joint ==> !retires);
}

// RecoveryFence: while an operator recovery's fence stands, every seal is
// refused with `Recovered`. Otherwise a seal installs a fence one above the
// epoch it expected only when that epoch is current, so the new epoch is
// above every applied one; any other seal only repeats an existing fence.
fn a_recovery_fence_refuses_every_seal(current: u64, expected: u64) {
    let fenced = seal_step(true, current, expected);
    assert(fenced is Recovered);
    match seal_step(false, current, expected) {
        SealStep::Install(epoch) => assert(epoch > current && current == expected),
        SealStep::Repeat(epoch) => assert(current != expected && epoch == expected + 1),
        SealStep::Unavailable => assert(expected == u64::MAX),
        SealStep::Recovered => assert(false),
    }
    // The recovery fence sits above the survivor's epoch, and after the
    // acknowledgement the first seal of that epoch installs the next one.
    if let Some(fence) = recovery_epoch(current) {
        assert(fence > current);
        if fence < u64::MAX {
            let resumed = seal_step(false, fence, fence);
            assert(resumed matches SealStep::Install(next) && next > fence);
            let stale = seal_step(false, fence, current);
            assert(stale is Repeat);
        }
    }
}

// The boundary restart trusts is the intact slot with the higher sequence.
// A write alternates slots, so a torn write of round n + 1 leaves round n.
fn restart_trusts_the_newest_intact_slot(older: u64)
    requires older < u64::MAX,
{
    let both = newest_slot(Some(older), Some(older + 1));
    assert(both matches Some(1));
    let reversed = newest_slot(Some(older + 1), Some(older));
    assert(reversed matches Some(0));
    let torn = newest_slot(Some(older), None);
    assert(torn matches Some(0));
    let lost = newest_slot(None, None);
    assert(lost is None);
}

// A checkpoint past the trusted boundary, or inside a segment header, is
// refused.
fn a_checkpoint_past_the_boundary_is_refused(
    segment: u64, offset: u64, boundary_segment: u64, boundary_offset: u64, header: u64,
) {
    let within = checkpoint_within(segment, offset, boundary_segment, boundary_offset, header);
    assert(segment > boundary_segment ==> !within);
    assert(segment == boundary_segment && offset > boundary_offset ==> !within);
    assert(offset < header || boundary_offset < header ==> !within);
}

spec fn total(lengths: Seq<u64>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { total(lengths, n - 1) + lengths[n - 1] as int }
}

proof fn total_grows(lengths: Seq<u64>, a: int, b: int)
    requires 0 <= a <= b <= lengths.len(),
    ensures total(lengths, a) <= total(lengths, b),
    decreases b - a,
{
    if a < b {
        total_grows(lengths, a, b - 1);
    }
}

// Rollback detection. Replay of the boundary's segment from `start` reads
// whole frames of the given lengths followed by a clean end or a torn
// frame. It finishes only exactly at the trusted boundary, and when the
// data volume holds fewer bytes than the boundary acknowledged, as after
// a rollback, it fails.
fn replay_detects_a_rolled_back_segment(
    lengths: &[u64], start: u64, end: u64,
) -> (finished: bool)
    requires
        lengths@.len() <= 0x1_0000,
        forall|i: int| 0 <= i < lengths@.len() ==> 0 < #[trigger] lengths@[i] <= 0x1_0000_0000,
        start <= 0x1_0000_0000_0000,
        start <= end,
    ensures
        end > start + total(lengths@, lengths@.len() as int) ==> !finished,
{
    let mut offset = start;
    let mut index: usize = 0;
    while offset != end
        invariant
            index <= lengths@.len(),
            lengths@.len() <= 0x1_0000,
            forall|i: int| 0 <= i < lengths@.len() ==> 0 < #[trigger] lengths@[i] <= 0x1_0000_0000,
            start <= 0x1_0000_0000_0000,
            offset as int == start as int + total(lengths@, index as int),
            total(lengths@, index as int) <= index as int * 0x1_0000_0000,
        decreases lengths@.len() - index,
    {
        let (frame, next) = if index < lengths.len() {
            (FrameRead::Complete, offset + lengths[index])
        } else {
            (FrameRead::Torn, offset)
        };
        match replay_step(frame, next, Some(end)) {
            ReplayStep::Apply => {
                assert(index < lengths@.len());
                index += 1;
                offset = next;
            }
            _ => return false,
        }
    }
    proof {
        total_grows(lengths@, index as int, lengths@.len() as int);
    }
    true
}

}
