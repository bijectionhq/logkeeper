use crate::production::*;
use vstd::prelude::*;

verus! {

pub fn create_cannot_reuse_a_stream_id(deleted: bool) {
    let eligible = live(deleted);
    assert(eligible == !deleted);
}

pub fn seal_requires_a_higher_epoch_or_same_identity(
    has_promise: bool, current: u64, epoch: u64, same_identity: bool,
) {
    let allowed = may_seal(has_promise, current, epoch, same_identity);
    assert(allowed == (!has_promise || epoch > current || (epoch == current && same_identity)));
}

pub fn sync_cannot_replace_headted_records(from: u64, head: u64, identical: bool) {
    let allowed = preserves_head(from, head, identical);
    assert(allowed == (head < from || identical));
}

pub fn sync_head_is_monotone_and_bounded(current: u64, next: u64, tail: u64, floor: u64) {
    let allowed = sync_head_valid(current, next, tail, floor);
    assert(allowed == (current <= next && next <= tail && 1 <= floor && floor as int <= next as int + 1));
}

pub fn append_requires_both_current_promise_and_sync(promised: bool, synced: bool) {
    let allowed = may_append(promised, synced);
    assert(allowed == (promised && synced));
}

pub fn append_retry_must_match_the_whole_existing_range(nonempty: bool, last: u64, tail: u64, identical: bool) {
    let retry = append_retry(nonempty, last, tail, identical);
    assert(retry == (nonempty && last <= tail && identical));
}

pub fn trim_cannot_cross_the_head(through: u64, head: u64) {
    let allowed = may_trim(through, head);
    assert(allowed == (through <= head));
}

pub fn check_reports_the_existing_tail(current: u64, request_epoch: u64) {
    let reported = checked_tail(current, request_epoch);
    assert(reported == current);
}

pub fn read_cannot_expose_the_accepted_tail(head: u64, accepted: u64)
    requires head <= accepted
{
    let through = read_head(head, accepted);
    assert(through == head);
}

pub fn read_cannot_cross_the_floor(floor: u64, from: u64) {
    let allowed = may_read(floor, from);
    assert(allowed == (floor <= from));
}

pub fn delete_is_terminal(deleted: bool, deleting: bool) {
    let next = tombstone(deleted, deleting);
    assert(next == (deleted || deleting));
}

pub fn replace_requires_a_synced_current_ensemble_with_one_new_member(
    current: bool, synced: bool, member: bool, changed: usize,
) {
    let allowed = may_replace(current, synced, member, changed);
    assert(allowed == (current && synced && member && changed == 1));
}

}
