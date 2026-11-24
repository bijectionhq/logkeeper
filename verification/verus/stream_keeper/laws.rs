use crate::production::*;
use vstd::prelude::*;

verus! {

pub fn create_cannot_reuse_a_stream_id(deleted: bool) {
    let eligible = live(deleted);
    assert(eligible == !deleted);
}

pub fn seal_requires_a_higher_epoch_or_same_holder(
    has_promise: bool, current: u64, epoch: u64, same_holder: bool,
) {
    let allowed = may_seal(has_promise, current, epoch, same_holder);
    assert(allowed == (!has_promise || epoch > current || (epoch == current && same_holder)));
}

pub fn sync_cannot_replace_committed_records(from: u64, commit: u64, identical: bool) {
    let allowed = preserves_commit(from, commit, identical);
    assert(allowed == (commit < from || identical));
}

pub fn sync_commit_is_monotone_and_bounded(current: u64, next: u64, end: u64, floor: u64) {
    let allowed = sync_commit_valid(current, next, end, floor);
    assert(allowed == (current <= next && next <= end && 1 <= floor && floor as int <= next as int + 1));
}

pub fn append_requires_both_current_promise_and_sync(promised: bool, synced: bool) {
    let allowed = may_append(promised, synced);
    assert(allowed == (promised && synced));
}

pub fn append_retry_must_match_the_whole_existing_range(nonempty: bool, last: u64, end: u64, identical: bool) {
    let retry = append_retry(nonempty, last, end, identical);
    assert(retry == (nonempty && last <= end && identical));
}

pub fn trim_cannot_cross_the_commit(through: u64, commit: u64) {
    let allowed = may_trim(through, commit);
    assert(allowed == (through <= commit));
}

pub fn check_reports_the_existing_end(current: u64, request_epoch: u64) {
    let reported = checked_end(current, request_epoch);
    assert(reported == current);
}

pub fn read_cannot_expose_the_accepted_tail(commit: u64, accepted: u64)
    requires commit <= accepted
{
    let through = read_end(commit, accepted);
    assert(through == commit);
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
