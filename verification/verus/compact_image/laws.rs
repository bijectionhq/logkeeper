use crate::production::{
    fence_row_valid, generation_in_range, hold_receipt_matches, lease_row_valid,
};
use vstd::prelude::*;

verus! {

fn vacant_generation_obeys_epoch(epoch: u64, generation: u64) {
    let accepted = generation_in_range(epoch, generation);
    assert(accepted ==> generation != 0 && (epoch == 0 ==> generation == 1));
}

fn accepted_lease_has_retained_owner_and_bounds(
    serial: u64,
    last_serial: u64,
    retained: bool,
    lease_end: u64,
    duration: u64,
    time: u64,
    key_increases: bool,
) {
    let accepted = lease_row_valid(serial, last_serial, retained, lease_end, duration, time, key_increases);
    assert(accepted ==> retained && duration <= lease_end as int <= time as int + duration);
    assert(accepted ==> 0 < serial <= last_serial && key_increases);
}

fn accepted_fence_has_bounded_coordinates(
    position: u64,
    last_position: u64,
    time: u64,
    last_time: u64,
    key_increases: bool,
) {
    let accepted = fence_row_valid(position, last_position, time, last_time, key_increases);
    assert(accepted ==> 0 < position <= last_position && time <= last_time && key_increases);
}

fn a_checked_hold_has_a_matching_receipt(admitted_at: u64, receipt: Option<u64>) {
    let accepted = hold_receipt_matches(admitted_at, receipt);
    assert(accepted ==> receipt == Some(admitted_at));
}

}
