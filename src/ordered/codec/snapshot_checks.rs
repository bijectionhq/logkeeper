#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn generationInRange(epoch: int, generation: int) -> bool {
    0 < generation && generation <= if epoch < 1 { 1 } else { epoch }
}

pub(crate) open spec fn leaseRowValid(
    serial: int,
    last_serial: int,
    retained: bool,
    lease_end: int,
    duration: int,
    time: int,
    key_increases: bool,
) -> bool {
    0 < serial <= last_serial
        && retained
        && duration <= lease_end <= time + duration
        && key_increases
}

pub(crate) open spec fn fenceRowValid(
    position: int,
    last_position: int,
    time: int,
    last_time: int,
    key_increases: bool,
) -> bool {
    0 < position <= last_position && time <= last_time && key_increases
}

pub(crate) open spec fn holdReceiptMatches(admitted_at: u64, receipt_position: Option<u64>) -> bool {
    receipt_position == Some(admitted_at)
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == generationInRange(epoch as int, generation as int),
))]
pub(super) fn generation_in_range(epoch: u64, generation: u64) -> bool {
    generation != 0 && generation <= epoch.max(1)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == leaseRowValid(
        serial as int, last_serial as int, retained, lease_end as int, duration as int, time as int, key_increases,
    ),
))]
pub(super) fn lease_row_valid(
    serial: u64,
    last_serial: u64,
    retained: bool,
    lease_end: u64,
    duration: u64,
    time: u64,
    key_increases: bool,
) -> bool {
    serial != 0
        && serial <= last_serial
        && retained
        && lease_end >= duration
        && lease_end <= time.saturating_add(duration)
        && key_increases
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == fenceRowValid(position as int, last_position as int, time as int, last_time as int, key_increases),
))]
pub(super) fn fence_row_valid(
    position: u64,
    last_position: u64,
    time: u64,
    last_time: u64,
    key_increases: bool,
) -> bool {
    position != 0 && position <= last_position && time <= last_time && key_increases
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == holdReceiptMatches(admitted_at, receipt_position),
))]
pub(super) fn hold_receipt_matches(admitted_at: u64, receipt_position: Option<u64>) -> bool {
    match receipt_position {
        Some(position) => admitted_at == position,
        None => false,
    }
}

pub(super) fn root_reference_row_valid(
    revision: u64,
    previous: Option<u64>,
    known: bool,
) -> bool {
    known && match previous {
        Some(previous) => previous < revision,
        None => true,
    }
}
