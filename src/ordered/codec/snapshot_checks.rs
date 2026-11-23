pub(super) fn generation_in_range(epoch: u64, generation: u64) -> bool {
    generation != 0 && generation <= epoch.max(1)
}

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

pub(super) fn fence_row_valid(
    position: u64,
    last_position: u64,
    time: u64,
    last_time: u64,
    key_increases: bool,
) -> bool {
    position != 0 && position <= last_position && time <= last_time && key_increases
}

pub(super) fn hold_receipt_matches(admitted_at: u64, receipt_position: Option<u64>) -> bool {
    match receipt_position {
        Some(position) => admitted_at == position,
        None => false,
    }
}
