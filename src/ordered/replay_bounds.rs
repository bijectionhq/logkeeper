#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Index the exact retained interval, with an exclusive upper cut.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    (out is Some) == (floor <= from && from <= through && through as int - floor as int <= retained),
    out matches Some((first, end)) ==> first <= end <= retained
        && floor as int + first as int == from as int
        && floor as int + end as int == through as int,
))]
pub(super) fn retained_indices(
    floor: u64, from: u64, through: u64, retained: usize,
) -> Option<(usize, usize)> {
    if floor > from || from > through || through - floor > retained as u64 {
        return None;
    }
    Some(((from - floor) as usize, (through - floor) as usize))
}

/// An exact cursor can resume at any cut within the original protected interval.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == if exact_cut && start <= from && from <= through && from as int - start as int <= usize::MAX as int {
        Some((from as int - start as int) as usize)
    } else { None },
))]
pub(super) fn cursor_offset(start: u64, from: u64, through: u64, exact_cut: bool) -> Option<usize> {
    if !exact_cut || from < start || from > through {
        return None;
    }
    let offset = from - start;
    if offset > usize::MAX as u64 {
        return None;
    }
    Some(offset as usize)
}

#[cfg_attr(verus_keep_ghost, verus_spec(charge => ensures
    (charge is Some) == (from as int + 1 == record_cut && record_cut <= through && byte_start <= byte_end),
    charge matches Some(bytes) ==> bytes as int == byte_end as int - byte_start as int,
))]
pub(super) fn replay_record_charge(
    from: u64, record_cut: u64, through: u64, byte_start: u64, byte_end: u64,
) -> Option<u64> {
    if from.checked_add(1) != Some(record_cut) || record_cut > through {
        return None;
    }
    byte_end.checked_sub(byte_start)
}
