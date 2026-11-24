//! Numeric checks shared by the segmented WAL and the checkpoint index.
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (len as int <= max as int && 8 + len as int <= remaining as int)
))]
pub(super) fn frame_body_fits(remaining: u64, len: u32, max: usize) -> bool {
    len as usize <= max && remaining >= 8 && u64::from(len) <= remaining - 8
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (expected == actual)))]
pub(super) fn checksum_matches(expected: u32, actual: u32) -> bool {
    expected == actual
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (seq <= next && len as int <= max as int
        && offset as int + len as int <= size as int)
))]
pub(super) fn extent_fits(
    seq: u64,
    next: u64,
    offset: u64,
    len: u32,
    max: usize,
    size: u64,
) -> bool {
    seq <= next && len as usize <= max && offset <= size && u64::from(len) <= size - offset
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == if len as int <= u32::MAX { Some(len as u32) } else { None }
))]
pub(super) fn stored_length(len: usize) -> Option<u32> {
    u32::try_from(len).ok()
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if len as int <= 4294967295 && offset as int + len as int <= 18446744073709551615 {
        Some((len as u32, (offset as int + len as int) as u64))
    } else {
        None
    }
))]
pub(super) fn place_extent(offset: u64, len: usize) -> Option<(u32, u64)> {
    let len = stored_length(len)?;
    let end = offset.checked_add(u64::from(len))?;
    Some((len, end))
}
