#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (issued == received)
))]
pub(super) fn matches_ticket(issued: u64, received: u64) -> bool {
    issued == received
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (if previous == u64::MAX { None } else { Some((previous + 1) as u64) })
))]
pub(super) fn next_ticket(previous: u64) -> Option<u64> {
    if previous == u64::MAX {
        None
    } else {
        Some(previous + 1)
    }
}
