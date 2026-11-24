//! Acceptance and repair predicates for an ordered voter cohort.

use super::admission::matches_fingerprint;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == ((members as int) < 2 * accepted as int),
))]
pub(super) fn accept_quorum(accepted: usize, members: usize) -> bool {
    accepted >= members / 2 + 1
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (successor is None),
))]
pub(super) fn may_extend<G>(successor: Option<G>) -> bool {
    successor.is_none()
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (successor matches Some(target) && target@ == destination@),
))]
pub(super) fn matches_chosen_seal(successor: Option<&[u8; 32]>, destination: &[u8; 32]) -> bool {
    match successor {
        Some(target) => matches_fingerprint(target, destination),
        None => false,
    }
}

#[cfg(any(feature = "ordered-daemon", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (paid >= quorum),
))]
pub(super) fn has_paid_repair_quorum(paid: usize, quorum: usize) -> bool {
    paid >= quorum
}
