//! Acceptance and repair predicates for an ordered voter cohort.

use super::admission::matches_fingerprint;

pub(super) fn accept_quorum(accepted: usize, members: usize) -> bool {
    accepted >= members / 2 + 1
}

pub(super) fn may_extend<G>(successor: Option<G>) -> bool {
    successor.is_none()
}

pub(super) fn matches_chosen_seal(successor: Option<&[u8; 32]>, destination: &[u8; 32]) -> bool {
    match successor {
        Some(target) => matches_fingerprint(target, destination),
        None => false,
    }
}
