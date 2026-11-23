//! Receipt replay and persistence decisions shared by the ordered reducer.

use super::admission;

pub(super) fn replay_mutation<R: Copy>(stored: &[u8], presented: &[u8], original: R) -> Option<R> {
    admission::matches_fingerprint(stored, presented).then_some(original)
}

pub(super) fn replay<R: Copy>(
    reading: bool,
    stored: &[u8],
    presented: &[u8],
    original: R,
) -> Option<R> {
    if reading {
        return None;
    }
    replay_mutation(stored, presented, original)
}

pub(super) fn record_after_apply<O, E>(reading: bool, applied: &Result<O, E>) -> bool {
    !reading || applied.is_ok()
}
