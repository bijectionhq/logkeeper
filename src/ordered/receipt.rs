//! Receipt replay and persistence decisions shared by the ordered reducer.

use super::admission;
use std::collections::BTreeMap;

#[derive(Clone)]
pub(super) struct RetainedOutcome<R> {
    pub(super) fingerprint: [u8; 32],
    pub(super) receipt: R,
}

pub(super) fn replay_mutation<R: Copy>(stored: &[u8], presented: &[u8], original: R) -> Option<R> {
    if admission::matches_fingerprint(stored, presented) {
        Some(original)
    } else {
        None
    }
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

pub(super) fn record_after_apply<K: Ord, R, O, E>(
    outcomes: &mut BTreeMap<K, RetainedOutcome<R>>,
    key: K,
    reading: bool,
    applied: &Result<O, E>,
    retained: RetainedOutcome<R>,
) -> bool {
    if reading && applied.is_err() {
        return false;
    }
    outcomes.insert(key, retained);
    true
}

pub(super) fn remove_expired<K: Ord, R>(
    outcomes: &mut BTreeMap<K, RetainedOutcome<R>>,
    key: K,
    position: u64,
    expires_at: u64,
    owns_live_hold: bool,
) {
    if !admission::retains_receipt(position, expires_at, owns_live_hold) {
        outcomes.remove(&key);
    }
}
