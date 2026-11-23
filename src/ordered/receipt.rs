//! Receipt replay and persistence decisions shared by the ordered reducer.

use super::admission;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receipt<P, I, K, A> {
    pub placement: P,
    pub principal: I,
    pub request: K,
    pub position: u64,
    pub outcome: A,
}

#[derive(Clone)]
pub(super) struct RetainedOutcome<R> {
    pub(super) fingerprint: [u8; 32],
    pub(super) receipt: R,
}

pub(super) type ReceiptBook<P, I, K, A> = BTreeMap<(I, K), RetainedOutcome<Receipt<P, I, K, A>>>;

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

pub(super) fn record_after_apply<P, I: Ord + Copy, K: Ord + Copy, O, E>(
    outcomes: &mut ReceiptBook<P, I, K, Result<O, E>>,
    reading: bool,
    fingerprint: [u8; 32],
    receipt: Receipt<P, I, K, Result<O, E>>,
) -> bool {
    if reading && receipt.outcome.is_err() {
        return false;
    }
    outcomes.insert(
        (receipt.principal, receipt.request),
        RetainedOutcome {
            fingerprint,
            receipt,
        },
    );
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
