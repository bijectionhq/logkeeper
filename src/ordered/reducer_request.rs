//! Retry admission and receipt scheduling for the ordered reducer.

use super::Refusal;
use super::cohort;
use super::receipt::{self, Receipt, ReceiptBook, RetainedOutcome};
use std::collections::BTreeMap;

#[allow(clippy::too_many_arguments)]
pub(super) fn admit_request<K: Ord, R: Copy, S>(
    book: &BTreeMap<K, RetainedOutcome<R>>,
    key: &K,
    reading: bool,
    fingerprint: &[u8; 32],
    position: u64,
    expires_at: u64,
    successor: Option<S>,
    horizon: u64,
) -> Result<Option<R>, Refusal> {
    if let Some(previous) = book.get(key) {
        // The original read receipt supplies provenance for its hold. The
        // spent identity cannot replay it or overwrite it with a new read.
        let replayed = receipt::replay(
            reading,
            &previous.fingerprint,
            fingerprint,
            previous.receipt,
        );
        return match replayed {
            Some(original) => Ok(Some(original)),
            None => Err(Refusal::Conflict),
        };
    }
    if receipt::fresh_request_expired(position, expires_at) {
        return Err(Refusal::Expired);
    }
    if !cohort::may_extend(successor) {
        return Err(Refusal::CohortSealed);
    }
    if expires_at - position > horizon {
        return Err(Refusal::Invalid);
    }
    Ok(None)
}

pub(super) fn finish_request<P, I: Ord + Copy, K: Ord + Copy, O: Copy>(
    book: &mut ReceiptBook<P, I, K, Result<O, Refusal>>,
    expiry: &mut BTreeMap<(u64, (I, K)), ()>,
    reading: bool,
    fingerprint: [u8; 32],
    applied: Receipt<P, I, K, Result<O, Refusal>>,
    expires_at: u64,
) {
    let key = (applied.principal, applied.request);
    // Only an admitted read leaves a receipt, as provenance for its hold.
    if receipt::record_after_apply(book, reading, fingerprint, applied) {
        expiry.insert((expires_at, key), ());
    }
}
