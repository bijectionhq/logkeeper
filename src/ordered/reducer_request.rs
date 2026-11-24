//! Retry admission and receipt scheduling for the ordered reducer.

use super::Refusal;
use super::cohort;
use super::receipt::{self, Receipt, ReceiptBook, RetainedOutcome};
use std::collections::BTreeMap;

#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::btree_map_inv;

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn lateRefusal(position: u64, expires_at: u64, sealed: bool, horizon: u64)
    -> Option<Refusal> {
    if expires_at <= position { Some(Refusal::Expired) }
    else if sealed { Some(Refusal::CohortSealed) }
    else if expires_at as int - position > horizon { Some(Refusal::Invalid) }
    else { None }
}

pub(super) open spec fn cachedReceipt<R>(reading: bool, stored: Seq<u8>, presented: Seq<u8>,
    original: R) -> Result<Option<R>, Refusal> {
    if !reading && stored == presented { Ok(Some(original)) }
    else { Err(Refusal::Conflict) }
}

pub(super) open spec fn should_record<O>(reading: bool, applied: Result<O, Refusal>) -> bool {
    !reading || applied is Ok
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(book),
    ensures out == match book@.get(*key) {
        Some(previous) => cachedReceipt(reading, previous.fingerprint@, fingerprint@, previous.receipt),
        None => match lateRefusal(position, expires_at, successor.is_some(), horizon) {
            Some(reason) => Err(reason),
            None => Ok(None),
        },
    },
))]
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

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        obeys_cmp::<(I, K)>(), obeys_cmp_concrete_eq::<(I, K)>(), btree_map_inv(old(book)),
        obeys_cmp::<(u64, (I, K))>(), obeys_cmp_concrete_eq::<(u64, (I, K))>(), btree_map_inv(old(expiry)),
    ensures
        final(book)@ == if should_record(reading, applied.outcome) {
            old(book)@.insert((applied.principal, applied.request), RetainedOutcome { fingerprint, receipt: applied })
        } else { old(book)@ },
        final(expiry)@ == if should_record(reading, applied.outcome) {
            old(expiry)@.insert((expires_at, (applied.principal, applied.request)), ())
        } else { old(expiry)@ },
))]
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
