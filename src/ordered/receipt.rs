//! Receipt replay and persistence decisions shared by the ordered reducer.

use super::Refusal;
use super::admission;
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
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

#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::btree_map_inv;

pub(super) fn require_original_placement<P: Eq>(original: P, installed: P) -> Result<(), Refusal> {
    if original != installed {
        return Err(Refusal::WrongPlacement);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if stored@ == presented@ { Some(original) } else { None },
))]
pub(super) fn replay_mutation<R: Copy>(stored: &[u8], presented: &[u8], original: R) -> Option<R> {
    if admission::matches_fingerprint(stored, presented) {
        Some(original)
    } else {
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if !reading && stored@ == presented@ { Some(original) } else { None },
))]
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

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_cmp::<(I, K)>(), obeys_cmp_concrete_eq::<(I, K)>(), btree_map_inv(old(outcomes)),
    ensures
        out == (!reading || receipt.outcome is Ok),
        final(outcomes)@ == if out {
            old(outcomes)@.insert((receipt.principal, receipt.request), RetainedOutcome { fingerprint, receipt })
        } else {
            old(outcomes)@
        },
))]
pub(super) fn record_after_apply<P, I: Ord + Copy, K: Ord + Copy, O: Copy, E: Copy>(
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

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(outcomes)),
    ensures final(outcomes)@ == if position < expires_at || owns_live_hold {
        old(outcomes)@
    } else {
        old(outcomes)@.remove(key)
    },
))]
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
