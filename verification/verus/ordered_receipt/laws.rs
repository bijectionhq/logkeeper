use crate::admission::retains_receipt as retain_at_position;
use crate::production::{
    Receipt, ReceiptBook, RetainedOutcome, record_after_apply as insert_applied, remove_expired,
    replay as reissue, replay_mutation as reissue_mutation,
};
use std::collections::BTreeMap;
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
use vstd::prelude::*;
use vstd::std_specs::btree::btree_map_inv;

verus! {

// Logkeeper.Protocol.Ordered.abstract_book
pub(super) open spec fn abstract_book<K, R>(book: Map<K, RetainedOutcome<R>>, key: K)
    -> Option<([u8; 32], R)>
{
    if book.contains_key(key) {
        Some((book[key].fingerprint, book[key].receipt))
    } else {
        None
    }
}

// Logkeeper.Protocol.Ordered.replay_mutation
pub open spec fn replay_mutation<R>(stored: Seq<u8>, presented: Seq<u8>, original: R)
    -> Option<R>
{
    if stored == presented { Some(original) } else { None }
}

// Logkeeper.Protocol.Ordered.replay
pub open spec fn replay<R>(reading: bool, stored: Seq<u8>, presented: Seq<u8>, original: R)
    -> Option<R>
{
    if reading { None } else { replay_mutation(stored, presented, original) }
}

// Logkeeper.Protocol.Ordered.record_after_apply
pub open spec fn record_after_apply<O, E>(reading: bool, applied: Result<O, E>) -> bool {
    !reading || applied is Ok
}

// Logkeeper.Protocol.Ordered.retain_applied
pub open spec fn retain_applied<O, E>(reading: bool, applied: Result<O, E>)
    -> Option<Result<O, E>>
{
    if record_after_apply(reading, applied) { Some(applied) } else { None }
}

// Logkeeper.Protocol.Ordered.retains_receipt
pub open spec fn retains_receipt(position: int, expires_at: int, owns_live_hold: bool)
    -> bool
{
    position < expires_at || owns_live_hold
}

pub fn barriers_never_replay<R: Copy>(stored: &[u8], offered: &[u8], original: R) {
    let result = reissue(true, stored, offered, original);
    assert(result == replay(true, stored@, offered@, original));
}

pub fn mutation_retry_exact<R: Copy>(stored: &[u8], offered: &[u8], original: R) {
    let apply = reissue(false, stored, offered, original);
    let lookup = reissue_mutation(stored, offered, original);
    assert(apply == replay(false, stored@, offered@, original)
        && lookup == replay_mutation(stored@, offered@, original));
}

pub fn mutation_receipt_within_horizon<R: Copy>(
    position: u64, expires_at: u64, owns_live_hold: bool, fingerprint: &[u8], original: R,
)
    requires position < expires_at,
{
    let retained = retain_at_position(position, expires_at, owns_live_hold);
    assert(retained && retains_receipt(position as int, expires_at as int, owns_live_hold));
    let reissued = reissue(false, fingerprint, fingerprint, original);
    assert(reissued == Some(original));
}

pub fn expired_receipt_without_hold(position: u64, expires_at: u64)
    requires expires_at <= position,
{
    let retained = retain_at_position(position, expires_at, false);
    assert(!retained && !retains_receipt(position as int, expires_at as int, false));
}

pub(super) fn expiry_preserves_recoverable_receipts<K: Ord + Copy, R>(
    book: &mut BTreeMap<K, RetainedOutcome<R>>,
    key: K, position: u64, expires_at: u64, owns_live_hold: bool,
)
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(book)),
{
    let ghost before = book@;
    remove_expired(book, key, position, expires_at, owns_live_hold);
    assert(book@ == if retains_receipt(position as int, expires_at as int, owns_live_hold) {
        before
    } else {
        before.remove(key)
    });
}

pub(super) fn recording_uses_the_applied_outcome<P, I: Ord + Copy, K: Ord + Copy, O, E>(
    book: &mut ReceiptBook<P, I, K, Result<O, E>>,
    reading: bool, receipt: Receipt<P, I, K, Result<O, E>>, fingerprint: [u8; 32],
)
    requires obeys_cmp::<(I, K)>(), obeys_cmp_concrete_eq::<(I, K)>(), btree_map_inv(old(book)),
{
    let ghost before = book@;
    let ghost key = (receipt.principal, receipt.request);
    let record = insert_applied(book, reading, fingerprint, receipt);
    let ghost projected = abstract_book(book@, key);
    let ghost inserted = if record && projected is Some {
        Some(projected.unwrap().1.outcome)
    } else {
        None
    };
    assert(record == record_after_apply(reading, receipt.outcome) && book@ == (if record {
        before.insert(key, RetainedOutcome { fingerprint, receipt })
    } else {
        before
    }) && (record ==> projected == Some((fingerprint, receipt)))
        && inserted == retain_applied(reading, receipt.outcome));
}

}
