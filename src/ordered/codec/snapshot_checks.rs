use crate::ordered::{
    admission,
    receipt::{Receipt, ReceiptBook, RetainedOutcome},
};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::OrdSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::{btree::*, iter::IteratorSpec};

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn generationInRange(epoch: int, generation: int) -> bool {
    0 < generation && generation <= if epoch < 1 { 1 } else { epoch }
}

pub(crate) open spec fn leaseRowValid(
    serial: int,
    last_serial: int,
    retained: bool,
    lease_end: int,
    duration: int,
    time: int,
    key_increases: bool,
) -> bool {
    0 < serial <= last_serial
        && retained
        && duration <= lease_end <= time + duration
        && key_increases
}

pub(crate) open spec fn fenceRowValid(
    position: int,
    last_position: int,
    time: int,
    last_time: int,
    key_increases: bool,
) -> bool {
    0 < position <= last_position && time <= last_time && key_increases
}

pub(crate) open spec fn holdReceiptMatches(admitted_at: u64, receipt_position: Option<u64>) -> bool {
    receipt_position == Some(admitted_at)
}

pub(crate) open spec fn rootReferenceRowValid(revision: u64, previous: Option<u64>, known: bool) -> bool {
    known && oldRootKeyIncreases(revision, previous)
}

pub(crate) open spec fn oldRootKeyIncreases(revision: u64, previous: Option<u64>) -> bool {
    match previous {
        Some(key) => key < revision,
        None => true,
    }
}

pub(crate) open spec fn objectControlTrailerCanonical(present: bool, roots: usize, fences: usize) -> bool {
    present == (roots != 0 || fences != 0)
}

pub(crate) open spec fn receiptPositionFresh(positions: Set<u64>, position: u64) -> bool {
    !positions.contains(position)
}

pub(crate) open spec fn receiptRowValid(
    snapshot_position: u64, decision_position: u64, expires_at: u64, retry_horizon: u64,
    nonce_present: bool, owns_live_hold: bool,
) -> bool {
    nonce_present && 0 < decision_position <= snapshot_position
        && decision_position < expires_at
        && expires_at as int - decision_position <= retry_horizon
        && (snapshot_position < expires_at || owns_live_hold)
}

pub(crate) open spec fn receiptPartition<P, I, K, A>(
    book: Map<(I, K), RetainedOutcome<Receipt<P, I, K, A>>>, positions: Set<u64>,
) -> bool {
    &&& forall|key: (I, K)| #[trigger] book.contains_key(key) ==> {
        let row = book[key].receipt;
        key == (row.principal, row.request) && positions.contains(row.position)
    }
    &&& forall|left: (I, K), right: (I, K)|
        #[trigger] book.contains_key(left) && #[trigger] book.contains_key(right) && left != right
        ==> book[left].receipt.position != book[right].receipt.position
    &&& forall|position: u64| #[trigger] positions.contains(position) ==> exists|key: (I, K)|
        #[trigger] book.contains_key(key) && book[key].receipt.position == position
}

pub(crate) open spec fn receiptExpiryPartition<P, I, K, A>(
    book: Map<(I, K), RetainedOutcome<Receipt<P, I, K, A>>>,
    expiry: Map<(u64, (I, K)), ()>,
    now: u64,
    expires: spec_fn(K) -> u64,
) -> bool {
    forall|entry: (u64, (I, K))| #[trigger] expiry.contains_key(entry)
        <==> book.contains_key(entry.1) && entry.0 == expires(entry.1.1) && now < entry.0
}

pub(crate) open spec fn lastSnapshotKey<K: Ord, V>(rows: Map<K, V>, last: Option<K>) -> bool {
    match last {
        None => rows.is_empty(),
        Some(last) => rows.contains_key(last) && forall|key: K| #[trigger] rows.contains_key(key)
            ==> last.cmp_spec(&key) != Ordering::Less,
    }
}

pub(super) open spec fn allSnapshotRowsValid<Row>(rows: Set<Row>, passing: Set<Row>) -> bool {
    forall|row: Row| #[trigger] rows.contains(row) ==> passing.contains(row)
}

pub(super) open spec fn checksSnapshotRow<Row, Check: Fn(&Row) -> bool>(
    check: Check, passing: Set<Row>,
) -> bool {
    &&& forall|row: &Row| #[trigger] call_requires(check, (row,))
    &&& forall|row: &Row, actual: bool| #[trigger] call_ensures(check, (row,), actual)
        ==> actual == passing.contains(*row)
}

// Order-preserving encodings of composite keys are mathematical integers.
// Each per-row observation is supplied by a projection of the named State
// fields. In particular, a hold receipt position is present only after exact
// origin, identity, outcome kind and hold equality checks.
pub(crate) ghost struct ReducerImage {
    pub position: u64,
    pub time: u64,
    pub epoch: u64,
    pub generation: u64,
    pub enrollment_serial: u64,
    pub lease_duration: u64,
    pub current_grant: Option<(u64, u64, bool)>,
    pub roster_keys: Seq<int>,
    pub old_root_keys: Seq<int>,
    pub hold_keys: Seq<int>,
    pub receipt_keys: Seq<int>,
    pub lease_keys: Seq<int>,
    pub root_reference_keys: Seq<int>,
    pub fence_keys: Seq<int>,
    pub roster_limit: nat,
    pub old_root_limit: nat,
    pub ordinary_hold_limit: nat,
    pub activation_hold_limit: nat,
    pub retry_horizon: nat,
    pub lease_limit: nat,
    pub root_reference_limit: nat,
    pub fence_limit: nat,
    pub ordinary_holds: nat,
    pub activation_holds: nat,
    pub hold_receipts: Seq<(u64, Option<u64>)>,
    pub receipt_positions: Seq<u64>,
    pub leases: Seq<(u64, u64, bool)>,
    pub known_root_references: Seq<bool>,
    pub fences: Seq<(u64, u64)>,
    pub complete_references: bool,
    pub withdrawal_receipts_match: bool,
    pub references: Seq<Seq<int>>,
    pub object_control_used: nat,
    pub object_control_capacity: nat,
}

pub(crate) open spec fn strictlyIncreasingKeys(keys: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < keys.len()
        ==> (#[trigger] keys[i]) < (#[trigger] keys[j])
}

pub(crate) open spec fn boundedMap(keys: Seq<int>, limit: nat) -> bool {
    keys.len() <= limit && strictlyIncreasingKeys(keys)
}

pub(crate) open spec fn receiptPositionsUnique(positions: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < positions.len()
        ==> (#[trigger] positions[i]) != (#[trigger] positions[j])
}

pub(crate) open spec fn reducerInvariant(image: ReducerImage) -> bool {
    &&& generationInRange(image.epoch as int, image.generation as int)
    &&& match image.current_grant {
        Some((epoch, generation, enrolled)) => enrolled && 0 < epoch
            && epoch == image.epoch && generation == image.generation,
        None => true,
    }
    &&& boundedMap(image.roster_keys, image.roster_limit)
    &&& boundedMap(image.old_root_keys, image.old_root_limit)
    &&& boundedMap(image.hold_keys, image.ordinary_hold_limit + image.activation_hold_limit)
    &&& image.ordinary_holds <= image.ordinary_hold_limit
    &&& image.activation_holds <= image.activation_hold_limit
    &&& image.hold_keys.len() == image.ordinary_holds + image.activation_holds
    &&& boundedMap(image.receipt_keys,
        image.retry_horizon + image.ordinary_hold_limit + image.activation_hold_limit)
    &&& boundedMap(image.lease_keys, image.lease_limit)
    &&& boundedMap(image.root_reference_keys, image.root_reference_limit)
    &&& boundedMap(image.fence_keys, image.fence_limit)
    &&& image.hold_receipts.len() == image.hold_keys.len()
    &&& forall|i: int| 0 <= i < image.hold_receipts.len() ==> {
        let row = #[trigger] image.hold_receipts[i];
        holdReceiptMatches(row.0, row.1)
    }
    &&& image.receipt_positions.len() == image.receipt_keys.len()
    &&& receiptPositionsUnique(image.receipt_positions)
    &&& image.leases.len() == image.lease_keys.len()
    &&& forall|i: int| 0 <= i < image.leases.len() ==> {
        let row = #[trigger] image.leases[i];
        leaseRowValid(row.0 as int, image.enrollment_serial as int, row.2, row.1 as int,
            image.lease_duration as int, image.time as int, true)
    }
    &&& image.known_root_references.len() == image.root_reference_keys.len()
    &&& forall|i: int| 0 <= i < image.known_root_references.len()
        ==> #[trigger] image.known_root_references[i]
    &&& image.fences.len() == image.fence_keys.len()
    &&& forall|i: int| 0 <= i < image.fences.len() ==> {
        let row = #[trigger] image.fences[i];
        fenceRowValid(row.0 as int, image.position as int, row.1 as int, image.time as int, true)
    }
    &&& image.object_control_used <= image.object_control_capacity
    &&& image.withdrawal_receipts_match
    &&& image.fence_keys.len() > 0 ==> image.complete_references
    &&& forall|i: int| 0 <= i < image.references.len() ==> {
        let names = #[trigger] image.references[i];
        &&& names.len() <= 16_384
        &&& strictlyIncreasingKeys(names)
        &&& forall|j: int| 0 <= j < names.len()
            ==> names[j] != 0 && !image.fence_keys.contains(#[trigger] names[j])
    }
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == generationInRange(epoch as int, generation as int),
))]
pub(super) fn generation_in_range(epoch: u64, generation: u64) -> bool {
    generation != 0 && generation <= epoch.max(1)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == leaseRowValid(
        serial as int, last_serial as int, retained, lease_end as int, duration as int, time as int, key_increases,
    ),
))]
pub(super) fn lease_row_valid(
    serial: u64,
    last_serial: u64,
    retained: bool,
    lease_end: u64,
    duration: u64,
    time: u64,
    key_increases: bool,
) -> bool {
    serial != 0
        && serial <= last_serial
        && retained
        && lease_end >= duration
        && lease_end <= time.saturating_add(duration)
        && key_increases
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == fenceRowValid(position as int, last_position as int, time as int, last_time as int, key_increases),
))]
pub(super) fn fence_row_valid(
    position: u64,
    last_position: u64,
    time: u64,
    last_time: u64,
    key_increases: bool,
) -> bool {
    position != 0 && position <= last_position && time <= last_time && key_increases
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == holdReceiptMatches(admitted_at, receipt_position),
))]
pub(super) fn hold_receipt_matches(admitted_at: u64, receipt_position: Option<u64>) -> bool {
    match receipt_position {
        Some(position) => admitted_at == position,
        None => false,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == rootReferenceRowValid(revision, previous, known),
))]
pub(super) fn root_reference_row_valid(
    revision: u64,
    previous: Option<u64>,
    known: bool,
) -> bool {
    known && match previous {
        Some(previous) => previous < revision,
        None => true,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == oldRootKeyIncreases(revision, previous),
))]
pub(super) fn old_root_key_increases(revision: u64, previous: Option<u64>) -> bool {
    match previous {
        Some(last) => last < revision,
        None => true,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == objectControlTrailerCanonical(present, roots, fences),
))]
pub(super) fn object_control_trailer_canonical(present: bool, roots: usize, fences: usize) -> bool {
    present == (roots != 0 || fences != 0)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires btree_set_wf(old(positions)),
    ensures btree_set_wf(final(positions)),
        out == receiptPositionFresh(old(positions)@, position),
        final(positions)@ == old(positions)@.insert(position),
))]
pub(super) fn insert_receipt_position(positions: &mut BTreeSet<u64>, position: u64) -> bool {
    positions.insert(position)
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires btree_map_inv(old(rows)), obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(),
    ensures btree_map_inv(final(rows)), final(rows)@ == old(rows)@.insert(key, row),
))]
pub(super) fn insert_snapshot_row<K: Ord, Row>(rows: &mut BTreeMap<K, Row>, key: K, row: Row) {
    rows.insert(key, row);
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires btree_map_inv(old(outcomes)), btree_map_inv(old(expiry)), btree_set_wf(old(positions)),
        obeys_cmp::<(I, K)>(), obeys_cmp_concrete_eq::<(I, K)>(),
        obeys_cmp::<(u64, (I, K))>(), obeys_cmp_concrete_eq::<(u64, (I, K))>(),
        receiptPartition(old(outcomes)@, old(positions)@),
        receiptExpiryPartition(old(outcomes)@, old(expiry)@, snapshot_position, expires@),
        expires_at == expires@(receipt.request),
        lastSnapshotKey(old(outcomes)@, *old(previous)),
    ensures
        btree_map_inv(final(outcomes)), btree_map_inv(final(expiry)), btree_set_wf(final(positions)),
        receiptPartition(final(outcomes)@, final(positions)@),
        receiptExpiryPartition(final(outcomes)@, final(expiry)@, snapshot_position, expires@),
        lastSnapshotKey(final(outcomes)@, *final(previous)),
        *final(previous) == if out { Some((receipt.principal, receipt.request)) } else { *old(previous) },
        out == (receiptRowValid(snapshot_position, receipt.position, expires_at, retry_horizon,
            nonce_present, owns_live_hold)
            && receiptPositionFresh(old(positions)@, receipt.position)
            && match *old(previous) {
                Some(last) => last.cmp_spec(&(receipt.principal, receipt.request)) == Ordering::Less,
                None => true,
            }),
        out ==> !old(outcomes)@.contains_key((receipt.principal, receipt.request)),
        final(outcomes)@ == if out {
            old(outcomes)@.insert((receipt.principal, receipt.request), RetainedOutcome { fingerprint, receipt })
        } else { old(outcomes)@ },
        final(expiry)@ == if out && snapshot_position < expires_at {
            old(expiry)@.insert((expires_at, (receipt.principal, receipt.request)), ())
        } else { old(expiry)@ },
))]
pub(super) fn insert_snapshot_receipt<P, I: Ord + Copy, K: Ord + Copy, A>(
    outcomes: &mut ReceiptBook<P, I, K, A>,
    expiry: &mut BTreeMap<(u64, (I, K)), ()>,
    positions: &mut BTreeSet<u64>,
    previous: &mut Option<(I, K)>,
    snapshot_position: u64,
    retry_horizon: u64,
    expires_at: u64,
    nonce_present: bool,
    owns_live_hold: bool,
    receipt: Receipt<P, I, K, A>,
    fingerprint: [u8; 32],
    #[cfg(verus_keep_ghost)] expires: Ghost<FnSpec<(K,), u64>>,
) -> bool {
    let key = (receipt.principal, receipt.request);
    let position = receipt.position;
    if !nonce_present
        || position == 0
        || position > snapshot_position
        || position >= expires_at
        || expires_at - position > retry_horizon
        || !admission::retains_receipt(snapshot_position, expires_at, owns_live_hold)
    {
        return false;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = outcomes@;
        let ghost seen = positions@;
        let ghost last_key = *previous;
        let ghost old_expiry = expiry@;
    }
    if let Some(last) = *previous {
        let order = last.cmp(&key);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(vstd::laws_cmp::obeys_cmp_ord);
            assert(order == last.cmp_spec(&key));
        }
        if !matches!(order, Ordering::Less) {
            return false;
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(lastSnapshotKey(before, last_key));
        if before.contains_key(key) {
            let last = last_key.unwrap();
            assert(last.cmp_spec(&key) != Ordering::Less);
        }
        assert(!before.contains_key(key));
    }
    if !insert_receipt_position(positions, position) {
        return false;
    }
    if expires_at > snapshot_position {
        insert_snapshot_row(expiry, (expires_at, key), ());
    }
    insert_snapshot_row(outcomes, key, RetainedOutcome { fingerprint, receipt });
    *previous = Some(key);
    #[cfg(verus_keep_ghost)]
    proof! {
        use vstd::laws_cmp::{obeys_cmp_ord, obeys_partial_cmp_spec_properties};
        use vstd::std_specs::cmp::PartialOrdSpec;
        reveal(obeys_cmp_ord);
        reveal(obeys_partial_cmp_spec_properties);
        assert(!before.contains_key(key));
        assert forall|other: (I, K)| #[trigger] outcomes@.contains_key(other)
            implies key.cmp_spec(&other) != Ordering::Less by {
            if other != key {
                assert(before.contains_key(other));
                let last = last_key.unwrap();
                assert(last.cmp_spec(&other) != Ordering::Less);
                assert(last.cmp_spec(&key) == Ordering::Less);
                if other != last {
                    assert(other.partial_cmp_spec(&last) == Some(Ordering::Less));
                    assert(last.partial_cmp_spec(&key) == Some(Ordering::Less));
                    assert(other.partial_cmp_spec(&key) == Some(Ordering::Less));
                }
                assert(other.cmp_spec(&key) == Ordering::Less);
                assert(key.partial_cmp_spec(&other) == Some(Ordering::Greater));
            }
        }
        assert forall|other: (I, K)| #[trigger] outcomes@.contains_key(other) implies {
            let row = outcomes@[other].receipt;
            other == (row.principal, row.request) && positions@.contains(row.position)
        } by {
            if other != key {
                assert(before.contains_key(other));
            }
        }
        assert forall|left: (I, K), right: (I, K)|
            #[trigger] outcomes@.contains_key(left) && #[trigger] outcomes@.contains_key(right)
                && left != right
            implies outcomes@[left].receipt.position != outcomes@[right].receipt.position by {
            if left != key {
                assert(before.contains_key(left));
                assert(seen.contains(before[left].receipt.position));
            }
            if right != key {
                assert(before.contains_key(right));
                assert(seen.contains(before[right].receipt.position));
            }
        }
        assert forall|p: u64| #[trigger] positions@.contains(p) implies exists|other: (I, K)|
            #[trigger] outcomes@.contains_key(other) && outcomes@[other].receipt.position == p by {
            if p == position {
                assert(outcomes@.contains_key(key) && outcomes@[key].receipt.position == p);
            } else {
                assert(seen.contains(p));
                let other = choose|other: (I, K)|
                    #[trigger] before.contains_key(other) && before[other].receipt.position == p;
                assert(outcomes@.contains_key(other) && outcomes@[other].receipt.position == p);
            }
        }
        assert forall|entry: (u64, (I, K))| #[trigger] expiry@.contains_key(entry)
            <==> outcomes@.contains_key(entry.1) && entry.0 == expires@(entry.1.1)
                && snapshot_position < entry.0 by {
            assert(old_expiry.contains_key(entry)
                == (before.contains_key(entry.1) && entry.0 == expires@(entry.1.1)
                    && snapshot_position < entry.0));
        }
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires btree_map_wf(rows), obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(),
        checksSnapshotRow(valid, passing@),
    ensures out == allSnapshotRowsValid(rows@.values(), passing@),
))]
pub(super) fn all_snapshot_rows<K: Ord, Row>(
    rows: &BTreeMap<K, Row>,
    valid: impl Fn(&Row) -> bool,
    #[cfg(verus_keep_ghost)] passing: Ghost<Set<Row>>,
) -> bool {
    let mut values = rows.values();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = values.remaining(); }
    let accepted = values.all(valid);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(before.unref().to_set() =~= rows@.values());
        if accepted {
            assert forall|row: Row| #[trigger] rows@.values().contains(row) implies
                passing@.contains(row) by {
                assert(before.unref().to_set().contains(row));
                let i = choose|i: int| 0 <= i < before.len() && #[trigger] before.unref()[i] == row;
                assert(*before[i] == row);
                assert(call_ensures(valid, (before[i],), true));
            }
        } else {
            let i = choose|i: int| 0 <= i < before.len()
                && call_ensures(valid, (#[trigger] before[i],), false);
            assert(before.unref()[i] == *before[i]);
            assert(before.unref().contains(*before[i]));
            assert(before.unref().to_set().contains(*before[i]));
            assert(rows@.values().contains(*before[i]));
            assert(!passing@.contains(*before[i]));
        }
    }
    accepted
}
