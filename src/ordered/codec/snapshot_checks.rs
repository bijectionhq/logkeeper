use std::collections::BTreeMap;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
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
    known && match previous {
        Some(key) => key < revision,
        None => true,
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
