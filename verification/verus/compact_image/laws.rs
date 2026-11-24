use crate::production::{
    fence_row_valid, generation_in_range, hold_receipt_matches, lease_row_valid,
    root_reference_row_valid, all_snapshot_rows, checksSnapshotRow,
    insert_receipt_position, insert_snapshot_receipt, insert_snapshot_row,
    object_control_trailer_canonical, old_root_key_increases, receiptExpiryPartition, receiptPartition,
    ReducerImage, reducerInvariant, receiptPositionsUnique,
};
use vstd::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use crate::receipt::Receipt;
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
use vstd::std_specs::btree::*;

verus! {

fn vacant_generation_obeys_epoch(epoch: u64, generation: u64) {
    let accepted = generation_in_range(epoch, generation);
    assert(accepted ==> generation != 0 && (epoch == 0 ==> generation == 1));
}

fn accepted_lease_has_retained_owner_and_bounds(
    serial: u64,
    last_serial: u64,
    retained: bool,
    lease_end: u64,
    duration: u64,
    time: u64,
    key_increases: bool,
) {
    let accepted = lease_row_valid(serial, last_serial, retained, lease_end, duration, time, key_increases);
    assert(accepted ==> retained && duration <= lease_end as int <= time as int + duration);
    assert(accepted ==> 0 < serial <= last_serial && key_increases);
}

fn accepted_fence_has_bounded_coordinates(
    position: u64,
    last_position: u64,
    time: u64,
    last_time: u64,
    key_increases: bool,
) {
    let accepted = fence_row_valid(position, last_position, time, last_time, key_increases);
    assert(accepted ==> 0 < position <= last_position && time <= last_time && key_increases);
}

fn a_checked_hold_has_a_matching_receipt(admitted_at: u64, receipt: Option<u64>) {
    let accepted = hold_receipt_matches(admitted_at, receipt);
    assert(accepted ==> receipt == Some(admitted_at));
}

fn accepted_reference_has_known_root_and_increasing_key(revision: u64, previous: u64, known: bool) {
    let accepted = root_reference_row_valid(revision, Some(previous), known);
    assert(accepted ==> known && previous < revision);
}

fn accepted_old_root_rows_are_in_revision_order(revision: u64, previous: Option<u64>) {
    let accepted = old_root_key_increases(revision, previous);
    assert(accepted ==> match previous {
        Some(key) => key < revision,
        None => true,
    });
}

fn accepted_object_control_trailer_matches_encoder_presence(
    present: bool, roots: usize, fences: usize,
) {
    let accepted = object_control_trailer_canonical(present, roots, fences);
    assert(accepted ==> present == (roots > 0 || fences > 0));
}

fn accepting_a_receipt_preserves_unique_decision_positions(
    positions: &mut BTreeSet<u64>, position: u64, Ghost(decoded): Ghost<Seq<u64>>,
)
    requires btree_set_wf(old(positions)), old(positions)@ == decoded.to_set(),
        receiptPositionsUnique(decoded),
{
    let ghost before = positions@;
    let accepted = insert_receipt_position(positions, position);
    if accepted {
        assert(!decoded.contains(position));
        let ghost next = decoded.push(position);
        assert forall|i: int, j: int| 0 <= i < j < next.len()
            implies (#[trigger] next[i]) != (#[trigger] next[j]) by {
            if j == decoded.len() {
                if decoded[i] == position {
                    assert(decoded.contains(position));
                }
            }
        }
        assert(receiptPositionsUnique(next));
        assert forall|p: u64| positions@.contains(p) <==> #[trigger] next.to_set().contains(p) by {
            assert(positions@.contains(p) == (before.contains(p) || p == position));
            if next.contains(p) {
                let i = choose|i: int| 0 <= i < next.len() && #[trigger] next[i] == p;
                if i < decoded.len() {
                    assert(decoded[i] == p);
                    assert(decoded.contains(p));
                }
            }
            if decoded.contains(p) {
                let i = choose|i: int| 0 <= i < decoded.len() && #[trigger] decoded[i] == p;
                assert(next[i] == p);
                assert(next.contains(p));
            }
            assert(next[decoded.len() as int] == position);
            assert(next.contains(position));
            assert(next.contains(p) == (decoded.contains(p) || p == position));
        }
        assert(positions@ =~= next.to_set());
    }
}

fn one_invalid_hold_prevents_recovery(
    rows: &BTreeMap<u64, (u64, Option<u64>)>,
    check: impl Fn(&(u64, Option<u64>)) -> bool,
    rejected: (u64, Option<u64>),
    Ghost(passing): Ghost<Set<(u64, Option<u64>)>>,
)
    requires
        btree_map_wf(rows),
        checksSnapshotRow(check, passing),
        rows@.values().contains(rejected),
        !passing.contains(rejected),
{
    let accepted = all_snapshot_rows(rows, check, Ghost(passing));
    assert(!accepted);
}

fn insertion_preserves_checked_snapshot_rows<K: Ord + Copy, Row>(
    rows: &mut BTreeMap<K, Row>, key: K, row: Row,
    Ghost(valid): Ghost<spec_fn(K, Row) -> bool>,
)
    requires
        btree_map_inv(old(rows)), obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(),
        valid(key, row),
        forall|stored: K| #[trigger] old(rows)@.contains_key(stored) ==> valid(stored, old(rows)@[stored]),
{
    let ghost before = rows@;
    insert_snapshot_row(rows, key, row);
    assert(rows@[key] == row);
    assert forall|stored: K| #[trigger] rows@.contains_key(stored) implies valid(stored, rows@[stored]) by {
        if stored != key {
            assert(before.contains_key(stored));
        }
    }
}

fn decoded_receipts_use_exact_retry_and_expiry_keys(now: u64, at: u64, until: u64, live_hold: bool)
    requires 0 < at <= now, at < until, now < until || live_hold,
{
    let mut book = BTreeMap::new();
    let mut expiry = BTreeMap::new();
    let mut positions = BTreeSet::new();
    let mut previous = None;
    let receipt = Receipt { placement: (), principal: 1u64, request: (2u64, until), position: at, outcome: () };
    let ghost deadline = |id: (u64, u64)| id.1;
    let accepted = insert_snapshot_receipt(
        &mut book, &mut expiry, &mut positions, &mut previous, now, u64::MAX, until, true, live_hold,
        receipt, [0; 32], Ghost(deadline),
    );
    let ghost key = (receipt.principal, receipt.request);
    assert(accepted);
    assert(book@[key].receipt == receipt);
    assert(expiry@.contains_key((until, key)) == (now < until));
    assert(receiptPartition(book@, positions@));
    assert(receiptExpiryPartition(book@, expiry@, now, deadline));
}

proof fn the_reducer_invariant_excludes_reused_receipt_positions(image: ReducerImage, i: int, j: int)
    requires reducerInvariant(image), 0 <= i < j < image.receipt_positions.len(),
    ensures image.receipt_positions[i] != image.receipt_positions[j],
{
}

}
