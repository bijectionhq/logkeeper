use crate::production::{
    admit_object_references, fence_map, has_live_reference, install_fence, referenced, row_matches,
    withdraw_object,
};
use crate::Refusal;
use std::collections::{BTreeMap, VecDeque};
use vstd::prelude::*;
use vstd::std_specs::btree::btree_map_wf;

verus! {

pub open spec fn fenced<K, F>(fences: Map<K, F>, name: K) -> bool {
    fences.contains_key(name)
}

pub open spec fn canAdmitReferences<K, F>(fences: Map<K, F>, names: Seq<K>) -> bool {
    forall|i: int| 0 <= i < names.len() ==> !fenced(fences, #[trigger] names[i])
}

pub open spec fn canWithdraw(known: bool, present: bool) -> bool {
    known && !present
}

// LAW FENCED-NAMES-REFUSE-NEW-REFERENCES.
pub fn fenced_refuses_reference<K: Ord, F>(
    fences: &BTreeMap<K, F>, names: &[K], index: usize,
)
    requires
        fence_map(fences),
        index < names@.len(),
        fenced(fences@, names@[index as int]),
{
    let result = admit_object_references(Some(names), true, fences);
    assert(!canAdmitReferences(fences@, names@));
    if let Ok(()) = result {
        assert(!fences@.contains_key(names@[index as int]));
    }
}

// LAW A-FENCE-REFUSES-OPAQUE-REFERENCES.
pub fn fenced_refuses_opaque_references<K: Ord, F>(fences: &BTreeMap<K, F>, name: K)
    requires fence_map(fences), fenced(fences@, name),
{
    let result = admit_object_references(None, true, fences);
    assert(result == Err(Refusal::Unavailable));
}

// LAW REFERENCED-NAMES-REFUSE-WITHDRAWAL.
pub fn referenced_refuses_withdrawal<K: Ord, F: Copy, R>(
    fences: &BTreeMap<K, F>, name: &K, known: bool, roots: &BTreeMap<u64, Vec<K>>,
    records: &VecDeque<R>, in_root: impl Fn(&Vec<K>) -> bool, in_record: impl Fn(&R) -> bool,
    Ghost(root_members): Ghost<Set<Vec<K>>>, Ghost(record_members): Ghost<Set<R>>,
)
    requires
        fence_map(fences),
        !fenced(fences@, *name),
        btree_map_wf(roots),
        row_matches(in_root, root_members),
        row_matches(in_record, record_members),
{
    let present = has_live_reference(roots, records, in_root, in_record,
        Ghost(root_members), Ghost(record_members));
    let exact = |_fence: &F| -> (out: bool) ensures !out { false };
    let complete = || -> (out: bool) ensures out == known { known };
    let has_reference = || -> (out: bool) ensures out == present { present };
    let result = withdraw_object(fences, name, true, exact, complete, has_reference,
        Ghost(known), Ghost(present), Ghost(false));
    assert((result == Ok(None)) == canWithdraw(known,
        referenced(roots@, records@, root_members, record_members)));
}

// LAW EXACT-RETRY-RETURNS-THE-ORIGINAL-FENCE.
pub fn retry_withdrawal_matches_version<K: Ord>(
    fences: &BTreeMap<K, u64>, name: &K, version: u64,
)
    requires fence_map(fences), fenced(fences@, *name),
{
    let ghost same = version == fences@[*name];
    let exact = |stored: &u64| -> (out: bool)
        ensures out == (*stored == version)
    { *stored == version };
    let complete = || -> (out: bool) ensures !out { false };
    let has_reference = || -> (out: bool) ensures !out { false };
    let outcome = withdraw_object(fences, name, true, exact, complete, has_reference,
        Ghost(false), Ghost(false), Ghost(same));
    assert(outcome == if same { Ok(Some(fences@[*name])) } else { Err(Refusal::Conflict) });
}

// LAW A-FRESH-WITHDRAWAL-FENCES-ONLY-THAT-NAME.
pub fn withdrawn_name_stays_fenced<K: Ord + Copy, F: Copy>(
    fences: &mut BTreeMap<K, F>, names: &[K], index: usize, fence: F, present: bool,
)
    requires
        fence_map(old(fences)),
        index < names@.len(),
        !fenced(old(fences)@, names@[index as int]),
{
    let ghost prior = fences@;
    let name = names[index];
    let exact = |_stored: &F| -> (out: bool) ensures !out { false };
    let complete = || -> (out: bool) ensures out { true };
    let has_reference = || -> (out: bool) ensures out == present { present };
    let selected = withdraw_object(fences, &name, true, exact, complete, has_reference,
        Ghost(true), Ghost(present), Ghost(false));
    if let Ok(None) = selected {
        assert(!present);
        install_fence(fences, name, fence);
        assert(fenced(fences@, name));
        assert(fences@[name] == fence);
        assert forall|other: K| other != name implies
            #[trigger] fenced(fences@, other) == fenced(prior, other) by {
            if fenced(prior, other) {
                assert(fences@[other] == prior[other]);
            }
        }
        let late = admit_object_references(Some(names), true, fences);
        assert(late == Err(Refusal::Conflict));
    }

}

}
