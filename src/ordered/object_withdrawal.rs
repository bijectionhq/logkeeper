//! Name-keyed admission, exact retry and fence insertion.

use super::Refusal;
use std::collections::{BTreeMap, VecDeque};

#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::{btree::*, cmp::borrowed_key_ordering_matches, iter::IteratorSpec};

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn fence_map<K: Ord, F>(fences: &BTreeMap<K, F>) -> bool {
        &&& btree_map_inv(fences)
        &&& obeys_cmp::<K>()
        &&& obeys_cmp_concrete_eq::<K>()
        &&& borrowed_key_ordering_matches::<K, K>()
    }

    pub open spec fn no_fenced_names<K, F>(names: Seq<K>, limit: int, fences: Map<K, F>) -> bool {
        forall|i: int| 0 <= i < limit ==> !fences.contains_key(#[trigger] names[i])
    }

    pub open spec fn observes<C: Fn() -> bool>(observe: C, expected: bool) -> bool {
        &&& call_requires(observe, ())
        &&& forall|actual: bool| #[trigger] call_ensures(observe, (), actual) ==> actual == expected
    }

    pub open spec fn referenced<K, R>(
        roots: Map<u64, Vec<K>>, records: Seq<R>, root_members: Set<Vec<K>>, record_members: Set<R>,
    ) -> bool {
        (exists|names: Vec<K>| roots.values().contains(names) && #[trigger] root_members.contains(names))
            || (exists|record: R| records.contains(record) && #[trigger] record_members.contains(record))
    }

    pub open spec fn row_matches<T, P: Fn(&T) -> bool>(project: P, members: Set<T>) -> bool {
        &&& forall|row: &T| #[trigger] call_requires(project, (row,))
        &&& forall|row: &T, actual: bool| #[trigger] call_ensures(project, (row,), actual)
            ==> actual == members.contains(*row)
    }

    proof fn matched_row<T, P: Fn(&T) -> bool>(
        rows: Seq<&T>, project: P, members: Set<T>, found: bool,
    )
        requires
            row_matches(project, members),
            found ==> exists|i: int| 0 <= i < rows.len()
                && call_ensures(project, (#[trigger] rows[i],), true),
            !found ==> forall|i: int| 0 <= i < rows.len()
                ==> call_ensures(project, (#[trigger] rows[i],), false),
        ensures found == exists|row: T|
            rows.unref().to_set().contains(row) && #[trigger] members.contains(row),
    {
        if found {
            let i = choose|i: int| 0 <= i < rows.len()
                && call_ensures(project, (#[trigger] rows[i],), true);
            assert(rows.unref()[i] == *rows[i]);
            assert(rows.unref().contains(*rows[i]));
            assert(members.contains(*rows[i]));
        } else {
            assert forall|row: T| #[trigger] members.contains(row) implies
                !rows.unref().to_set().contains(row) by {
                if rows.unref().to_set().contains(row) {
                    let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows.unref()[i] == row;
                    assert(*rows[i] == row);
                    assert(call_ensures(project, (rows[i],), false));
                }
            }
        }
    }

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires fence_map(fences),
    ensures out == match references {
        Some(names) => if !canonical {
            Err(Refusal::Invalid)
        } else if no_fenced_names(names@, names@.len() as int, fences@) {
            Ok(())
        } else {
            Err(Refusal::Conflict)
        },
        None => if fences@.is_empty() { Ok(()) } else { Err(Refusal::Unavailable) },
    },
))]

pub(super) fn admit_object_references<K: Ord, F>(
    references: Option<&[K]>,
    canonical: bool,
    fences: &BTreeMap<K, F>,
) -> Result<(), Refusal> {
    match references {
        Some(_) if !canonical => Err(Refusal::Invalid),
        Some(names) => {
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant
                    fence_map(fences),
                    canonical,
                    references == Some(names),
                    0 <= index <= names@.len(),
                    no_fenced_names(names@, index as int, fences@),
                decreases names@.len() - index,
            ))]
            while index < names.len() {
                let name = &names[index];
                let fenced = fences.contains_key(name);
                #[cfg(verus_keep_ghost)]
                proof! { lemma_btree_map_contains_key_ensures_if_obeys_cmp_concrete_eq(fences, name, fenced); }
                if fenced {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(!no_fenced_names(names@, names@.len() as int, fences@));
                    }
                    return Err(Refusal::Conflict);
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|i: int| 0 <= i <= index implies
                        !fences@.contains_key(#[trigger] names@[i]) by {
                        if i < index {
                            assert(!fences@.contains_key(names@[i]));
                        }
                    }
                }
                index += 1;
            }
            Ok(())
        }
        None if !fences.is_empty() => Err(Refusal::Unavailable),
        None => Ok(()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires
        fence_map(fences),
        observes(complete, known@),
        observes(referenced, live@),
        fences@.contains_key(*name) ==> call_requires(exact, (&fences@[*name],)),
        forall|value: &F, result: bool| fences@.contains_key(*name)
            && *value == fences@[*name] && #[trigger] call_ensures(exact, (value,), result)
            ==> result == same@,
    ensures out == if !valid {
        Err(Refusal::Invalid)
    } else if fences@.contains_key(*name) {
        if same@ { Ok(Some(fences@[*name])) } else { Err(Refusal::Conflict) }
    } else if !known@ {
        Err(Refusal::Unavailable)
    } else if live@ {
        Err(Refusal::Conflict)
    } else {
        Ok(None)
    },
))]
pub(super) fn withdraw_object<K: Ord, F: Copy>(
    fences: &BTreeMap<K, F>,
    name: &K,
    valid: bool,
    exact: impl Fn(&F) -> bool,
    complete: impl Fn() -> bool,
    referenced: impl Fn() -> bool,
    #[cfg(verus_keep_ghost)] known: Ghost<bool>,
    #[cfg(verus_keep_ghost)] live: Ghost<bool>,
    #[cfg(verus_keep_ghost)] same: Ghost<bool>,
) -> Result<Option<F>, Refusal> {
    if !valid {
        return Err(Refusal::Invalid);
    }
    let existing = fences.get(name);
    #[cfg(verus_keep_ghost)]
    proof! { lemma_btree_map_get_ensures_if_obeys_cmp_concrete_eq(fences, name, existing); }
    if let Some(fence) = existing {
        return if exact(fence) {
            Ok(Some(*fence))
        } else {
            Err(Refusal::Conflict)
        };
    }
    if !complete() {
        return Err(Refusal::Unavailable);
    }
    if referenced() {
        return Err(Refusal::Conflict);
    }
    Ok(None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires fence_map(old(fences)), !old(fences)@.contains_key(name),
    ensures fence_map(final(fences)), final(fences)@ == old(fences)@.insert(name, fence),
))]
pub(super) fn install_fence<K: Ord, F>(fences: &mut BTreeMap<K, F>, name: K, fence: F) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = *fences; }
    let _previous = fences.insert(name, fence);
    #[cfg(verus_keep_ghost)]
    proof! {
        lemma_btree_map_insert_ensures_if_obeys_cmp_concrete_eq(&before, fences, name, fence, _previous);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires
        btree_map_wf(roots),
        row_matches(in_root, root_members@),
        row_matches(in_record, record_members@),
    ensures
        out == referenced(roots@, records@, root_members@, record_members@),
))]
pub(super) fn has_live_reference<K, R>(
    roots: &BTreeMap<u64, Vec<K>>,
    records: &VecDeque<R>,
    in_root: impl Fn(&Vec<K>) -> bool,
    in_record: impl Fn(&R) -> bool,
    #[cfg(verus_keep_ghost)] root_members: Ghost<Set<Vec<K>>>,
    #[cfg(verus_keep_ghost)] record_members: Ghost<Set<R>>,
) -> bool {
    let mut root_rows = roots.values();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost root_before = root_rows.remaining(); }
    let root_match = root_rows.any(in_root);
    #[cfg(verus_keep_ghost)]
    proof! { matched_row(root_before, in_root, root_members@, root_match); }
    if root_match {
        return true;
    }

    let mut record_rows = records.iter();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost record_before = record_rows.remaining(); }
    let record_match = record_rows.any(in_record);
    #[cfg(verus_keep_ghost)]
    proof! {
        matched_row(record_before, in_record, record_members@, record_match);
        assert(record_before.unref() =~= records@);
    }
    record_match
}
