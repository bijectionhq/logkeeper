//! Canonical immutable object names shared by the reducer and codecs.

use super::ObjectName;
use super::budget::MAX_OBJECT_REFERENCES;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn orderAt(left: Seq<u8>, right: Seq<u8>, pivot: int) -> bool {
    &&& 0 <= pivot < 32
    &&& left[pivot] < right[pivot]
    &&& forall|j: int| 0 <= j < pivot ==> (#[trigger] left[j]) == right[j]
}

pub(super) open spec fn objectNameBefore(left: Seq<u8>, right: Seq<u8>) -> bool {
    exists|pivot: int| #[trigger] orderAt(left, right, pivot)
}

pub(super) open spec fn zeroName() -> Seq<u8> {
    Seq::new(32, |_i| 0u8)
}

pub(super) open spec fn objectNamesCanonical(names: Seq<ObjectName>) -> bool {
    &&& names.len() <= 16_384
    &&& names.len() > 0 ==> objectNameBefore(zeroName(), names[0]@)
    &&& forall|i: int| 1 <= i < names.len()
        ==> objectNameBefore(names[i - 1]@, (#[trigger] names[i])@)
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == objectNameBefore(left@, right@),))]
fn name_before(left: &ObjectName, right: &ObjectName) -> bool {
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 32,
            forall|j: int| 0 <= j < i ==> (#[trigger] left@[j]) == right@[j],
        decreases 32 - i,
    ))]
    while i < 32 {
        if left[i] != right[i] {
            #[cfg(verus_keep_ghost)]
            proof! {
                if left@[i as int] < right@[i as int] {
                    assert(orderAt(left@, right@, i as int));
                } else if objectNameBefore(left@, right@) {
                    let pivot = choose|p: int| #[trigger] orderAt(left@, right@, p);
                    if pivot < i {
                        assert(left@[pivot] == right@[pivot]);
                    } else if pivot > i {
                        assert(left@[i as int] == right@[i as int]);
                    }
                    assert(false);
                }
            }
            return left[i] < right[i];
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if objectNameBefore(left@, right@) {
            let pivot = choose|p: int| #[trigger] orderAt(left@, right@, p);
            assert(left@[pivot] == right@[pivot]);
        }
    }
    false
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == objectNamesCanonical(names@),))]
pub(super) fn valid_object_names(names: &[ObjectName]) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { super::budget::reference_limit_is_16384(); }
    if names.len() > MAX_OBJECT_REFERENCES {
        return false;
    }
    if names.is_empty() {
        return true;
    }
    let zero = [0; 32];
    #[cfg(verus_keep_ghost)]
    proof! { assert(zero@ =~= zeroName()); }
    if !name_before(&zero, &names[0]) {
        return false;
    }
    let mut i = 1;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            1 <= i <= names@.len() <= 16_384,
            objectNameBefore(zeroName(), names@[0]@),
            forall|j: int| 1 <= j < i
                ==> objectNameBefore(names@[j - 1]@, (#[trigger] names@[j])@),
        decreases names@.len() - i,
    ))]
    while i < names.len() {
        if !name_before(&names[i - 1], &names[i]) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(!objectNamesCanonical(names@));
            }
            return false;
        }
        i += 1;
    }
    true
}
