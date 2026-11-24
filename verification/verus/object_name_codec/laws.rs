use crate::ObjectName;
use crate::production::{objectNameBefore, objectNamesCanonical, orderAt, valid_object_names, zeroName};
use vstd::prelude::*;

verus! {

proof fn object_name_order_is_transitive(first: Seq<u8>, middle: Seq<u8>, last: Seq<u8>)
    requires objectNameBefore(first, middle), objectNameBefore(middle, last),
    ensures objectNameBefore(first, last),
{
    let left = choose|p: int| #[trigger] orderAt(first, middle, p);
    let right = choose|p: int| #[trigger] orderAt(middle, last, p);
    let pivot = if left < right { left } else { right };
    assert forall|i: int| 0 <= i < pivot implies (#[trigger] first[i]) == last[i] by {
        assert(first[i] == middle[i]);
        assert(middle[i] == last[i]);
    }
    if left < right {
        assert(middle[pivot] == last[pivot]);
    } else if right < left {
        assert(first[pivot] == middle[pivot]);
    }
    assert(orderAt(first, last, pivot));
}

proof fn increasing_names_are_pairwise_ordered(names: Seq<ObjectName>, earlier: int, later: int)
    requires objectNamesCanonical(names), 0 <= earlier < later < names.len(),
    ensures objectNameBefore(names[earlier]@, names[later]@),
    decreases later - earlier,
{
    assert(objectNameBefore(names[later - 1]@, names[later]@));
    if earlier < later - 1 {
        increasing_names_are_pairwise_ordered(names, earlier, later - 1);
        object_name_order_is_transitive(names[earlier]@, names[later - 1]@, names[later]@);
    }
}

fn admitted_object_names_are_bounded_sorted_unique_and_nonzero(names: &[ObjectName]) {
    let accepted = valid_object_names(names);
    if accepted {
        assert(names@.len() <= 16_384);
        assert forall|earlier: int, later: int| 0 <= earlier < later < names@.len() implies
            objectNameBefore((#[trigger] names@[earlier])@, (#[trigger] names@[later])@)
                && names@[earlier]@ != names@[later]@ by {
            increasing_names_are_pairwise_ordered(names@, earlier, later);
            let left = names@[earlier]@;
            let right = names@[later]@;
            let pivot = choose|p: int| #[trigger] orderAt(left, right, p);
            assert(left[pivot] < right[pivot]);
        }
        assert forall|index: int| 0 <= index < names@.len() implies
            (#[trigger] names@[index])@ != zeroName() by {
            if index != 0 {
                increasing_names_are_pairwise_ordered(names@, 0, index);
                object_name_order_is_transitive(zeroName(), names@[0]@, names@[index]@);
            }
            let name = names@[index]@;
            let pivot = choose|p: int| #[trigger] orderAt(zeroName(), name, p);
            assert(zeroName()[pivot] < name[pivot]);
        }
    }
}

}
