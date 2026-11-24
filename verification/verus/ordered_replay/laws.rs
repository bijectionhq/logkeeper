use crate::production::{cursor_offset, replay_record_charge, retained_indices};
use vstd::prelude::*;

verus! {

pub open spec fn included(first: int, end: int, index: int) -> bool {
    first <= index < end
}

pub fn selected_replay_indices_cover_exact_interval(
    floor: u64, from: u64, through: u64, retained: usize,
) -> (indices: Option<(usize, usize)>)
    ensures
        (indices is Some) == (floor <= from <= through && through as int - floor as int <= retained),
        indices matches Some((first, end)) ==> first <= end <= retained
            && (forall|index: int| #[trigger] included(first as int, end as int, index)
                <==> from <= floor as int + index < through),
{
    let indices = retained_indices(floor, from, through, retained);
    proof {
        if let Some((first, end)) = indices {
            assert forall|index: int| #[trigger] included(first as int, end as int, index)
                <==> from <= floor as int + index < through by {}
        }
    }
    indices
}

pub fn resume_requires_exact_cut_in_original_interval(
    start: u64, from: u64, through: u64, exact_cut: bool,
) -> (skip: Option<usize>)
    ensures
        skip matches Some(index) ==> exact_cut && start <= from <= through
            && start as int + index as int == from as int,
        !exact_cut ==> skip is None,
{
    cursor_offset(start, from, through, exact_cut)
}

pub fn replay_head_and_page_charge_the_exact_successor(
    from: u64, record_cut: u64, through: u64, byte_start: u64, byte_end: u64,
) -> (charge: Option<u64>)
    ensures charge matches Some(bytes) ==> from as int + 1 == record_cut
        && record_cut <= through && byte_start as int + bytes == byte_end,
{
    replay_record_charge(from, record_cut, through, byte_start, byte_end)
}

}
