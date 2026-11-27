use crate::production::*;
use vstd::prelude::*;

verus! {

fn a_deposed_lineage_never_supplies_the_successors_records(
    start: u64, floor: u64, successor: u64, object_end: u64,
)
    requires successor > 0,
{
    if let Some((first, end)) = restore_window(start, floor, Some(successor)) {
        assert(first >= start && first >= floor && end < successor);
        if object_end >= first {
            let (last, next) = restore_cut(first, object_end, end);
            assert(first <= last < successor && next as int == last as int + 1);
        }
    }
}

fn extending_a_run_never_crosses_a_gap(last: u64, first: u64)
    requires last < u64::MAX,
{
    let (next, extending) = restore_cursor(Some(last), first);
    assert(extending <==> last as int + 1 >= first);
    assert(extending ==> next as int == last as int + 1);
    assert(!extending ==> next == first);
}

fn a_gap_never_discards_an_available_cover(
    ranges: &[(u64, u64)], cursor: u64, end: u64, at: usize,
)
    requires cursor <= end, at < ranges@.len(), covers(ranges@[at as int], cursor),
{
    let selection = select_restore_object(ranges, cursor, end);
    assert(selection is Object);
    if let Selection::Object(index) = selection {
        assert(ranges@[index as int].1 >= ranges@[at as int].1);
    }
}

}
