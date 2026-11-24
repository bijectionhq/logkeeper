use super::production::{extent_fits, frame_body_fits, place_extent};
use vstd::prelude::*;

verus! {

fn frame_never_reads_past_segment(remaining: u64, len: u32, max: usize) {
    let fits = frame_body_fits(remaining, len, max);
    assert(fits ==> len as int <= max as int && 8 + len as int <= remaining as int);
}

fn extent_stays_in_its_pack(
    seq: u64, next: u64, offset: u64, len: u32, max: usize, size: u64,
) {
    let fits = extent_fits(seq, next, offset, len, max, size);
    assert(fits ==> seq <= next && len as int <= max as int
        && offset as int + len as int <= size as int);
}

fn new_extents_are_adjacent(offset: u64, first: usize, second: usize) {
    if let Some((written, next)) = place_extent(offset, first) {
        if let Some((following, end)) = place_extent(next, second) {
            assert(written as int == first as int);
            assert(following as int == second as int);
            assert(next as int == offset as int + first as int);
            assert(end as int == offset as int + first as int + second as int);
        }
    }
}

}
