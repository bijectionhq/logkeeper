use crate::production::{
    matches_preparation as binds, may_acquire as acquire, may_close as close,
    next_revision as advances,
};
use vstd::{laws_eq::obeys_concrete_eq, prelude::*};

verus! {

pub open spec fn matches_preparation<C>(prepared: C, published: C) -> bool {
    prepared == published
}

pub open spec fn next_revision(current: int, offered: int) -> bool {
    offered == current + 1
}

pub open spec fn may_close(source_of_preparation: bool, held: bool) -> bool {
    !source_of_preparation && !held
}

pub open spec fn may_acquire(above_erasure_floor: bool, retained: bool, closed: bool) -> bool {
    above_erasure_floor && retained && !closed
}

pub fn publication_keeps_prepared_custody<C: Eq>(prepared: C, published: C)
    requires obeys_concrete_eq::<C>(),
{
    let publishes = binds(prepared, published);
    assert(publishes == matches_preparation(prepared, published));
}

pub fn preparation_revision_advances(current: u64, offered: u64) {
    let admissible = advances(current, offered);
    assert(admissible == next_revision(current as int, offered as int));
}

pub fn a_held_checkpoint_cannot_close(source_of_preparation: bool, pinned: bool) {
    let held = || -> (out: bool) ensures out == pinned { pinned };
    let closes = close(source_of_preparation, held, Ghost(pinned));
    assert(closes == may_close(source_of_preparation, pinned));
}

pub fn a_closed_checkpoint_refuses_new_acquisition(
    above_erasure_floor: bool, is_retained: bool, is_closed: bool,
) {
    let retained = || -> (out: bool) ensures out == is_retained { is_retained };
    let closed = || -> (out: bool) ensures out == is_closed { is_closed };
    let admits = acquire(above_erasure_floor, retained, closed, Ghost(is_retained), Ghost(is_closed));
    assert(admits == may_acquire(above_erasure_floor, is_retained, is_closed));
}

}
