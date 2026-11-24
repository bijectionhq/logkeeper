//! Admission predicates for ordered checkpoint custody.

pub(super) fn matches_preparation<C: Eq>(prepared: C, published: C) -> bool {
    prepared == published
}

pub(super) fn next_revision(current: u64, offered: u64) -> bool {
    Some(offered) == current.checked_add(1)
}

pub(super) fn may_close(source_of_preparation: bool, held: impl Fn() -> bool) -> bool {
    !source_of_preparation && !held()
}

pub(super) fn may_acquire(
    above_erasure_floor: bool,
    retained: impl Fn() -> bool,
    closed: impl Fn() -> bool,
) -> bool {
    above_erasure_floor && retained() && !closed()
}
