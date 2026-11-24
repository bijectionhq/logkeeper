//! Admission predicates for ordered checkpoint custody.

#[cfg(verus_keep_ghost)]
use vstd::{laws_eq::obeys_concrete_eq, prelude::*};

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<C>(),
    ensures out == (prepared == published),
))]
pub(super) fn matches_preparation<C: Eq>(prepared: C, published: C) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(obeys_concrete_eq); }
    prepared == published
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (offered as int == current as int + 1),
))]
pub(super) fn next_revision(current: u64, offered: u64) -> bool {
    Some(offered) == current.checked_add(1)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires call_requires(held, ()), !call_ensures(held, (), !pinned@),
    ensures out == (!source_of_preparation && !pinned@),
))]
pub(super) fn may_close(
    source_of_preparation: bool,
    held: impl Fn() -> bool,
    #[cfg(verus_keep_ghost)] pinned: Ghost<bool>,
) -> bool {
    !source_of_preparation && !held()
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires
        call_requires(retained, ()), !call_ensures(retained, (), !is_retained@),
        call_requires(closed, ()), !call_ensures(closed, (), !is_closed@),
    ensures out == (above_erasure_floor && is_retained@ && !is_closed@),
))]
pub(super) fn may_acquire(
    above_erasure_floor: bool,
    retained: impl Fn() -> bool,
    closed: impl Fn() -> bool,
    #[cfg(verus_keep_ghost)] is_retained: Ghost<bool>,
    #[cfg(verus_keep_ghost)] is_closed: Ghost<bool>,
) -> bool {
    above_erasure_floor && retained() && !closed()
}
