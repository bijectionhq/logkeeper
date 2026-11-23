//! Executable admission and retention decisions shared with the proof harness.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Some) == (used as int + charge as int <= ceiling as int),
        match out {
            Some(end) => end as int == used as int + charge as int,
            None => true,
        },
))]
pub(super) fn debit(used: u64, charge: u64, ceiling: u64) -> Option<u64> {
    if used > ceiling || charge > ceiling - used {
        return None;
    }
    Some(used + charge)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (start < end && start < floor),
))]
pub(super) fn pins_suffix(start: u64, end: u64, floor: u64) -> bool {
    start < end && start < floor
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (position < expires_at || owns_live_hold),
))]
pub(super) fn retains_receipt(position: u64, expires_at: u64, owns_live_hold: bool) -> bool {
    position < expires_at || owns_live_hold
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (stored@ == presented@),
))]
pub(super) fn matches_fingerprint(stored: &[u8], presented: &[u8]) -> bool {
    if stored.len() != presented.len() {
        return false;
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= stored@.len(),
            stored@.len() == presented@.len(),
            forall|i: int| 0 <= i < index ==> stored@[i] == presented@[i],
        decreases stored@.len() - index,
    ))]
    while index < stored.len() {
        if stored[index] != presented[index] {
            #[cfg(verus_keep_ghost)]
            proof! { assert(stored@[index as int] != presented@[index as int]); }
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|at: int| 0 <= at < index + 1 implies stored@[at] == presented@[at] by {
                if at < index { assert(stored@[at] == presented@[at]); }
            }
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(stored@ =~= presented@); }
    true
}
