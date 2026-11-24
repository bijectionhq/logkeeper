//! Paid object fence installation.

use super::{Refusal, object_withdrawal};
use std::collections::BTreeMap;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn commitWithdrawal<K, F>(prior: Map<K, F>, name: K, fence: F) -> Map<K, F> {
    prior.insert(name, fence)
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires object_withdrawal::fence_map(old(fences)), !old(fences)@.contains_key(name),
    ensures
        out == if capacity < (if used as int + charge > usize::MAX { usize::MAX as int }
            else { used as int + charge }) { Err(Refusal::Capacity) } else { Ok(()) },
        final(fences)@ == if out is Ok { commitWithdrawal(old(fences)@, name, fence) } else { old(fences)@ },
        object_withdrawal::fence_map(final(fences)),
))]
pub(super) fn commit_withdrawal<K: Ord, F>(
    fences: &mut BTreeMap<K, F>,
    name: K,
    fence: F,
    used: usize,
    charge: usize,
    capacity: usize,
) -> Result<(), Refusal> {
    if used.saturating_add(charge) > capacity {
        return Err(Refusal::Capacity);
    }
    object_withdrawal::install_fence(fences, name, fence);
    Ok(())
}
