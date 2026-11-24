//! Paid object fence installation.

use super::{Refusal, object_withdrawal};
use std::collections::BTreeMap;

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
