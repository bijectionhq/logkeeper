//! Name-keyed admission, exact retry and fence insertion.

use super::Refusal;
use std::collections::{BTreeMap, VecDeque};

pub(super) fn admit_object_references<K: Ord, F>(
    references: Option<&[K]>,
    canonical: bool,
    fences: &BTreeMap<K, F>,
) -> Result<(), Refusal> {
    match references {
        Some(_) if !canonical => Err(Refusal::Invalid),
        Some(names) => {
            let mut index = 0;
            while index < names.len() {
                if fences.contains_key(&names[index]) {
                    return Err(Refusal::Conflict);
                }
                index += 1;
            }
            Ok(())
        }
        None if !fences.is_empty() => Err(Refusal::Unavailable),
        None => Ok(()),
    }
}

pub(super) fn withdraw_object<K: Ord, F: Copy>(
    fences: &BTreeMap<K, F>,
    name: &K,
    valid: bool,
    exact: impl Fn(&F) -> bool,
    complete: impl Fn() -> bool,
    referenced: impl Fn() -> bool,
) -> Result<Option<F>, Refusal> {
    if !valid {
        return Err(Refusal::Invalid);
    }
    if let Some(fence) = fences.get(name) {
        return if exact(fence) {
            Ok(Some(*fence))
        } else {
            Err(Refusal::Conflict)
        };
    }
    if !complete() {
        return Err(Refusal::Unavailable);
    }
    if referenced() {
        return Err(Refusal::Conflict);
    }
    Ok(None)
}

pub(super) fn install_fence<K: Ord, F>(fences: &mut BTreeMap<K, F>, name: K, fence: F) {
    fences.insert(name, fence);
}

pub(super) fn has_live_reference<K, R>(
    roots: &BTreeMap<u64, Vec<K>>,
    records: &VecDeque<R>,
    in_root: impl Fn(&Vec<K>) -> bool,
    in_record: impl Fn(&R) -> bool,
) -> bool {
    roots.values().any(in_root) || records.iter().any(in_record)
}
