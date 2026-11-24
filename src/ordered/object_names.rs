//! Canonical immutable object names shared by the reducer and codecs.

use super::ObjectName;
use super::budget::MAX_OBJECT_REFERENCES;

fn name_before(left: &ObjectName, right: &ObjectName) -> bool {
    let mut i = 0;
    while i < 32 {
        if left[i] != right[i] {
            return left[i] < right[i];
        }
        i += 1;
    }
    false
}

pub(super) fn valid_object_names(names: &[ObjectName]) -> bool {
    if names.len() > MAX_OBJECT_REFERENCES {
        return false;
    }
    if names.is_empty() {
        return true;
    }
    if !name_before(&[0; 32], &names[0]) {
        return false;
    }
    let mut i = 1;
    while i < names.len() {
        if !name_before(&names[i - 1], &names[i]) {
            return false;
        }
        i += 1;
    }
    true
}
