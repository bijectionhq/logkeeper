//! Validation and selection of physical voter slots.

use super::{Error, matches_fingerprint};

#[cfg(verus_keep_ghost)]
use super::slot_selection;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (observed@ == stored@),
))]
pub(crate) fn authenticates_body(observed: &[u8], stored: &[u8]) -> bool {
    matches_fingerprint(observed, stored)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == slot_selection(first, second),
))]
pub(crate) fn select_slot(first: Option<u64>, second: Option<u64>) -> Result<Option<usize>, Error> {
    match (first, second) {
        (None, None) => Ok(None),
        (Some(_), None) => Ok(Some(0)),
        (None, Some(_)) => Ok(Some(1)),
        (Some(a), Some(b)) if a == b => Err(Error::Diverged),
        (Some(a), Some(b)) => Ok(Some(if b > a { 1 } else { 0 })),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (image_generation == expected_generation && observed_image@ == expected_image@
        && promised_matches && accepted_matches && observed_prefix@ == expected_prefix@),
))]
pub(crate) fn read_back_matches(
    image_generation: u64,
    expected_generation: u64,
    observed_image: &[u8],
    expected_image: &[u8],
    promised_matches: bool,
    accepted_matches: bool,
    observed_prefix: &[u8],
    expected_prefix: &[u8],
) -> bool {
    image_generation == expected_generation
        && matches_fingerprint(observed_image, expected_image)
        && promised_matches
        && accepted_matches
        && matches_fingerprint(observed_prefix, expected_prefix)
}
