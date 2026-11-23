//! Validation and selection of physical voter slots.

use super::{Error, bounded_body_length, matches_fingerprint};

pub(crate) const MAGIC: &[u8; 8] = b"LKORV005";

pub(super) fn slot_body_length(length: u64, payload_limit: usize) -> Option<usize> {
    bounded_body_length(length, 2, payload_limit)
}

pub(super) fn authenticates_body(observed: &[u8], stored: &[u8]) -> bool {
    matches_fingerprint(observed, stored)
}

pub(super) fn slot_header_matches(
    magic: &[u8],
    addressed: &[u8],
    group: &[u8],
    witness: u128,
    voter: u128,
    generation: u64,
) -> bool {
    matches_fingerprint(magic, MAGIC)
        && matches_fingerprint(addressed, group)
        && witness == voter
        && generation != 0
}

pub(super) fn select_slot(first: Option<u64>, second: Option<u64>) -> Result<Option<usize>, Error> {
    match (first, second) {
        (None, None) => Ok(None),
        (Some(_), None) => Ok(Some(0)),
        (None, Some(_)) => Ok(Some(1)),
        (Some(a), Some(b)) if a == b => Err(Error::Diverged),
        (Some(a), Some(b)) => Ok(Some(if b > a { 1 } else { 0 })),
    }
}

pub(super) fn read_back_matches(
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
