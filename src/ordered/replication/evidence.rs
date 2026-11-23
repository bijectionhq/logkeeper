//! Decisions used when collecting rotation slot attestations.

use super::{Ballot, Fingerprint, Uuid};
use crate::ordered::admission::matches_fingerprint;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlotImage {
    pub generation: u64,
    pub digest: Fingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlotPair {
    /// Index of the selected image in the physical A/B order.
    pub selected: u8,
    pub images: [SlotImage; 2],
}

impl SlotPair {
    pub fn is_mirrored(&self) -> bool {
        if self.selected > 1 {
            return false;
        }
        let selected = self.images[self.selected as usize];
        let alternate = self.images[1 - self.selected as usize];
        alternate.generation != 0
            && alternate.generation.checked_add(1) == Some(selected.generation)
            && !matches_fingerprint(&alternate.digest, &[0; 32])
            && !matches_fingerprint(&selected.digest, &[0; 32])
            && !matches_fingerprint(&alternate.digest, &selected.digest)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Vote {
    pub voter: Uuid,
    pub ballot: Ballot,
    pub digest: Fingerprint,
    pub slots: SlotPair,
    pub read_back: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoterSlots {
    pub voter: Uuid,
    pub slots: SlotPair,
}

pub(super) fn strict_majority(cohort_size: usize) -> usize {
    cohort_size / 2 + 1
}

pub(super) fn record_vote(
    voters: &mut Vec<VoterSlots>,
    expected: Uuid,
    ballot: Ballot,
    digest: Fingerprint,
    read_back: bool,
    vote: Vote,
) -> bool {
    if vote.voter.as_u128() != expected.as_u128()
        || vote.ballot.round != ballot.round
        || vote.ballot.nonce.as_u128() != ballot.nonce.as_u128()
        || !matches_fingerprint(&vote.digest, &digest)
        || !vote.slots.is_mirrored()
        || vote.read_back != read_back
    {
        return false;
    }
    voters.push(VoterSlots {
        voter: expected,
        slots: vote.slots,
    });
    true
}

pub(super) fn valid_voters(voters: &[VoterSlots]) -> bool {
    let mut index = 0;
    while index < voters.len() {
        let current = &voters[index];
        if current.voter.as_u128() == 0 || !current.slots.is_mirrored() {
            return false;
        }
        if index > 0 && voters[index - 1].voter.as_u128() >= current.voter.as_u128() {
            return false;
        }
        index += 1;
    }
    true
}
