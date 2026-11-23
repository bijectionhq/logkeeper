//! Decisions used when collecting rotation slot attestations.

use super::{Ballot, Checkpoint, Fingerprint, Outcome, Receipt, Uuid};
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

pub(crate) fn strict_majority(cohort_size: usize) -> usize {
    cohort_size / 2 + 1
}

pub(crate) fn record_vote(
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

pub(crate) fn valid_voters(voters: &[VoterSlots]) -> bool {
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

/// Both images on each member of an accepting majority encode the named
/// prefix. Every later eligible recovery inherits that prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotationSlots {
    pub group: Fingerprint,
    pub cohort_size: usize,
    pub ballot: Ballot,
    pub prefix: Fingerprint,
    pub position: u64,
    pub checkpoint: Checkpoint,
    pub key_generation: u64,
    pub voters: Vec<VoterSlots>,
}

impl RotationSlots {
    pub fn covers(&self, receipt: Receipt) -> bool {
        let Ok(Outcome::Granted { grant, recovery }) = receipt.outcome else {
            return false;
        };
        self.group != [0; 32]
            && self.ballot.round != 0
            && !self.ballot.nonce.is_nil()
            && self.prefix != [0; 32]
            && receipt.position != 0
            && self.position >= receipt.position
            && self.checkpoint == recovery.checkpoint
            && recovery.admitted_at == receipt.position
            && recovery.start == self.checkpoint.cut
            && recovery.through == self.checkpoint.cut
            && self.key_generation == grant.key_generation
            && self.key_generation > 1
            && self.cohort_size >= 3
            && self.cohort_size % 2 == 1
            && self.voters.len() == strict_majority(self.cohort_size)
            && valid_voters(&self.voters)
    }
}

