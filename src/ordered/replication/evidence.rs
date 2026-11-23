//! Decisions used when collecting rotation slot attestations.

use super::{BTreeSet, Ballot, Checkpoint, Fingerprint, Outcome, Receipt, Uuid};
use crate::ordered::admission::matches_fingerprint;

#[cfg(verus_keep_ghost)]
use super::{covers_rotation, record_matches, valid_voter_prefix, well_formed, zeros};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct SlotImage {
    pub generation: u64,
    pub digest: Fingerprint,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct SlotPair {
    /// Index of the selected image in the physical A/B order.
    pub selected: u8,
    pub images: [SlotImage; 2],
}

impl SlotPair {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == well_formed(*self),
    ))]
    pub fn is_mirrored(&self) -> bool {
        let zero = [0; 32];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(zero@ =~= zeros());
        }
        if self.selected > 1 {
            return false;
        }
        let selected = self.images[self.selected as usize];
        let alternate = self.images[1 - self.selected as usize];
        alternate.generation != 0
            && alternate.generation.checked_add(1) == Some(selected.generation)
            && !matches_fingerprint(&alternate.digest, &zero)
            && !matches_fingerprint(&selected.digest, &zero)
            && !matches_fingerprint(&alternate.digest, &selected.digest)
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[derive(Clone, Copy)]
pub struct Vote {
    pub voter: Uuid,
    pub ballot: Ballot,
    pub digest: Fingerprint,
    pub slots: SlotPair,
    pub read_back: bool,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct VoterSlots {
    pub voter: Uuid,
    pub slots: SlotPair,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (configured.members@.contains(id) && !old(seen).members@.contains(id)),
        final(seen).members@ == if configured.members@.contains(id) {
            old(seen).members@.insert(id)
        } else {
            old(seen).members@
        },
))]
pub(crate) fn register_peer(
    configured: &BTreeSet<Uuid>,
    seen: &mut BTreeSet<Uuid>,
    id: Uuid,
) -> bool {
    configured.contains(&id) && seen.insert(id)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == cohort_size / 2 + 1, 2 * out as int > cohort_size as int,
))]
pub(crate) fn strict_majority(cohort_size: usize) -> usize {
    cohort_size / 2 + 1
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == record_matches(vote, expected, ballot, digest, read_back),
        out ==> final(voters)@.len() == old(voters)@.len() + 1
            && final(voters)@.drop_last() == old(voters)@
            && final(voters)@.last().voter == expected
            && final(voters)@.last().slots == vote.slots,
        !out ==> final(voters)@ == old(voters)@,
))]
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

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == valid_voter_prefix(voters@, voters@.len() as int),
))]
pub(crate) fn valid_voters(voters: &[VoterSlots]) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant valid_voter_prefix(voters@, index as int),
        decreases voters@.len() - index,
    ))]
    while index < voters.len() {
        let current = &voters[index];
        if current.voter.as_u128() == 0 || !current.slots.is_mirrored() {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(voters@[index as int] == *current);
                assert(current.voter.0 == 0 || !well_formed(current.slots));
                assert(!valid_voter_prefix(voters@, voters@.len() as int));
            }
            return false;
        }
        if index > 0 && voters[index - 1].voter.as_u128() >= current.voter.as_u128() {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(voters@[index as int] == *current);
                assert(voters@[index as int - 1].voter.0 >= voters@[index as int].voter.0);
                assert(!valid_voter_prefix(voters@, voters@.len() as int));
            }
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i: int| 0 <= i <= index implies
                #[trigger] voters@[i].voter.0 != 0 && well_formed(voters@[i].slots) by {
                if i == index as int {
                    assert(voters@[i] == *current);
                }
            }
            assert forall|i: int| 0 < i <= index implies
                voters@[i - 1].voter.0 < #[trigger] voters@[i].voter.0 by {
                if i == index as int {
                    assert(voters@[i] == *current);
                }
            }
        }
        index += 1;
    }
    true
}

/// Both images on each member of an accepting majority encode the named
/// prefix. Every later eligible recovery inherits that prefix.
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
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
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == covers_rotation(self, receipt),
    ))]
    pub fn covers(&self, receipt: Receipt) -> bool {
        let Ok(Outcome::Granted { grant, recovery }) = receipt.outcome else {
            return false;
        };
        let zero = [0; 32];
        #[cfg(verus_keep_ghost)]
        proof! { assert(zero@ =~= zeros()); }
        !matches_fingerprint(&self.group, &zero)
            && self.ballot.round != 0
            && !self.ballot.nonce.is_nil()
            && !matches_fingerprint(&self.prefix, &zero)
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
