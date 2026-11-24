//! Confirmation consumes replies for one prepared ballot and one candidate image.

use super::{Ballot, Fingerprint, Uuid, Vote, VoterSlots, evidence::record_vote, rules::contains_voter};
use crate::ordered::cohort::accept_quorum;

#[cfg(verus_keep_ghost)]
use super::record_matches;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) enum Confirmation {
    Ignored,
    Pending,
    Confirmed,
}

pub(super) struct Candidate {
    pub(super) ballot: Ballot,
    pub(super) digest: Fingerprint,
    pub(super) read_back: bool,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    (out is Ignored) == (!configured@.contains(expected.0)
        || (exists|i: int| 0 <= i < old(voters)@.len() && #[trigger] old(voters)@[i].voter == expected)
        || !record_matches(reply, expected, candidate.ballot, candidate.digest, candidate.read_back)),
    out is Ignored ==> final(voters)@ == old(voters)@,
    !(out is Ignored) ==>
        configured@.contains(expected.0)
        && (forall|i: int| 0 <= i < old(voters)@.len() ==> #[trigger] old(voters)@[i].voter != expected)
        && record_matches(reply, expected, candidate.ballot, candidate.digest, candidate.read_back)
        && final(voters)@.len() == old(voters)@.len() + 1
        && final(voters)@.drop_last() == old(voters)@
        && final(voters)@.last().voter == expected && final(voters)@.last().slots == reply.slots,
    (out is Confirmed) == (!(out is Ignored) && final(voters)@.len() > configured@.len() / 2),
))]
pub(super) fn receive_vote(
    configured: &[u128],
    voters: &mut Vec<VoterSlots>,
    candidate: &Candidate,
    expected: Uuid,
    reply: Vote,
) -> Confirmation {
    let voter = expected.as_u128();
    if !contains_voter(configured, voter) {
        return Confirmation::Ignored;
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= voters@.len(),
            voters@ == old(voters)@,
            voter == expected.0,
            forall|i: int| 0 <= i < index ==> #[trigger] voters@[i].voter != expected,
        decreases voters@.len() - index,
    ))]
    while index < voters.len() {
        if voters[index].voter.as_u128() == voter {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(exists|i: int| 0 <= i < old(voters)@.len()
                    && #[trigger] old(voters)@[i].voter == expected) by {
                    let witness = index as int;
                    assert(old(voters)@[witness].voter == expected);
                }
            }
            return Confirmation::Ignored;
        }
        index += 1;
    }
    if !record_vote(voters, expected, candidate.ballot, candidate.digest, candidate.read_back, reply) {
        return Confirmation::Ignored;
    }
    if accept_quorum(voters.len(), configured.len()) {
        Confirmation::Confirmed
    } else {
        Confirmation::Pending
    }
}
