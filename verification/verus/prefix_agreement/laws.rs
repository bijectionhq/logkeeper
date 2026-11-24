use crate::production::*;
use crate::rotation_support::{Ballot, Fingerprint, Uuid, Vote, VoterSlots, well_formed};
use crate::rotation_support::evidence::record_vote;
use vstd::prelude::*;

verus! {

fn promise_only_advances_above_floor(floor: BallotRank, ballot: BallotRank) {
    let refused = depose_prepare(Some(floor), ballot);
    if !refused && floor != ballot {
        assert(ballot_lt(floor, ballot));
    }
}

fn accept_at_or_above_promise(floor: BallotRank, ballot: BallotRank) {
    let decision = accept_ballot(Some(floor), ballot);
    if let AcceptBallot::Promised = decision {
        assert(!ballot_lt(ballot, floor) && ballot == floor);
    }
}

fn chosen_votes_bind_ballot_voter_and_image(
    voters: &mut Vec<VoterSlots>, expected: Uuid, ballot: Ballot,
    digest: Fingerprint, read_back: bool, vote: Vote,
) {
    let recorded = record_vote(voters, expected, ballot, digest, read_back, vote);
    if recorded {
        assert(vote.voter == expected && vote.ballot == ballot && vote.digest@ == digest@
            && well_formed(vote.slots) && vote.read_back == read_back);
    }
}

proof fn increasing_between(votes: Seq<u128>, first: int, last: int)
    requires
        0 <= first < last < votes.len(),
        forall|i: int| 0 < i < votes.len() ==> #[trigger] votes[i - 1] < #[trigger] votes[i],
    ensures votes[first] < votes[last],
    decreases last - first,
{
    if first + 1 < last {
        increasing_between(votes, first, last - 1);
    }
    assert(votes[last - 1] < votes[last]);
}

fn majority_is_strict(configured: &[u128], votes: &[u128]) {
    let chosen = configured_majority(configured, votes);
    if chosen {
        assert(2 * votes@.len() > configured@.len());
    }
}

fn majority_counts_only_configured_voters(configured: &[u128], votes: &[u128], i: usize)
    requires i < votes@.len(),
{
    let chosen = configured_majority(configured, votes);
    if chosen {
        assert(configured@.contains(votes@[i as int]));
    }
}

fn majority_counts_each_voter_once(configured: &[u128], votes: &[u128], first: usize, last: usize)
    requires first < last < votes@.len(),
{
    let chosen = configured_majority(configured, votes);
    if chosen {
        proof { increasing_between(votes@, first as int, last as int); }
        assert(votes@[first as int] != votes@[last as int]);
    }
}

fn winner_dominates_observed(current: BallotRank, observed: BallotRank) {
    let winner = recovery_choice(current, observed);
    let rank = if let RecoveryChoice::Replace = winner { observed } else { current };
    assert(!ballot_lt(rank, current) && !ballot_lt(rank, observed));
}

fn sealing_carries_exact_predecessor_image<T>(
    selected_seal: Option<&[u8; 32]>, destination: &[u8; 32], selected: T,
) {
    let sealed = seal_image(selected_seal, destination, selected);
    assert(sealed == if selected_seal matches Some(target) && target@ == destination@
        { Some(selected) } else { None });
}

fn installation_carries_exact_predecessor_image<T>(
    predecessor: Option<&[u8; 32]>, destination: &[u8; 32], source: &[u8; 32],
    target: &[u8; 32], image: T,
) {
    let installed = install_image(predecessor, destination, source, target, image);
    assert(installed == if (predecessor matches Some(old) && old@ == source@)
        && destination@ == target@ { Some(image) } else { None });
}

}
