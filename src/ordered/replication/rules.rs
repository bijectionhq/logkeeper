//! Local decisions for the durable prefix protocol.

use crate::ordered::cohort::{accept_quorum, matches_chosen_seal};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn ballot_lt(left: BallotRank, right: BallotRank) -> bool {
        left.0 < right.0 || (left.0 == right.0 && left.1 < right.1)
    }
}

pub(super) type BallotRank = (u64, u128);

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == ballot_lt(left, right),
))]
pub(super) fn lower_ballot(left: BallotRank, right: BallotRank) -> bool {
    left.0 < right.0 || (left.0 == right.0 && left.1 < right.1)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match floor {
        Some(floor) => ballot_lt(ballot, floor),
        None => false,
    },
))]
pub(super) fn depose_prepare(floor: Option<BallotRank>, ballot: BallotRank) -> bool {
    match floor {
        Some(floor) => lower_ballot(ballot, floor),
        None => false,
    }
}

pub(super) enum AcceptBallot {
    Deposed,
    Promised,
    Unprepared,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match floor {
        Some(floor) => (out is Deposed) == ballot_lt(ballot, floor)
            && (out is Promised) == (floor == ballot),
        None => out is Unprepared,
    },
))]
pub(super) fn accept_ballot(floor: Option<BallotRank>, ballot: BallotRank) -> AcceptBallot {
    match floor {
        Some(floor) if lower_ballot(ballot, floor) => AcceptBallot::Deposed,
        Some(floor) if same_ballot(floor, ballot) => AcceptBallot::Promised,
        _ => AcceptBallot::Unprepared,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (left == right),
))]
pub(super) fn same_ballot(left: BallotRank, right: BallotRank) -> bool {
    left.0 == right.0 && left.1 == right.1
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (left@ == right@),
))]
pub(super) fn same_image(left: &[u8; 32], right: &[u8; 32]) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= 32, left@.len() == 32, right@.len() == 32,
            forall|i: int| 0 <= i < index ==> left@[i] == right@[i],
        decreases 32 - index,
    ))]
    while index < 32 {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(left@ =~= right@); }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == configured@.contains(voter),
))]
fn contains_voter(configured: &[u128], voter: u128) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= configured@.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] configured@[i] != voter,
        decreases configured@.len() - index,
    ))]
    while index < configured.len() {
        if configured[index] == voter {
            #[cfg(verus_keep_ghost)]
            proof! { assert(exists|i: int| 0 <= i < configured@.len() && configured@[i] == voter)
            by { let witness = index as int; assert(configured@[witness] == voter); } }
            return true;
        }
        index += 1;
    }
    false
}

// The certificate is in voter order at the point where the coordinator returns it.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out ==> 2 * votes@.len() > configured@.len(),
        out ==> forall|i: int| 0 <= i < votes@.len() ==> configured@.contains(#[trigger] votes@[i]),
        out ==> forall|i: int| 0 < i < votes@.len() ==> #[trigger] votes@[i - 1] < #[trigger] votes@[i],
))]
pub(super) fn configured_majority(configured: &[u128], votes: &[u128]) -> bool {
    if !accept_quorum(votes.len(), configured.len()) {
        return false;
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= votes@.len(),
            2 * votes@.len() > configured@.len(),
            forall|i: int| 0 <= i < index ==> configured@.contains(#[trigger] votes@[i]),
            forall|i: int| 0 < i < index ==> #[trigger] votes@[i - 1] < #[trigger] votes@[i],
        decreases votes@.len() - index,
    ))]
    while index < votes.len() {
        if !contains_voter(configured, votes[index])
            || (index > 0 && votes[index - 1] >= votes[index])
        {
            return false;
        }
        index += 1;
    }
    true
}

pub(super) enum RecoveryChoice {
    Keep,
    Tie,
    Replace,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Keep) == ballot_lt(observed, current),
        (out is Tie) == (current == observed),
))]
pub(super) fn recovery_choice(current: BallotRank, observed: BallotRank) -> RecoveryChoice {
    if lower_ballot(observed, current) {
        RecoveryChoice::Keep
    } else if same_ballot(observed, current) {
        RecoveryChoice::Tie
    } else {
        RecoveryChoice::Replace
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match selected_seal {
        Some(target) => target@ == destination@,
        None => false,
    },
))]
pub(super) fn sealed_for(selected_seal: Option<&[u8; 32]>, destination: &[u8; 32]) -> bool {
    matches_chosen_seal(selected_seal, destination)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if selected_seal matches Some(target) && target@ == destination@
        { Some(selected) } else { None },
))]
pub(super) fn seal_image<T>(
    selected_seal: Option<&[u8; 32]>,
    destination: &[u8; 32],
    selected: T,
) -> Option<T> {
    if sealed_for(selected_seal, destination) {
        Some(selected)
    } else {
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if (predecessor matches Some(old) && old@ == source@)
        && destination@ == target@ { Some(image) } else { None },
))]
pub(super) fn install_image<T>(
    predecessor: Option<&[u8; 32]>,
    destination: &[u8; 32],
    source: &[u8; 32],
    target: &[u8; 32],
    image: T,
) -> Option<T> {
    if sealed_for(predecessor, source) && same_image(destination, target) {
        Some(image)
    } else {
        None
    }
}
