//! Local decisions for the durable prefix protocol.

pub(super) type BallotRank = (u64, u128);

pub(super) fn lower_ballot(left: BallotRank, right: BallotRank) -> bool {
    left.0 < right.0 || (left.0 == right.0 && left.1 < right.1)
}

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

pub(super) fn accept_ballot(floor: Option<BallotRank>, ballot: BallotRank) -> AcceptBallot {
    match floor {
        Some(floor) if lower_ballot(ballot, floor) => AcceptBallot::Deposed,
        Some(floor) if same_ballot(floor, ballot) => AcceptBallot::Promised,
        _ => AcceptBallot::Unprepared,
    }
}

pub(super) fn same_ballot(left: BallotRank, right: BallotRank) -> bool {
    left.0 == right.0 && left.1 == right.1
}

pub(super) fn strict_majority(configured: usize, votes: usize) -> bool {
    votes > configured / 2
}

fn contains_voter(configured: &[u128], voter: u128) -> bool {
    let mut index = 0;
    while index < configured.len() {
        if configured[index] == voter {
            return true;
        }
        index += 1;
    }
    false
}

// The certificate is in voter order at the point where the coordinator returns it.
pub(super) fn configured_majority(configured: &[u128], votes: &[u128]) -> bool {
    if !strict_majority(configured.len(), votes.len()) {
        return false;
    }
    let mut index = 0;
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

pub(super) fn recovery_choice(current: BallotRank, observed: BallotRank) -> RecoveryChoice {
    if lower_ballot(observed, current) {
        RecoveryChoice::Keep
    } else if same_ballot(observed, current) {
        RecoveryChoice::Tie
    } else {
        RecoveryChoice::Replace
    }
}

pub(super) fn sealed_for(selected_seal: Option<&[u8; 32]>, destination: &[u8; 32]) -> bool {
    match selected_seal {
        Some(target) => same_image(target, destination),
        None => false,
    }
}

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
