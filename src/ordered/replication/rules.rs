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
        Some(floor) if floor == ballot => AcceptBallot::Promised,
        _ => AcceptBallot::Unprepared,
    }
}
