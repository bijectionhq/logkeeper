use crate::production::{
    accept_quorum as confirm, has_paid_repair_quorum as paid_repair, matches_chosen_seal as seed,
    may_extend as admit_fresh,
};
use vstd::prelude::*;

verus! {

pub open spec fn accept_quorum(accepted: int, members: int) -> bool {
    members < 2 * accepted
}

pub open spec fn has_paid_repair_quorum(paid: int, quorum: int) -> bool {
    quorum <= paid
}

pub open spec fn may_extend<G>(successor: Option<G>) -> bool {
    successor is None
}

pub open spec fn matches_chosen_seal(successor: Option<&[u8; 32]>, destination: &[u8; 32]) -> bool {
    successor matches Some(target) && target@ == destination@
}

pub fn accept_quorum_is_majority(accepted: usize, members: usize) {
    let confirmed = confirm(accepted, members);
    assert(confirmed == accept_quorum(accepted as int, members as int));
}

pub fn seal_requires_paid_successor_quorum(paid: usize, members: usize) {
    let funded = paid_repair(paid, members / 2 + 1);
    assert(funded == has_paid_repair_quorum(paid as int, (members as int) / 2 + 1)
        && funded == accept_quorum(paid as int, members as int));
}

pub fn sealed_cohort_refuses_new_decisions<G>(successor: G) {
    let extends = admit_fresh(Some(successor));
    assert(extends == may_extend(Some(successor)));
}

pub fn repair_requires_the_chosen_destination(successor: Option<&[u8; 32]>, destination: &[u8; 32]) {
    let seeds = seed(successor, destination);
    assert(seeds == matches_chosen_seal(successor, destination));
}

}
