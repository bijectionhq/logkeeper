//! Writer authorization and frontier decisions used by the ordered reducer.

use std::collections::VecDeque;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    WrongPlacement,
    Unauthorized,
    Stale,
    Conflict,
    Invalid,
    Expired,
    Capacity,
    Unavailable,
    CohortSealed,
}

/// An exclusive data frontier and the identity of the prefix before it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Cut {
    pub next_lsn: u64,
    pub history: [u8; 32],
}

pub(super) fn authorize<E: Eq + Copy>(
    principal: Option<E>,
    current: Option<(E, u64, u64)>,
    presented: (E, u64, u64),
) -> Result<(), Refusal> {
    if principal != Some(presented.0) {
        return Err(Refusal::Unauthorized);
    }
    let Some((holder, epoch, key_generation)) = current else {
        return Err(Refusal::Stale);
    };
    let (candidate, candidate_epoch, candidate_generation) = presented;
    if holder != candidate || epoch != candidate_epoch || key_generation != candidate_generation {
        return Err(Refusal::Stale);
    }
    Ok(())
}

pub(super) fn next_epoch(epoch: u64) -> Result<u64, Refusal> {
    epoch.checked_add(1).ok_or(Refusal::Capacity)
}

pub(super) fn append_next(head: u64, expected_next: u64) -> Result<u64, Refusal> {
    if head != expected_next {
        return Err(Refusal::Stale);
    }
    expected_next.checked_add(1).ok_or(Refusal::Capacity)
}

#[derive(Clone)]
pub(super) struct Authority<G> {
    pub(super) epoch: u64,
    pub(super) key_generation: u64,
    pub(super) grant: Option<G>,
}

impl<G> Authority<G> {
    pub(super) fn install(&mut self, epoch: u64, key_generation: u64, grant: G) {
        self.epoch = epoch;
        self.key_generation = key_generation;
        self.grant = Some(grant);
    }

    pub(super) fn withdraw(&mut self, holder_matches: bool) {
        if holder_matches {
            self.vacate();
        }
    }

    pub(super) fn vacate(&mut self) {
        self.grant = None;
    }
}

pub(super) fn commit_append<R>(records: &mut VecDeque<R>, head: &mut Cut, record: R, cut: Cut) {
    records.push_back(record);
    *head = cut;
}
