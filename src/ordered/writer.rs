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

pub(super) fn authorize(holder_matches: bool, grant_matches: bool) -> Result<(), Refusal> {
    if !holder_matches {
        return Err(Refusal::Unauthorized);
    }
    if !grant_matches {
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

pub(super) fn withdraw<G>(grant: &mut Option<G>, holder_matches: bool) {
    if holder_matches {
        vacate(grant);
    }
}

pub(super) fn vacate<G>(grant: &mut Option<G>) {
    *grant = None;
}

pub(super) fn commit_append<R>(records: &mut VecDeque<R>, head: &mut Cut, record: R, cut: Cut) {
    records.push_back(record);
    *head = cut;
}
