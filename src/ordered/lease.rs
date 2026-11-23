//! Journal time, serving leases and withdrawn-owner selection.

use super::{Refusal, writer};
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq, thiserror::Error))]
pub enum ApplyError {
    #[cfg_attr(
        not(verus_keep_ghost),
        error("command position does not follow the applied journal prefix")
    )]
    Position,
    #[cfg_attr(
        not(verus_keep_ghost),
        error("decision time precedes the applied journal time")
    )]
    Time,
}

pub(super) fn advance_decision(
    position: &mut u64,
    time: &mut u64,
    next_position: u64,
    next_time: u64,
) -> Result<(), ApplyError> {
    if position.checked_add(1) != Some(next_position) {
        return Err(ApplyError::Position);
    }
    if next_time < *time {
        return Err(ApplyError::Time);
    }
    *position = next_position;
    *time = next_time;
    Ok(())
}

pub(super) fn issue<W: Ord, E: Ord + Copy>(
    roster: &BTreeMap<W, E>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    principal: Option<E>,
    current: Option<(E, u64, u64)>,
    grant: (E, u64, u64),
    now: u64,
    duration: u64,
) -> Result<u64, Refusal> {
    writer::authorize(principal, current, grant)?;
    if roster.get(worker) != Some(&grant.0) {
        return Err(Refusal::Stale);
    }
    let end = now.checked_add(duration).ok_or(Refusal::Capacity)?;
    let last = leases.get(&grant.0).copied().unwrap_or(0);
    leases.insert(grant.0, last.max(end));
    Ok(end)
}

pub(super) fn disposal_time(end: Option<u64>, drift: u64) -> Option<u64> {
    match end {
        Some(end) => end.checked_add(drift),
        None => Some(0),
    }
}

pub(super) fn check_disposal(
    authorized: bool,
    serial: u64,
    last_serial: u64,
    enrolled: bool,
    now: u64,
    end: Option<u64>,
    drift: u64,
) -> Result<(), Refusal> {
    if !authorized {
        return Err(Refusal::Unauthorized);
    }
    if serial == 0 || serial > last_serial || enrolled {
        return Err(Refusal::Stale);
    }
    let eligible_at = disposal_time(end, drift).ok_or(Refusal::Capacity)?;
    if now < eligible_at {
        return Err(Refusal::Unavailable);
    }
    Ok(())
}

fn eligible_for_page<W: Ord, E: Ord + Copy>(
    roster: &BTreeMap<W, E>,
    owner: E,
    worker: &W,
    after: Option<E>,
) -> bool {
    !(matches!(after, Some(cursor) if owner <= cursor) || roster.get(worker) == Some(&owner))
}

/// Keep the smallest distinct owners in the page so far.
fn offer_owner<E: Ord + Copy>(page: &mut Vec<E>, owner: E, limit: usize) {
    let mut start = 0;
    let mut end = page.len();
    while start < end {
        let middle = start + (end - start) / 2;
        if page[middle] < owner {
            start = middle + 1;
        } else {
            end = middle;
        }
    }
    if start == limit || (start < page.len() && page[start] == owner) {
        return;
    }
    if page.len() == limit {
        page.pop();
    }
    page.insert(start, owner);
}

pub(super) fn withdrawn_page<K, H: Copy, W: Ord, E: Ord + Copy, F: Fn(H) -> (E, W)>(
    holds: &BTreeMap<K, H>,
    roster: &BTreeMap<W, E>,
    identify: F,
    after: Option<E>,
    limit: usize,
) -> Vec<E> {
    let mut page = Vec::new();
    let mut entries = holds.values();
    loop {
        let Some(entry) = entries.next() else {
            return page;
        };
        let (owner, worker) = identify(*entry);
        if eligible_for_page(roster, owner, &worker, after) {
            {
                offer_owner(&mut page, owner, limit);
            }
        }
    }
}
