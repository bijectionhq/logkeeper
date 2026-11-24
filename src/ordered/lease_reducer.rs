//! Admission and state updates for the reducer's lease and hold maps.

use std::collections::BTreeMap;

use super::{Refusal, lease, replay_bounds, rotation};

pub(super) struct ReadInterval {
    pub(super) empty: bool,
    pub(super) floor: u64,
    pub(super) from: u64,
    pub(super) through: u64,
    pub(super) retained: usize,
}

pub(super) struct CheckpointAccess {
    pub(super) cut: u64,
    pub(super) erasure_floor: u64,
    pub(super) retained: bool,
    pub(super) closed: bool,
}

impl CheckpointAccess {
    pub(super) fn is_open(self) -> bool {
        rotation::admits_history(self.erasure_floor, self.cut) && self.retained && !self.closed
    }
}

pub(super) fn held_indices<E: Eq, H: Eq>(
    principal: Option<E>,
    owner: E,
    stored: Option<H>,
    requested: H,
    interval: ReadInterval,
) -> Result<(usize, usize), Refusal> {
    if principal != Some(owner) {
        return Err(Refusal::Unauthorized);
    }
    if stored != Some(requested) {
        return Err(Refusal::Unavailable);
    }
    if interval.empty {
        Ok((0, 0))
    } else {
        replay_bounds::retained_indices(interval.floor, interval.from, interval.through, interval.retained)
            .ok_or(Refusal::Unavailable)
    }
}

pub(super) struct ReadBasis<W, E, H> {
    pub(super) worker: W,
    pub(super) owner: E,
    pub(super) stored: Option<H>,
    pub(super) requested: H,
    pub(super) interval: ReadInterval,
    pub(super) checkpoint: CheckpointAccess,
}

pub(super) fn issue_read<W: Ord, E: Ord + Copy, H: Eq>(
    roster: &BTreeMap<W, E>,
    leases: &mut BTreeMap<E, u64>,
    principal: Option<E>,
    basis: ReadBasis<W, E, H>,
    now: u64,
    duration: u64,
) -> Result<u64, Refusal> {
    if roster.get(&basis.worker) != Some(&basis.owner) {
        return Err(Refusal::Stale);
    }
    held_indices(principal, basis.owner, basis.stored, basis.requested, basis.interval)?;
    if !basis.checkpoint.is_open() {
        return Err(Refusal::Unavailable);
    }
    let end = now.checked_add(duration).ok_or(Refusal::Capacity)?;
    let last = leases.get(&basis.owner).copied().unwrap_or(0);
    leases.insert(basis.owner, last.max(end));
    Ok(end)
}

pub(super) fn remove_hold<K: Ord, H>(holds: &mut BTreeMap<K, H>, key: &K) {
    holds.remove(key);
}

pub(super) fn has_owner<H: Copy, E: Eq, K, F: Fn(H) -> E>(
    holds: &BTreeMap<K, H>,
    owner: E,
    identify: F,
) -> bool {
    let mut entries = holds.values();
    loop {
        let Some(entry) = entries.next() else {
            return false;
        };
        let observed = identify(*entry);
        if observed == owner {
            return true;
        }
    }
}

pub(super) fn prune_end<W: Ord, E: Ord + Copy, K, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    owner: E,
    identify: F,
) {
    if roster.get(worker) != Some(&owner) {
        let held = has_owner(holds, owner, identify);
        if !held {
            leases.remove(&owner);
        }
    }
}

pub(super) fn dispose_holds<K: Ord + Copy, H: Copy, E: Eq + Copy, F: Fn(H) -> E>(
    holds: &mut BTreeMap<K, H>,
    owner: E,
    identify: &F,
) -> Vec<(K, H)> {
    let mut retired = Vec::new();
    let mut entries = holds.iter();
    loop {
        let Some((key, entry)) = entries.next() else {
            break;
        };
        let observed = identify(*entry);
        if observed == owner {
            retired.push((*key, *entry));
        }
    }
    let mut i = 0;
    while i < retired.len() {
        let key = retired[i].0;
        remove_hold(holds, &key);
        i += 1;
    }
    retired
}

pub(super) fn update_roster<W: Ord + Copy, E>(
    roster: &mut BTreeMap<W, E>,
    worker: &W,
    enrollment: Option<E>,
) {
    if let Some(enrollment) = enrollment {
        roster.insert(*worker, enrollment);
    } else {
        roster.remove(worker);
    }
}

pub(super) fn release_hold<W: Ord, E: Ord + Copy, K: Ord, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &mut BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    key: &K,
    worker: &W,
    owner: E,
    identify: F,
) {
    remove_hold(holds, key);
    prune_end(roster, holds, leases, worker, owner, identify);
}

pub(super) fn dispose_owner<W: Ord, E: Ord + Copy, K: Ord + Copy, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &mut BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    owner: E,
    identify: F,
) -> Vec<(K, H)> {
    let retired = dispose_holds(holds, owner, &identify);
    prune_end(roster, holds, leases, worker, owner, identify);
    retired
}

pub(super) struct ExpiryDisposal {
    pub(super) authorized: bool,
    pub(super) serial: u64,
    pub(super) last_serial: u64,
    pub(super) now: u64,
    pub(super) drift: u64,
}

pub(super) fn dispose_expired<W: Ord, E: Ord + Copy, K: Ord + Copy, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &mut BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    owner: E,
    check: ExpiryDisposal,
    identify: F,
) -> Result<Vec<(K, H)>, Refusal> {
    lease::check_disposal(
        check.authorized,
        check.serial,
        check.last_serial,
        roster.get(worker) == Some(&owner),
        check.now,
        leases.get(&owner).copied(),
        check.drift,
    )?;
    Ok(dispose_owner(roster, holds, leases, worker, owner, identify))
}
