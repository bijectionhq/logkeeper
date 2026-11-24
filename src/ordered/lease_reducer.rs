//! Admission and state updates for the reducer's lease and hold maps.

use std::collections::BTreeMap;

use super::{Refusal, lease, replay_bounds, rotation};

#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
#[cfg(verus_keep_ghost)]
use vstd::laws_eq::obeys_concrete_eq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::{btree_map_inv, btree_map_wf, key_obeys_cmp_spec};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

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
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == (self.erasure_floor <= self.cut && self.retained && !self.closed),
    ))]
    pub(super) fn is_open(self) -> bool {
        rotation::admits_history(self.erasure_floor, self.cut) && self.retained && !self.closed
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn interval_available(interval: ReadInterval) -> bool {
    interval.empty || (interval.floor <= interval.from <= interval.through
        && interval.through as int - interval.floor <= interval.retained)
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<E>(), obeys_concrete_eq::<H>(),
    ensures out == if principal != Some(owner) { Err(Refusal::Unauthorized) }
        else if stored != Some(requested) || !interval_available(interval) { Err(Refusal::Unavailable) }
        else if interval.empty { Ok((0, 0)) }
        else { Ok(((interval.from as int - interval.floor) as usize,
            (interval.through as int - interval.floor) as usize)) },
))]
pub(super) fn held_indices<E: Eq, H: Eq>(
    principal: Option<E>,
    owner: E,
    stored: Option<H>,
    requested: H,
    interval: ReadInterval,
) -> Result<(usize, usize), Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<E>>());
        assert(obeys_concrete_eq::<Option<H>>());
        reveal(obeys_concrete_eq);
    }
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

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<E>(), obeys_concrete_eq::<H>(),
        obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
    ensures out == if roster@.get(basis.worker) != Some(basis.owner) { Err(Refusal::Stale) }
        else if principal != Some(basis.owner) { Err(Refusal::Unauthorized) }
        else if basis.stored != Some(basis.requested) || !interval_available(basis.interval)
            || basis.checkpoint.cut < basis.checkpoint.erasure_floor
            || !basis.checkpoint.retained || basis.checkpoint.closed { Err(Refusal::Unavailable) }
        else if now as int + duration > u64::MAX { Err(Refusal::Capacity) }
        else { Ok((now as int + duration) as u64) },
        btree_map_inv(final(leases)),
        final(leases)@ == match out {
            Ok(end) => old(leases)@.insert(basis.owner,
                super::lease::retained_end(old(leases)@.get(basis.owner), end)),
            Err(_) => old(leases)@,
        },
))]
pub(super) fn issue_read<W: Ord, E: Ord + Copy, H: Eq>(
    roster: &BTreeMap<W, E>,
    leases: &mut BTreeMap<E, u64>,
    principal: Option<E>,
    basis: ReadBasis<W, E, H>,
    now: u64,
    duration: u64,
) -> Result<u64, Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_ref_obeys_concrete_eq,
            vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<&E>>());
        reveal(obeys_concrete_eq);
    }
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

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
    ensures btree_map_inv(final(holds)), final(holds)@ == old(holds)@.remove(*key),
))]
pub(super) fn remove_hold<K: Ord, H>(holds: &mut BTreeMap<K, H>, key: &K) {
    holds.remove(key);
}

#[cfg(verus_keep_ghost)]
verus! {
type OwnerProjection<H, E> = spec_fn(H) -> E;

pub(crate) open spec fn held_by<K, H, E>(
    holds: Map<K, H>, owner: E, identify: spec_fn(H) -> E,
) -> bool {
    exists|entry: H| #[trigger] holds.values().contains(entry) && identify(entry) == owner
}

pub(crate) open spec fn after_prune<W, E, K, H>(
    roster: Map<W, E>, holds: Map<K, H>, leases: Map<E, u64>,
    worker: W, owner: E, identify: spec_fn(H) -> E,
) -> Map<E, u64> {
    if roster.get(worker) == Some(owner) || held_by(holds, owner, identify) { leases }
    else { leases.remove(owner) }
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(projection): Ghost<OwnerProjection<H, E>>
    requires key_obeys_cmp_spec::<K>(), btree_map_wf(holds), obeys_concrete_eq::<E>(),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures out == held_by(holds@, owner, projection),
))]
fn has_owner<H: Copy, E: Eq, K, F: Fn(H) -> E>(
    holds: &BTreeMap<K, H>,
    owner: E,
    identify: F,
) -> bool {
    let mut entries = holds.values();
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = entries.remaining();
        let ghost mut seen = 0int;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::set::group_set_lemmas;
        assert(original.unref().to_set() =~= holds@.values());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            entries.obeys_prophetic_iter_laws(), entries.decrease() is Some,
            entries.remaining() == original.skip(seen),
            entries.remaining().len() == original.len() - seen,
            0 <= seen <= original.len(),
            original.unref().to_set() == holds@.values(),
            obeys_concrete_eq::<E>(),
            forall|i: int| 0 <= i < seen ==> projection(*#[trigger] original[i]) != owner,
            forall|entry: H| identify.requires((entry,)),
            forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
        decreases entries.decrease()->Some_0,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost pending = entries.remaining(); }
        let Some(entry) = entries.next() else {
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::seq::group_seq_axioms, vstd::set::group_set_lemmas;
                assert(seen == original.len());
                assert forall|row: H| #[trigger] holds@.values().contains(row)
                    implies projection(row) != owner by {
                    let i = choose|i: int| 0 <= i < original.len() && original.unref()[i] == row;
                    assert(*original[i] == row);
                };
            }
            return false;
        };
        let observed = identify(*entry);
        #[cfg(verus_keep_ghost)]
        proof! {
            broadcast use vstd::seq::group_seq_axioms, vstd::set::group_set_lemmas;
            reveal(obeys_concrete_eq);
            assert(pending.len() > 0);
            assert(*entry == *pending[0]);
            assert(pending == original.skip(seen));
            assert(pending[0] == original[seen]);
            assert(original.unref()[seen] == *entry);
            assert(original.unref().to_set().contains(*entry));
            assert((observed == owner) == (projection(*entry) == owner));
        }
        if observed == owner {
            return true;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            broadcast use vstd::seq::group_seq_axioms;
            assert(entries.remaining() == pending.skip(1));
            seen = seen + 1;
            assert(entries.remaining() =~= original.skip(seen));
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    with Ghost(projection): Ghost<OwnerProjection<H, E>>
    requires key_obeys_cmp_spec::<K>(), btree_map_wf(holds),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures btree_map_inv(final(leases)),
        final(leases)@ == after_prune(roster@, holds@, old(leases)@, *worker, owner, projection),
))]
pub(super) fn prune_end<W: Ord, E: Ord + Copy, K, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    owner: E,
    identify: F,
) {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_ref_obeys_concrete_eq,
            vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<&E>>());
        reveal(obeys_concrete_eq);
    }
    if roster.get(worker) != Some(&owner) {
        #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(projection)))]
        let held = has_owner(holds, owner, identify);
        if !held {
            leases.remove(&owner);
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn after_disposal<H, E>(
    row: Option<H>, owner: E, identify: spec_fn(H) -> E,
) -> Option<H> {
    if row matches Some(entry) && identify(entry) == owner { None } else { row }
}

pub(crate) open spec fn retired_rows<K, H, E>(
    retired: Seq<(K, H)>, previous: Map<K, H>, owner: E, identify: spec_fn(H) -> E,
) -> bool {
    forall|key: K, entry: H| #[trigger] retired.contains((key, entry)) <==>
        previous.get(key) == Some(entry) && identify(entry) == owner
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(projection): Ghost<OwnerProjection<H, E>>
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        obeys_concrete_eq::<E>(),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures btree_map_inv(final(holds)),
        forall|key: K| #[trigger] final(holds)@.get(key) ==
            after_disposal(old(holds)@.get(key), owner, projection),
        retired_rows(out@, old(holds)@, owner, projection),
))]
pub(super) fn dispose_holds<K: Ord + Copy, H: Copy, E: Eq + Copy, F: Fn(H) -> E>(
    holds: &mut BTreeMap<K, H>,
    owner: E,
    identify: &F,
) -> Vec<(K, H)> {
    let mut retired = Vec::new();
    let mut entries = holds.iter();
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = entries.remaining();
        let ghost before = holds@;
        let ghost mut visited = 0int;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|key: K, value: H| before.contains_pair(key, value) <==>
            (exists|j: int| 0 <= j < original.len()
                && *original[j].0 == key && *original[j].1 == value) by {}
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            entries.obeys_prophetic_iter_laws(), entries.decrease() is Some,
            entries.remaining() == original.skip(visited),
            entries.remaining().len() == original.len() - visited,
            0 <= visited <= original.len(),
            obeys_concrete_eq::<E>(),
            forall|entry: H| identify.requires((entry,)),
            forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
            forall|key: K, value: H| #[trigger] retired@.contains((key, value)) <==>
                projection(value) == owner && (exists|j: int| 0 <= j < visited
                    && *original[j].0 == key && *original[j].1 == value),
        ensures visited == original.len(),
        decreases entries.decrease()->Some_0,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pending = entries.remaining();
            let ghost selected = retired@;
        }
        let Some((key, entry)) = entries.next() else {
            #[cfg(verus_keep_ghost)]
            proof! { assert(visited == original.len()); }
            break;
        };
        let observed = identify(*entry);
        #[cfg(verus_keep_ghost)]
        proof! {
            broadcast use vstd::seq::group_seq_axioms;
            reveal(obeys_concrete_eq);
            assert(pending.len() > 0);
            assert((key, entry) == pending[0]);
            assert(pending[0] == original[visited]);
            assert((observed == owner) == (projection(*entry) == owner));
        }
        if observed == owner {
            retired.push((*key, *entry));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            broadcast use vstd::seq::group_seq_axioms;
            assert(retired@ == if projection(*entry) == owner {
                selected.push((*key, *entry))
            } else { selected });
            if projection(*entry) == owner {
                assert(retired@[selected.len() as int] == (*key, *entry));
                assert(retired@.contains((*key, *entry)));
            }
            assert forall|k: K, value: H| #[trigger] retired@.contains((k, value)) <==>
                projection(value) == owner && (exists|j: int| 0 <= j <= visited
                    && *original[j].0 == k && *original[j].1 == value) by {
                if retired@.contains((k, value)) {
                    if selected.contains((k, value)) {
                        let j = choose|j: int| 0 <= j < visited
                            && *original[j].0 == k && *original[j].1 == value;
                    } else {
                        let i = choose|i: int| 0 <= i < retired@.len() && retired@[i] == (k, value);
                        if i < selected.len() {
                            assert(selected.contains((k, value)));
                        }
                        assert((k, value) == (*key, *entry));
                        assert(projection(value) == owner);
                        assert(*original[visited].0 == k && *original[visited].1 == value);
                    }
                }
                if projection(value) == owner && (exists|j: int| 0 <= j <= visited
                    && *original[j].0 == k && *original[j].1 == value)
                {
                    let j = choose|j: int| 0 <= j <= visited
                        && *original[j].0 == k && *original[j].1 == value;
                    if j == visited {
                        assert((k, value) == (*key, *entry));
                        assert(retired@.contains((*key, *entry)));
                    } else {
                        assert(selected.contains((k, value)));
                        let i = choose|i: int| 0 <= i < selected.len() && selected[i] == (k, value);
                        assert(retired@[i] == (k, value));
                    }
                }
            }
            visited = visited + 1;
            assert(entries.remaining() =~= original.skip(visited));
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(visited == original.len());
        assert forall|key: K, entry: H| #[trigger] retired@.contains((key, entry)) <==>
            before.get(key) == Some(entry) && projection(entry) == owner by {}
    }
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= retired.len(), btree_map_inv(holds), obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(),
            forall|key: K| #[trigger] holds@.get(key) ==
                if exists|j: int| 0 <= j < i && #[trigger] retired@[j].0 == key {
                    None
                } else {
                    before.get(key)
                },
        decreases retired.len() - i,
    ))]
    while i < retired.len() {
        let key = retired[i].0;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost prior = holds@; }
        remove_hold(holds, &key);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|k: K| #[trigger] holds@.get(k) ==
                if exists|j: int| 0 <= j <= i && #[trigger] retired@[j].0 == k {
                    None
                } else {
                    before.get(k)
                } by {
                if k == key {
                    assert(retired@[i as int].0 == k);
                } else if exists|j: int| 0 <= j <= i && #[trigger] retired@[j].0 == k {
                    let j = choose|j: int| 0 <= j <= i && #[trigger] retired@[j].0 == k;
                    assert(j < i);
                }
                assert(holds@.get(k) == if k == key { None } else { prior.get(k) });
            }
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::seq::group_seq_axioms;
        assert forall|key: K| #[trigger] holds@.get(key) ==
            after_disposal(before.get(key), owner, projection) by {
            if before.get(key).is_some() && projection(before.get(key).unwrap()) == owner {
                let entry = before.get(key).unwrap();
                assert(retired@.contains((key, entry)));
                let j = choose|j: int| 0 <= j < retired.len() && retired@[j] == (key, entry);
                assert(retired@[j].0 == key);
            } else if exists|j: int| 0 <= j < retired.len() && #[trigger] retired@[j].0 == key {
                let j = choose|j: int| 0 <= j < retired.len() && #[trigger] retired@[j].0 == key;
                let row = retired@[j];
                assert(retired@.contains((key, row.1)));
            }
        }
    }
    retired
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(old(roster)),
    ensures btree_map_inv(final(roster)),
        final(roster)@ == match enrollment {
            Some(owner) => old(roster)@.insert(*worker, owner),
            None => old(roster)@.remove(*worker),
        },
))]
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

#[cfg_attr(verus_keep_ghost, verus_spec(
    with Ghost(projection): Ghost<OwnerProjection<H, E>>
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures btree_map_inv(final(holds)), btree_map_inv(final(leases)),
        final(holds)@ == old(holds)@.remove(*key),
        final(leases)@ == after_prune(roster@, final(holds)@, old(leases)@, *worker, owner, projection),
))]
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
    {
        #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(projection)))]
        prune_end(roster, holds, leases, worker, owner, identify);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(projection): Ghost<OwnerProjection<H, E>>
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures btree_map_inv(final(holds)), btree_map_inv(final(leases)),
        forall|key: K| #[trigger] final(holds)@.get(key) ==
            after_disposal(old(holds)@.get(key), owner, projection),
        retired_rows(out@, old(holds)@, owner, projection),
        final(leases)@ == after_prune(roster@, final(holds)@, old(leases)@, *worker, owner, projection),
))]
pub(super) fn dispose_owner<W: Ord, E: Ord + Copy, K: Ord + Copy, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &mut BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    owner: E,
    identify: F,
) -> Vec<(K, H)> {
    #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(projection)))]
    let retired = dispose_holds(holds, owner, &identify);
    {
        #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(projection)))]
        prune_end(roster, holds, leases, worker, owner, identify);
    }
    retired
}

pub(super) struct ExpiryDisposal {
    pub(super) authorized: bool,
    pub(super) serial: u64,
    pub(super) last_serial: u64,
    pub(super) now: u64,
    pub(super) drift: u64,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(projection): Ghost<OwnerProjection<H, E>>
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures btree_map_inv(final(holds)), btree_map_inv(final(leases)),
        (out is Ok) == (check.authorized && 0 < check.serial <= check.last_serial
            && roster@.get(*worker) != Some(owner)
            && (old(leases)@.get(owner) matches Some(end) ==> end as int + check.drift <= check.now)),
        match out {
            Ok(retired) => retired_rows(retired@, old(holds)@, owner, projection)
                && (forall|key: K| #[trigger] final(holds)@.get(key) ==
                    after_disposal(old(holds)@.get(key), owner, projection))
                && final(leases)@ == after_prune(
                    roster@, final(holds)@, old(leases)@, *worker, owner, projection),
            Err(_) => final(holds)@ == old(holds)@ && final(leases)@ == old(leases)@,
        },
))]
pub(super) fn dispose_expired<W: Ord, E: Ord + Copy, K: Ord + Copy, H: Copy, F: Fn(H) -> E>(
    roster: &BTreeMap<W, E>,
    holds: &mut BTreeMap<K, H>,
    leases: &mut BTreeMap<E, u64>,
    worker: &W,
    owner: E,
    check: ExpiryDisposal,
    identify: F,
) -> Result<Vec<(K, H)>, Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_ref_obeys_concrete_eq,
            vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<&E>>());
        reveal(obeys_concrete_eq);
    }
    lease::check_disposal(
        check.authorized,
        check.serial,
        check.last_serial,
        roster.get(worker) == Some(&owner),
        check.now,
        leases.get(&owner).copied(),
        check.drift,
    )?;
    {
        #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(projection)))]
        let retired = dispose_owner(roster, holds, leases, worker, owner, identify);
        Ok(retired)
    }
}
