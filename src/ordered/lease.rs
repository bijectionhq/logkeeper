//! Journal time, serving leases and withdrawn-owner selection.

use super::{Refusal, writer};
use std::collections::BTreeMap;

#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
#[cfg(verus_keep_ghost)]
use vstd::laws_eq::obeys_concrete_eq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::{btree_map_inv, btree_map_wf, key_obeys_cmp_spec};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::OrdSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

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

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out == if *old(position) as int + 1 != next_position { Err(ApplyError::Position) }
            else if next_time < *old(time) { Err(ApplyError::Time) } else { Ok(()) },
        *final(position) == if out is Ok { next_position } else { *old(position) },
        *final(time) == if out is Ok { next_time } else { *old(time) },
))]
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

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster),
        btree_map_inv(old(leases)),
    ensures
        out == if principal != Some(grant.0) { Err(Refusal::Unauthorized) }
            else if current != Some(grant) || roster@.get(*worker) != Some(grant.0) {
                Err(Refusal::Stale)
            } else if now as int + duration > u64::MAX { Err(Refusal::Capacity) }
            else { Ok((now as int + duration) as u64) },
        btree_map_inv(final(leases)),
        final(leases)@ == match out {
            Ok(end) => old(leases)@.insert(grant.0, retained_end(old(leases)@.get(grant.0), end)),
            Err(_) => old(leases)@,
        },
))]
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
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_ref_obeys_concrete_eq,
            vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<&E>>());
        reveal(obeys_concrete_eq);
    }
    if roster.get(worker) != Some(&grant.0) {
        return Err(Refusal::Stale);
    }
    let end = now.checked_add(duration).ok_or(Refusal::Capacity)?;
    let last = leases.get(&grant.0).copied().unwrap_or(0);
    leases.insert(grant.0, last.max(end));
    Ok(end)
}

#[cfg(verus_keep_ghost)]
verus! {
pub open spec fn retained_end(old_end: Option<u64>, end: u64) -> u64 {
    match old_end {
        Some(previous) if previous > end => previous,
        _ => end,
    }
}

pub open spec fn checked_disposal_time(end: Option<u64>, drift: u64) -> Option<u64> {
    match end {
        None => Some(0),
        Some(time) if time as int + drift <= u64::MAX => Some((time as int + drift) as u64),
        Some(_) => None,
    }
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == checked_disposal_time(end, drift),
))]
pub(super) fn disposal_time(end: Option<u64>, drift: u64) -> Option<u64> {
    match end {
        Some(end) => end.checked_add(drift),
        None => Some(0),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if !authorized { Err(Refusal::Unauthorized) }
        else if serial == 0 || serial > last_serial || enrolled { Err(Refusal::Stale) }
        else { match checked_disposal_time(end, drift) {
            Some(due) if now < due => Err(Refusal::Unavailable),
            Some(_) => Ok(()),
            None => Err(Refusal::Capacity),
        } },
))]
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

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn owner_before<E: Ord>(left: E, right: E) -> bool {
    left.cmp_spec(&right) is Less
}

type HoldProjection<H, E, W> = spec_fn(H) -> (E, W);

pub open spec fn owner_page<E: Ord>(page: Seq<E>, eligible: ISet<E>, limit: nat) -> bool {
    &&& page.len() <= limit
    &&& forall|i: int, j: int| 0 <= i < j < page.len() ==> #[trigger] owner_before(page[i], page[j])
    &&& forall|owner: E| #[trigger] page.contains(owner) ==> eligible.contains(owner)
    &&& forall|owner: E| #[trigger] eligible.contains(owner) && !page.contains(owner) ==>
        page.len() == limit &&
            forall|i: int| 0 <= i < page.len() ==> #[trigger] owner_before(page[i], owner)
}

pub open spec fn eligible_owner<W, E: Ord>(
    roster: Map<W, E>, owner: E, worker: W, after: Option<E>,
) -> bool {
    &&& match after { Some(cursor) => owner_before(cursor, owner), None => true }
    &&& roster.get(worker) != Some(owner)
}

pub open spec fn qualifying_owners<H, W, E: Ord>(
    holds: Set<H>, roster: Map<W, E>, identify: spec_fn(H) -> (E, W), after: Option<E>,
) -> ISet<E> {
    ISet::new(|owner: E| exists|hold: H| #[trigger] holds.contains(hold) &&
        (owner == identify(hold).0 && eligible_owner(roster, owner, identify(hold).1, after)))
}

proof fn preserves_page_on_insert<E: Ord>(
    prior: Seq<E>, next: Seq<E>, eligible: ISet<E>, owner: E, index: int, limit: nat,
)
    requires
        obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        owner_page(prior, eligible, limit), 0 <= index <= prior.len(), index < limit,
        forall|i: int| 0 <= i < index ==> #[trigger] owner_before(prior[i], owner),
        forall|i: int| index <= i < prior.len() ==> #[trigger] owner_before(owner, prior[i]),
        next == prior.take(if prior.len() == limit { prior.len() - 1 } else { prior.len() as int })
            .insert(index, owner),
    ensures owner_page(next, eligible.insert(owner), limit),
{
    broadcast use vstd::seq::group_seq_axioms, vstd::set::group_set_lemmas, vstd::iset::group_iset_lemmas;
    reveal(vstd::laws_cmp::obeys_cmp_ord);
    reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    let keep = if prior.len() == limit { prior.len() - 1 } else { prior.len() as int };
    assert(next.len() == keep + 1);
    assert forall|i: int| 0 <= i < next.len() implies
        next[i] == if i < index { prior[i] }
            else if i == index { owner } else { prior[i - 1] } by {}
    assert forall|i: int, j: int| 0 <= i < j < next.len() implies
        #[trigger] owner_before(next[i], next[j]) by {
        if i == index {
            assert(owner_before(owner, prior[j - 1]));
        } else if j == index {
            assert(owner_before(prior[i], owner));
        } else {
            let a = if i < index { i } else { i - 1 };
            let b = if j < index { j } else { j - 1 };
            assert(owner_before(prior[a], prior[b]));
        }
    }
    assert forall|candidate: E| #[trigger] next.contains(candidate) implies
        eligible.insert(owner).contains(candidate) by {
        let i = choose|i: int| 0 <= i < next.len() && next[i] == candidate;
        if i != index {
            assert(prior.contains(candidate));
        }
    }
    assert forall|missed: E| #[trigger] eligible.insert(owner).contains(missed)
        && !next.contains(missed) implies
        next.len() == limit &&
            forall|i: int| 0 <= i < next.len() ==> #[trigger] owner_before(next[i], missed) by {
        assert(next[index] == owner);
        assert(next.contains(owner));
        if prior.contains(missed) {
            let old_index = choose|i: int| 0 <= i < prior.len() && prior[i] == missed;
            if old_index < keep {
                let new_index = if old_index < index { old_index } else { old_index + 1 };
                assert(next[new_index] == missed);
                assert(next.contains(missed));
            }
            assert(old_index == prior.len() - 1 && prior.len() == limit);
            assert forall|i: int| 0 <= i < next.len() implies #[trigger] owner_before(next[i], missed) by {
                if i == index {
                    assert(owner_before(owner, prior[old_index]));
                } else {
                    let a = if i < index { i } else { i - 1 };
                    assert(owner_before(prior[a], prior[old_index]));
                }
            }
        } else {
            assert(eligible.contains(missed));
            assert forall|i: int| 0 <= i < next.len() implies #[trigger] owner_before(next[i], missed) by {
                if i == index {
                    assert(owner_before(owner, prior[index]));
                    assert(owner_before(prior[index], missed));
                    assert(owner_before(owner, missed));
                } else {
                    let a = if i < index { i } else { i - 1 };
                    assert(owner_before(prior[a], missed));
                }
            }
        }
    }
}

proof fn partition_qualifying_owners<H, W, E: Ord>(
    remaining: Set<H>, roster: Map<W, E>, identify: spec_fn(H) -> (E, W), after: Option<E>, hold: H,
)
    ensures qualifying_owners(remaining.insert(hold), roster, identify, after) =~=
        if eligible_owner(roster, identify(hold).0, identify(hold).1, after) {
            qualifying_owners(remaining, roster, identify, after).insert(identify(hold).0)
        } else {
            qualifying_owners(remaining, roster, identify, after)
        },
{
    broadcast use vstd::set::group_set_lemmas, vstd::iset::group_iset_lemmas;
    let before = qualifying_owners(remaining.insert(hold), roster, identify, after);
    let after_set = qualifying_owners(remaining, roster, identify, after);
    assert forall|owner: E| #[trigger] before.contains(owner) implies
        after_set.contains(owner) ||
            (owner == identify(hold).0 && eligible_owner(roster, owner, identify(hold).1, after)) by {
        let chosen = choose|candidate: H| #[trigger] remaining.insert(hold).contains(candidate) &&
            owner == identify(candidate).0 && eligible_owner(roster, owner, identify(candidate).1, after);
        if chosen != hold {
            assert(remaining.contains(chosen));
        }
    }
    assert forall|owner: E| #[trigger] after_set.contains(owner) ||
        (owner == identify(hold).0 && eligible_owner(roster, owner, identify(hold).1, after))
        implies before.contains(owner) by {
        if after_set.contains(owner) {
            let chosen = choose|candidate: H| #[trigger] remaining.contains(candidate) &&
                owner == identify(candidate).0 && eligible_owner(roster, owner, identify(candidate).1, after);
            assert(remaining.insert(hold).contains(chosen));
        } else {
            assert(remaining.insert(hold).contains(hold));
        }
    }
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(), obeys_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster),
    ensures out == eligible_owner(roster@, owner, *worker, after),
))]
fn eligible_for_page<W: Ord, E: Ord + Copy>(
    roster: &BTreeMap<W, E>,
    owner: E,
    worker: &W,
    after: Option<E>,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_ref_obeys_concrete_eq,
            vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<&E>>());
        reveal(obeys_concrete_eq);
        reveal(vstd::laws_cmp::obeys_cmp_ord);
        reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
        reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    }
    !(matches!(after, Some(cursor) if owner <= cursor) || roster.get(worker) == Some(&owner))
}

/// Keep the smallest distinct owners in the page so far.
#[cfg_attr(verus_keep_ghost, verus_spec(
    with Ghost(eligible): Ghost<ISet<E>>
    requires obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(), obeys_concrete_eq::<E>(),
        owner_page(old(page)@, eligible, limit as nat),
    ensures owner_page(final(page)@, eligible.insert(owner), limit as nat),
))]
fn offer_owner<E: Ord + Copy>(page: &mut Vec<E>, owner: E, limit: usize) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost prior = page@; }
    let mut start = 0;
    let mut end = page.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            start <= end <= prior.len(), page@ == prior,
            obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(), obeys_concrete_eq::<E>(),
            owner_page(prior, eligible, limit as nat),
            forall|i: int| 0 <= i < start ==> #[trigger] owner_before(prior[i], owner),
            forall|i: int| end <= i < prior.len() ==> !#[trigger] owner_before(prior[i], owner),
        decreases end - start,
    ))]
    while start < end {
        let middle = start + (end - start) / 2;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(vstd::laws_cmp::obeys_cmp_ord);
            reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
            reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
        }
        if page[middle] < owner {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i: int| 0 <= i < middle implies #[trigger] owner_before(prior[i], owner) by {
                    assert(owner_before(prior[i], prior[middle as int]));
                }
            }
            start = middle + 1;
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i: int| middle < i < prior.len() implies
                    !#[trigger] owner_before(prior[i], owner) by {
                    assert(owner_before(prior[middle as int], prior[i]));
                }
            }
            end = middle;
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::seq::group_seq_axioms, vstd::set::group_set_lemmas, vstd::iset::group_iset_lemmas;
        reveal(obeys_concrete_eq);
        reveal(vstd::laws_cmp::obeys_cmp_ord);
        reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
        reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    }
    if start == limit || (start < page.len() && page[start] == owner) {
        #[cfg(verus_keep_ghost)]
        proof! {
            if start != limit {
                assert(prior.contains(owner));
            }
            assert(owner_page(prior, eligible.insert(owner), limit as nat));
        }
        return;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i: int| start <= i < prior.len() implies
            #[trigger] owner_before(owner, prior[i]) by {
            assert(prior[start as int] != owner);
            assert(!owner_before(prior[start as int], owner));
            assert(owner_before(owner, prior[start as int]));
            if start < i {
                assert(owner_before(prior[start as int], prior[i]));
            }
        }
    }
    if page.len() == limit {
        page.pop();
    }
    page.insert(start, owner);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(page@ =~= prior.take(if prior.len() == limit { prior.len() - 1 } else { prior.len() as int })
            .insert(start as int, owner));
        preserves_page_on_insert(prior, page@, eligible, owner, start as int, limit as nat);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    with Ghost(projection): Ghost<HoldProjection<H, E, W>>
    requires key_obeys_cmp_spec::<K>(), btree_map_wf(holds),
        obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(), obeys_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: (E, W)| identify.ensures((entry,), result) ==> result == projection(entry),
    ensures owner_page(out@, qualifying_owners(holds@.values(), roster@, projection, after), limit as nat),
))]
pub(super) fn withdrawn_page<K, H: Copy, W: Ord, E: Ord + Copy, F: Fn(H) -> (E, W)>(
    holds: &BTreeMap<K, H>,
    roster: &BTreeMap<W, E>,
    identify: F,
    after: Option<E>,
    limit: usize,
) -> Vec<E> {
    #[cfg(verus_keep_ghost)]
    proof! { broadcast use vstd::seq::group_seq_axioms, vstd::set::group_set_lemmas, vstd::iset::group_iset_lemmas; }
    let mut page = Vec::new();
    let mut entries = holds.values();
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = holds@.values();
        let ghost mut seen = ISet::<E>::empty();
        let ghost mut remaining = entries.remaining().unref();
        let ghost wanted = qualifying_owners(original, roster@, projection, after);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(owner_page(page@, seen, limit as nat));
        assert(wanted =~= seen.union(qualifying_owners(remaining.to_set(), roster@, projection, after)));
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            entries.obeys_prophetic_iter_laws(),
            entries.remaining().unref() == remaining,
            entries.decrease() is Some,
            entries.remaining().len() == remaining.len(),
            forall|i: int| 0 <= i < remaining.len() ==> *entries.remaining()[i] == #[trigger] remaining[i],
            obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(), obeys_concrete_eq::<E>(),
            obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster),
            forall|entry: H| identify.requires((entry,)),
            forall|entry: H, result: (E, W)| identify.ensures((entry,), result) ==> result == projection(entry),
            owner_page(page@, seen, limit as nat),
            wanted == qualifying_owners(holds@.values(), roster@, projection, after),
            wanted == seen.union(qualifying_owners(remaining.to_set(), roster@, projection, after)),
        decreases entries.decrease()->Some_0,
    ))]
    loop {
        let Some(entry) = entries.next() else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(remaining.len() == 0);
                assert(qualifying_owners(remaining.to_set(), roster@, projection, after) =~= ISet::empty());
                assert(wanted =~= seen);
                assert(owner_page(page@, wanted, limit as nat));
            }
            return page;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(*entry == remaining[0]);
            let tail = entries.remaining().unref();
            assert(tail =~= remaining.skip(1));
            assert(remaining =~= seq![*entry] + tail);
            vstd::seq_lib::seq_to_set_distributes_over_add(seq![*entry], tail);
            assert(remaining.to_set() =~= tail.to_set().insert(*entry));
            partition_qualifying_owners(tail.to_set(), roster@, projection, after, *entry);
            remaining = tail;
        }
        let (owner, worker) = identify(*entry);
        if eligible_for_page(roster, owner, &worker, after) {
            {
                #[cfg_attr(verus_keep_ghost, verus_spec(with Ghost(seen)))]
                offer_owner(&mut page, owner, limit);
            }
            #[cfg(verus_keep_ghost)]
            proof! { seen = seen.insert(owner); }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(wanted =~= seen.union(qualifying_owners(remaining.to_set(), roster@, projection, after)));
        }
    }
}
