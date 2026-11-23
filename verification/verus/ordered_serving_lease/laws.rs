use crate::production::{
    advance_decision, check_disposal, issue, owner_page, qualifying_owners,
};
use crate::writer::{Authority, insert_hold};
use std::collections::BTreeMap;
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
use vstd::laws_eq::obeys_concrete_eq;
use vstd::prelude::*;
use vstd::std_specs::btree::{btree_map_inv, btree_map_wf, key_obeys_cmp_spec};
use vstd::std_specs::cmp::OrdSpec;

verus! {

// DisposalLease.decision_time.
pub open spec fn decision_time(previous: u64, incoming: u64) -> Option<u64> {
    if previous <= incoming { Some(incoming) } else { None }
}

// DisposalLease.lease_end, with the X2 grant identity from authorize_writer.
pub open spec fn lease_end<E>(
    principal: Option<E>, current: Option<(E, u64, u64)>, grant: (E, u64, u64),
    enrolled: Option<E>, now: u64, duration: u64,
) -> Option<u64> {
    if principal == Some(grant.0) && current == Some(grant) && enrolled == Some(grant.0)
        && now as int + duration <= u64::MAX {
        Some((now as int + duration) as u64)
    } else {
        None
    }
}

// DisposalLease.withdrawn, .MayDispose and .Admits.
pub open spec fn withdrawn(serial: u64, last_serial: u64, enrolled: bool) -> bool {
    0 < serial <= last_serial && !enrolled
}

pub open spec fn may_dispose(end: u64, drift: u64, now: u64) -> bool {
    end as int + drift <= now
}

pub open spec fn admits(end: u64, worker_clock: u64) -> bool {
    worker_clock < end
}

fn decision_time_is_monotone(
    position: &mut u64, time: &mut u64, next_position: u64, next_time: u64,
) {
    let previous = *time;
    let result = advance_decision(position, time, next_position, next_time);
    assert(*time >= previous
        && (result is Ok ==> decision_time(previous, next_time) == Some(*time)));
}

fn lease_requires_current_enrolled_grant<W: Ord + Copy, E: Ord + Copy>(
    roster: &BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>, worker: W,
    principal: Option<E>, current: Option<(E, u64, u64)>, grant: (E, u64, u64),
    now: u64, duration: u64,
)
    requires obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster), btree_map_inv(old(leases)),
{
    let ghost previous = leases@;
    let result = issue(roster, leases, &worker, principal, current, grant, now, duration);
    assert(result.ok() == lease_end(principal, current, grant, roster@.get(worker), now, duration)
        && match result {
            Ok(end) => leases@.get(grant.0) matches Some(retained) && retained >= end
                && (previous.get(grant.0) matches Some(old_end) ==> retained >= old_end),
            Err(_) => leases@ == previous,
        });
}

fn disposal_requires_withdrawal_and_drift(
    authorized: bool, serial: u64, last_serial: u64, enrolled: bool,
    now: u64, end: Option<u64>, drift: u64, worker_clock: u64,
)
    requires now as int <= worker_clock as int + drift,
{
    let result = check_disposal(authorized, serial, last_serial, enrolled, now, end, drift);
    assert(
        (result is Ok) == (authorized && withdrawn(serial, last_serial, enrolled)
            && match end { Some(t) => may_dispose(t, drift, now), None => true })
        && (end matches Some(t) ==> (result is Ok ==> !admits(t, worker_clock)))
    );
}

// A serial below the high-water mark and an absent roster slot suffice
// for a no-lease request. The gate has no historical enrollment ledger.
fn absent_unleased_identity_is_disposable() {
    let result = check_disposal(true, 1, 1, false, 0, None, 100);
    assert(result is Ok);
}

// DisposalLease.owner_page over the exact held-enrollment projection.
pub open spec fn withdrawn_owners<H, W, E: Ord>(
    holds: Set<H>, roster: Map<W, E>, projection: spec_fn(H) -> (E, W), after: Option<E>,
) -> ISet<E> {
    ISet::new(|owner: E| exists|entry: H| #[trigger] holds.contains(entry)
        && owner == projection(entry).0 && roster.get(projection(entry).1) != Some(owner)
        && (after matches Some(cursor) ==> cursor.cmp_spec(&owner) is Less))
}

fn withdrawn_owner_page_is_exact_and_bounded<K, H: Copy, W: Ord, E: Ord + Copy, F: Fn(H) -> (E, W)>(
    holds: &BTreeMap<K, H>, roster: &BTreeMap<W, E>, identify: F, after: Option<E>, limit: usize,
    Ghost(projection): Ghost<spec_fn(H) -> (E, W)>,
)
    requires key_obeys_cmp_spec::<K>(), btree_map_wf(holds),
        obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(), obeys_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, pair: (E, W)| identify.ensures((entry,), pair) ==> pair == projection(entry),
{
    let page = #[verus_spec(with Ghost(projection))]
        crate::production::withdrawn_page(holds, roster, identify, after, limit);
    proof {
        broadcast use vstd::iset::group_iset_lemmas;
        assert(qualifying_owners(holds@.values(), roster@, projection, after)
            =~= withdrawn_owners(holds@.values(), roster@, projection, after)
            && owner_page(page@, withdrawn_owners(holds@.values(), roster@, projection, after), limit as nat));
    }
}

fn grant_change_preserves_holds<K: Ord + Copy, H, G>(
    holds: &mut BTreeMap<K, H>, id: K, recovery: H,
    authority: &mut Authority<G>, epoch: u64, generation: u64, grant: G,
)
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        !old(holds)@.contains_key(id),
{
    let ghost previous = holds@;
    insert_hold(holds, id, recovery);
    authority.install(epoch, generation, grant);
    assert(forall|key: K| #[trigger] previous.contains_key(key) ==>
        holds@.contains_key(key) && holds@[key] == previous[key]);
}

}
