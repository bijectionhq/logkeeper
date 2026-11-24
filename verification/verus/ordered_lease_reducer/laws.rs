use crate::production::{
    CheckpointAccess, ExpiryDisposal, ReadBasis, ReadInterval, held_by, issue_read,
    update_roster,
};
use crate::{lease, rotation, writer};
use crate::Refusal;
use std::collections::BTreeMap;
use vstd::laws_cmp::{obeys_cmp, obeys_cmp_concrete_eq};
use vstd::laws_eq::obeys_concrete_eq;
use vstd::prelude::*;
use vstd::std_specs::btree::btree_map_inv;

verus! {

pub(crate) open spec fn read_lease_end<E, H>(
    enrolled: Option<E>, principal: Option<E>, owner: E,
    stored: Option<H>, requested: H, interval: ReadInterval,
    checkpoint: CheckpointAccess, now: u64, duration: u64,
) -> Option<u64> {
    if enrolled == Some(owner) && principal == Some(owner)
        && stored == Some(requested)
        && (interval.empty || (interval.floor <= interval.from <= interval.through
            && interval.through as int - interval.floor <= interval.retained))
        && checkpoint.erasure_floor <= checkpoint.cut && checkpoint.retained && !checkpoint.closed
        && now as int + duration <= u64::MAX {
        Some((now as int + duration) as u64)
    } else {
        None
    }
}

fn read_lease_requires_exact_protected_basis<W: Ord + Copy, E: Ord + Copy, H: Eq + Copy>(
    roster: &BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>, principal: Option<E>,
    basis: ReadBasis<W, E, H>, now: u64, duration: u64,
)
    requires obeys_concrete_eq::<E>(), obeys_concrete_eq::<H>(),
        obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
{
    let ghost worker = basis.worker;
    let ghost owner = basis.owner;
    let ghost stored = basis.stored;
    let ghost requested = basis.requested;
    let ghost interval = basis.interval;
    let ghost checkpoint = basis.checkpoint;
    let result = issue_read(roster, leases, principal, basis, now, duration);
    assert(result.ok() == read_lease_end(roster@.get(worker), principal, owner,
        stored, requested, interval, checkpoint, now, duration));
}

fn read_lease_retains_greatest_end<W: Ord + Copy, E: Ord + Copy, H: Eq + Copy>(
    roster: &BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>, principal: Option<E>,
    basis: ReadBasis<W, E, H>, now: u64, duration: u64,
)
    requires obeys_concrete_eq::<E>(), obeys_concrete_eq::<H>(),
        obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(),
        btree_map_inv(roster), btree_map_inv(old(leases)),
{
    let ghost prior = leases@;
    let ghost owner = basis.owner;
    let result = issue_read(roster, leases, principal, basis, now, duration);
    assert(match result {
        Ok(end) => (leases@.get(owner) matches Some(retained) && retained >= end
            && (prior.get(owner) matches Some(previous) ==> retained >= previous))
            && forall|other: E| other != owner ==> #[trigger] leases@.get(other) == prior.get(other),
        Err(_) => leases@ == prior,
    });
}


// The read gate cannot borrow authority from a vacant writer slot.
fn vacancy_never_substitutes_for_enrollment() {
    let mut roster = BTreeMap::<u64, u64>::new();
    let mut leases = BTreeMap::<u64, u64>::new();
    roster.insert(1, 2);
    let result = issue_read(&roster, &mut leases, Some(3), ReadBasis {
        worker: 1u64, owner: 3u64, stored: Some(8u64), requested: 8,
        interval: ReadInterval { empty: true, floor: 1, from: 0, through: 0, retained: 0 },
        checkpoint: CheckpointAccess { cut: 0, erasure_floor: 0, retained: true, closed: false },
    }, 10, 8);
    assert(result is Err && leases@.is_empty());
}

fn writer_lease_does_not_regress_or_change_other_ends<W: Ord, E: Ord + Copy>(
    roster: &BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>, worker: &W, owner: E,
    principal: Option<E>, current: Option<(E, u64, u64)>, epoch: u64, generation: u64,
    now: u64, duration: u64,
)
    requires obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster), btree_map_inv(old(leases)),
{
    let ghost previous = leases@;
    let result = lease::issue(roster, leases, worker, principal, current, (owner, epoch, generation), now, duration);
    assert(match result {
        Ok(end) => roster@.get(*worker) == Some(owner)
            && (leases@.get(owner) matches Some(retained) && end <= retained
                && (previous.get(owner) matches Some(prior) ==> prior <= retained))
            && forall|other: E| other != owner ==> #[trigger] leases@.get(other) == previous.get(other),
        Err(_) => leases@ == previous,
    });
}

fn old_root_cannot_renew(checkpoint: CheckpointAccess) {
    let ghost older = checkpoint.cut < checkpoint.erasure_floor;
    let ghost closed = checkpoint.closed;
    let open = checkpoint.is_open();
    assert((older || closed) ==> !open);
}

fn release_read_keeps_end_if_backed<K: Ord + Copy, H: Copy, W: Ord, E: Ord + Copy, F: Fn(H) -> E>(
    holds: &mut BTreeMap<K, H>, roster: &BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>,
    key: K, worker: &W, owner: E, identify: F, Ghost(project): Ghost<spec_fn(H) -> E>,
)
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster), btree_map_inv(old(leases)),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == project(entry),
        old(holds)@.get(key) matches Some(entry) && project(entry) == owner,
{
    let ghost previous_holds = holds@;
    let ghost previous_ends = leases@;
    let () = #[verus_spec(with Ghost(project))]
        crate::production::release_hold(roster, holds, leases, &key, worker, owner, identify);
    assert(holds@ == previous_holds.remove(key));
    assert(leases@ == if roster@.get(*worker) == Some(owner)
        || held_by(previous_holds.remove(key), owner, project) {
        previous_ends
    } else { previous_ends.remove(owner) });
}

fn expiry_disposal_clears_owner<K: Ord + Copy, H: Copy, W: Ord, E: Ord + Copy, F: Fn(H) -> E>(
    holds: &mut BTreeMap<K, H>, roster: &BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>,
    worker: &W, owner: E, authorized: bool, serial: u64, last_serial: u64,
    now: u64, drift: u64, identify: F, Ghost(project): Ghost<spec_fn(H) -> E>,
)
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(roster), btree_map_inv(old(leases)),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == project(entry),
{
    let ghost previous_holds = holds@;
    let ghost previous_ends = leases@;
    let result = #[verus_spec(with Ghost(project))]
        crate::production::dispose_expired(roster, holds, leases, worker, owner,
            ExpiryDisposal { authorized, serial, last_serial, now, drift }, identify);
    assert(result.is_ok() == (authorized && 0 < serial <= last_serial
        && roster@.get(*worker) != Some(owner)
        && (previous_ends.get(owner) matches Some(end) ==> end as int + drift <= now)));
    if result.is_ok() {
        assert forall|key: K| #[trigger] holds@.get(key) ==
            if previous_holds.get(key) matches Some(entry) && project(entry) == owner {
                None
            } else { previous_holds.get(key) } by {}
        proof {
            assert(!held_by(holds@, owner, project)) by {
                broadcast use vstd::map::group_map_lemmas, vstd::set::group_set_lemmas;
                if held_by(holds@, owner, project) {
                    let entry = choose|entry: H| #[trigger] holds@.values().contains(entry)
                        && project(entry) == owner;
                    let key = choose|key: K| holds@.dom().contains(key) && holds@[key] == entry;
                    assert(holds@.dom().contains(key));
                    assert(holds@.get(key) == Some(entry));
                }
            }
        }
        assert(leases@ == previous_ends.remove(owner));
    } else {
        assert(holds@ == previous_holds && leases@ == previous_ends);
    }
}

fn withdrawal_preserves_pending_owners<K, H: Copy, W: Ord + Copy, E: Ord + Copy, F: Fn(H) -> E>(
    holds: &BTreeMap<K, H>, roster: &mut BTreeMap<W, E>, leases: &mut BTreeMap<E, u64>,
    worker: W, former: E, replacement: Option<E>, identify: F,
    Ghost(project): Ghost<spec_fn(H) -> E>,
)
    requires vstd::std_specs::btree::key_obeys_cmp_spec::<K>(),
        vstd::std_specs::btree::btree_map_wf(holds),
        obeys_concrete_eq::<E>(), obeys_cmp::<E>(), obeys_cmp_concrete_eq::<E>(),
        obeys_cmp::<W>(), obeys_cmp_concrete_eq::<W>(), btree_map_inv(old(roster)),
        btree_map_inv(old(leases)), old(roster)@.get(worker) == Some(former),
        replacement != Some(former),
        forall|entry: H| identify.requires((entry,)),
        forall|entry: H, result: E| identify.ensures((entry,), result) ==> result == project(entry),
{
    let ghost previous = leases@;
    let ghost prior_roster = roster@;
    update_roster(roster, &worker, replacement);
    let () = #[verus_spec(with Ghost(project))]
        crate::production::prune_end(roster, holds, leases, &worker, former, identify);
    assert(roster@.get(worker) == replacement
        && forall|other: W| other != worker ==> #[trigger] roster@.get(other) == prior_roster.get(other));
    assert(leases@ == if held_by(holds@, former, project) {
        previous
    } else { previous.remove(former) });
}

fn rotation_adds_recovery_without_dropping_existing_holds<K: Ord + Copy, H, G, C, P>(
    holds: &mut BTreeMap<K, H>, id: K, recovery: H,
    authority: &mut writer::Authority<G>, epoch: u64, generation: u64, grant: G,
    published: &mut C, preparing: &mut Option<P>, floor: &mut u64, root: C, cut: crate::Cut,
)
    requires obeys_cmp::<K>(), obeys_cmp_concrete_eq::<K>(), btree_map_inv(old(holds)),
        !old(holds)@.contains_key(id), *old(floor) <= cut.next_lsn,
{
    let ghost previous = holds@;
    writer::insert_hold(holds, id, recovery);
    authority.install(epoch, generation, grant);
    rotation::publish_selection(published, preparing, floor, root, cut, true);
    assert(holds@ == previous.insert(id, recovery)
        && forall|key: K| #[trigger] previous.contains_key(key) ==> holds@.get(key) == previous.get(key));
    assert(*floor == cut.next_lsn && *preparing == None && authority.grant == Some(grant));
}

fn pending_erasure_blocks_writer_changes(pending: bool) {
    let result = rotation::check_writer_open(pending);
    assert(result.is_ok() == !pending);
}

fn vacancy_preserves_epoch_and_generation<G>(authority: &mut writer::Authority<G>) {
    let prior_epoch = authority.epoch;
    let prior_generation = authority.key_generation;
    authority.vacate();
    assert(authority.grant == None && authority.epoch == prior_epoch
        && authority.key_generation == prior_generation);
}

fn settlement_must_match_erasure_floor(
    current: u64, presented: u64, disposition: bool, closed: bool,
) {
    let result = rotation::check_settlement_fence(current, presented, disposition, closed);
    assert(result.is_ok() == (current == presented && disposition && closed));
}

}
