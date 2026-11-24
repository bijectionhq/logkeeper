use crate::budget::{AppendClass, append_debit};
use crate::object_withdrawal::fence_map;
use crate::production::*;
use crate::writer::{Authority, Cut};
use crate::Refusal;
use crate::receipt::{Receipt, ReceiptBook, RetainedOutcome};
use crate::request::{admit_request, finish_request};
use crate::retention::commit_withdrawal;
use std::collections::{BTreeMap, VecDeque};
use vstd::laws_eq::obeys_concrete_eq;
use vstd::prelude::*;
use vstd::std_specs::btree::btree_map_inv;

verus! {

pub(super) fn a_paid_append_advances_history_and_charges_one_lane<R>(
    records: &mut VecDeque<R>, head: &mut Cut, record: R, cut: Cut,
    class: AppendClass, charge: u64, window: u64, capacity: u64, reserve: u64,
    spent: &mut u64, ordinary: &mut u64, maintenance: &mut u64, Ghost(archive): Ghost<Seq<R>>,
) -> (out: Result<(), Refusal>)
    requires
        old(head).next_lsn == abstract_history(archive, old(records)@).len(),
        cut.next_lsn as int == old(head).next_lsn as int + 1,
        fundedBudget(abs_budget(*old(spent), *old(ordinary), *old(maintenance)),
            window as nat, capacity as nat, reserve as nat),
    ensures
        out is Ok ==> *final(head) == cut
            && final(head).next_lsn == abstract_history(archive, final(records)@).len()
            && abstract_history(archive, final(records)@)
                =~= abstract_history(archive, old(records)@).push(record)
            && abs_budget(*final(spent), *final(ordinary), *final(maintenance))
                == appendBudget(abs_budget(*old(spent), *old(ordinary), *old(maintenance)), class, charge as nat),
        out is Err ==> *final(head) == *old(head) && final(records)@ == old(records)@
            && *final(spent) == *old(spent) && *final(ordinary) == *old(ordinary)
            && *final(maintenance) == *old(maintenance),
        fundedBudget(abs_budget(*final(spent), *final(ordinary), *final(maintenance)),
            window as nat, capacity as nat, reserve as nat),
{
    broadcast use vstd::seq::group_seq_axioms;
    let debit = append_debit(class, charge, *spent, window, *ordinary, capacity, *maintenance, reserve)
        .ok_or(Refusal::Capacity)?;
    finish_append(records, head, record, cut, class, debit, spent, ordinary, maintenance);
    proof {
        match class {
            AppendClass::Data => {},
            AppendClass::Maintenance => {},
        }
    }
    Ok(())
}

pub(super) fn a_funded_window_replaces_the_allocation_and_resets_spend<W>(
    current: &mut W, next: W, spent: &mut u64, prior_serial: u64, serial: u64,
    bytes: u64, ordinary: u64, capacity: u64, present: bool,
) -> (out: Result<(), Refusal>)
    ensures out is Ok ==> *final(current) == next && *final(spent) == 0
        && ordinary as int + bytes <= capacity,
        out is Err ==> *final(spent) == *old(spent) && *final(current) == *old(current),
{
    fund_window(current, next, spent, present, prior_serial, serial, bytes, ordinary, capacity)
}

pub(super) fn a_successful_vacancy_keeps_its_epoch_and_generation<G, E: Copy + Eq>(
    authority: &mut Authority<G>, principal: Option<E>, current: Option<(E, u64, u64)>,
    presented: (E, u64, u64), erasure_pending: bool,
) -> (out: Result<(), Refusal>)
    requires obeys_concrete_eq::<E>(),
    ensures out is Ok ==> final(authority).grant is None && !erasure_pending
        && principal == Some(presented.0) && current == Some(presented),
        out is Err ==> final(authority).grant == old(authority).grant,
        final(authority).epoch == old(authority).epoch,
        final(authority).key_generation == old(authority).key_generation,
{
    vacate(authority, principal, current, presented, erasure_pending)
}

pub(super) fn a_retained_read_conflicts_and_a_mutation_replays_its_original<R: Copy>(
    book: &BTreeMap<u64, RetainedOutcome<R>>, key: &u64, reading: bool, fingerprint: &[u8; 32],
    position: u64, expires_at: u64, successor: Option<u64>, horizon: u64,
) -> (out: Result<Option<R>, Refusal>)
    requires btree_map_inv(book), book@.contains_key(*key),
    ensures
        reading ==> out == Err(Refusal::Conflict),
        !reading && fingerprint@ == book@[*key].fingerprint@ ==> out == Ok(Some(book@[*key].receipt)),
{
    admit_request(book, key, reading, fingerprint, position, expires_at, successor, horizon)
}

pub(super) fn a_refused_read_does_not_change_the_retry_book_or_expiry<O: Copy>(
    book: &mut ReceiptBook<u64, u64, u64, Result<O, Refusal>>,
    expiry: &mut BTreeMap<(u64, (u64, u64)), ()>,
    fingerprint: [u8; 32], applied: Receipt<u64, u64, u64, Result<O, Refusal>>, expires_at: u64,
)
    requires btree_map_inv(old(book)), btree_map_inv(old(expiry)), applied.outcome is Err,
    ensures final(book)@ == old(book)@, final(expiry)@ == old(expiry)@,
{
    finish_request(book, expiry, true, fingerprint, applied, expires_at);
}

pub(super) fn a_funded_withdrawal_adds_exactly_its_fresh_fence<F>(
    fences: &mut BTreeMap<u64, F>, name: u64, fence: F, used: usize, charge: usize, capacity: usize,
) -> (out: Result<(), Refusal>)
    requires fence_map(old(fences)), !old(fences)@.contains_key(name), capacity < usize::MAX,
    ensures
        out is Ok ==> final(fences)@ == old(fences)@.insert(name, fence)
            && used as int + charge <= capacity,
        out is Err ==> final(fences)@ == old(fences)@,
{
    commit_withdrawal(fences, name, fence, used, charge, capacity)
}

}
