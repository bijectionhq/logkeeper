//! Ordered command updates that couple writer, history, and funding state.

use super::admission;
use super::budget::{AppendClass, AppendDebit};
use super::{Refusal, rotation};
use super::writer::{self, Authority, Cut};
use std::collections::VecDeque;

#[cfg(verus_keep_ghost)]
use vstd::laws_eq::obeys_concrete_eq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct Budget {
    pub spent: int,
    pub ordinary: int,
    pub maintenance: int,
}

pub open spec fn abs_budget(spent: u64, ordinary: u64, maintenance: u64) -> Budget {
    Budget { spent: spent as int, ordinary: ordinary as int, maintenance: maintenance as int }
}

pub open spec fn fundedBudget(budget: Budget, window: nat, capacity: nat, reserve: nat) -> bool {
    &&& 0 <= budget.spent <= window
    &&& 0 <= budget.ordinary
    &&& budget.ordinary + (window - budget.spent) <= capacity
    &&& 0 <= budget.maintenance <= reserve
}

pub open spec fn appendBudget(b: Budget, class: AppendClass, charge: nat) -> Budget {
    match class {
        AppendClass::Data => Budget { spent: b.spent + charge, ordinary: b.ordinary + charge, ..b },
        AppendClass::Maintenance => Budget { maintenance: b.maintenance + charge, ..b },
    }
}

pub open spec fn admitsAppend(b: Budget, class: AppendClass, charge: nat,
    window: nat, capacity: nat, reserve: nat) -> bool {
    match class {
        AppendClass::Data => b.spent + charge <= window && b.ordinary + charge <= capacity,
        AppendClass::Maintenance => b.maintenance + charge <= reserve,
    }
}

pub open spec fn commitAppend<R>(retained: Seq<R>, record: R) -> Seq<R> {
    retained.push(record)
}

pub open spec fn abstract_history<R>(archive: Seq<R>, records: Seq<R>) -> Seq<R> {
    archive + records
}

pub open spec fn fundWindow(b: Budget, window: nat) -> (Budget, nat) {
    (Budget { spent: 0, ..b }, window)
}

pub open spec fn funding_refusal(allocation_present: bool, previous_serial: u64, serial: u64,
    bytes: u64, ordinary: u64, capacity: u64) -> Result<(), Refusal> {
    if !allocation_present || bytes == 0 || serial as int != previous_serial as int + 1 {
        Err(Refusal::Invalid)
    } else if ordinary as int + bytes > capacity { Err(Refusal::Capacity) }
    else { Ok(()) }
}

pub open spec fn vacate_refusal<E>(principal: Option<E>, current: Option<(E, u64, u64)>,
    presented: (E, u64, u64), erasure_pending: bool) -> Result<(), Refusal> {
    if principal != Some(presented.0) { Err(Refusal::Unauthorized) }
    else if current != Some(presented) { Err(Refusal::Stale) }
    else if erasure_pending { Err(Refusal::Unavailable) }
    else { Ok(()) }
}

pub open spec fn vacate_projection<G>(holder: Option<G>, epoch: u64, generation: u64,
    accepted: bool) -> (Option<G>, u64, u64) {
    (if accepted { None } else { holder }, epoch, generation)
}

}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures
        final(records)@ == commitAppend(old(records)@, record),
        *final(head) == cut,
        abs_budget(*final(spent), *final(ordinary), *final(maintenance)) == match class {
            AppendClass::Data => Budget {
                spent: debit.end as int, ordinary: debit.retained as int,
                maintenance: *old(maintenance) as int,
            },
            AppendClass::Maintenance => Budget {
                spent: *old(spent) as int, ordinary: *old(ordinary) as int,
                maintenance: debit.retained as int,
            },
        },
))]
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_append<R>(
    records: &mut VecDeque<R>,
    head: &mut Cut,
    record: R,
    cut: Cut,
    class: AppendClass,
    debit: AppendDebit,
    spent: &mut u64,
    ordinary: &mut u64,
    maintenance: &mut u64,
) {
    writer::commit_append(records, head, record, cut);
    match class {
        AppendClass::Data => {
            *spent = debit.end;
            *ordinary = debit.retained;
        }
        AppendClass::Maintenance => *maintenance = debit.retained,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out == funding_refusal(allocation_present, previous_serial, serial, bytes, ordinary, capacity),
        *final(window) == if out is Ok { next_window } else { *old(window) },
        *final(spent) == if out is Ok { fundWindow(abs_budget(*old(spent), ordinary, 0), bytes as nat).0.spent }
            else { *old(spent) as int },
        out is Ok ==> fundedBudget(abs_budget(*final(spent), ordinary, 0), bytes as nat, capacity as nat, 0),
))]
#[allow(clippy::too_many_arguments)]
pub(super) fn fund_window<W>(
    window: &mut W,
    next_window: W,
    spent: &mut u64,
    allocation_present: bool,
    previous_serial: u64,
    serial: u64,
    bytes: u64,
    ordinary: u64,
    capacity: u64,
) -> Result<(), Refusal> {
    if !allocation_present || bytes == 0 || Some(serial) != previous_serial.checked_add(1) {
        return Err(Refusal::Invalid);
    }
    admission::debit(ordinary, bytes, capacity).ok_or(Refusal::Capacity)?;
    *window = next_window;
    *spent = 0;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<E>(),
    ensures
        out == vacate_refusal(principal, current, presented, erasure_pending),
        (final(authority).grant, final(authority).epoch, final(authority).key_generation)
            == vacate_projection(old(authority).grant, old(authority).epoch, old(authority).key_generation, out is Ok),
))]
pub(super) fn vacate<G, E: Copy + Eq>(
    authority: &mut Authority<G>,
    principal: Option<E>,
    current: Option<(E, u64, u64)>,
    presented: (E, u64, u64),
    erasure_pending: bool,
) -> Result<(), Refusal> {
    writer::authorize(principal, current, presented)?;
    rotation::check_writer_open(erasure_pending)?;
    authority.vacate();
    Ok(())
}
