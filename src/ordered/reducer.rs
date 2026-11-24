//! Ordered command updates that couple writer, history, and funding state.

use super::admission;
use super::budget::{AppendClass, AppendDebit};
use super::{Refusal, rotation};
use super::writer::{self, Authority, Cut};
use std::collections::VecDeque;

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
