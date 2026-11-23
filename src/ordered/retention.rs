//! Selection and accounting for a removed replay prefix.

use super::{AppendClass, Refusal, writer};
use std::collections::{BTreeMap, VecDeque};

use super::admission::pins_suffix;

pub(super) struct TrimSelection {
    pub floor: u64,
    pub through: u64,
    pub checkpoint: u64,
    pub exact_cut: bool,
}

pub(super) fn trim<R, P: Fn(&R) -> (AppendClass, u64, u64)>(
    selection: TrimSelection,
    has_live_pin: impl Fn() -> bool,
    records: &mut VecDeque<R>,
    ordinary: &mut u64,
    maintenance: &mut u64,
    project: P,
) -> Result<(u64, u64), Refusal> {
    if !within_checkpoint(selection.through, selection.checkpoint) || !selection.exact_cut {
        return Err(Refusal::Invalid);
    }
    let count = trim_length(selection.floor, selection.through, has_live_pin())?;
    Ok(trim_records(records, count, ordinary, maintenance, project))
}

pub(super) fn within_checkpoint(through: u64, checkpoint: u64) -> bool {
    through <= checkpoint
}

pub(super) fn trim_length(floor: u64, through: u64, pinned: bool) -> Result<usize, Refusal> {
    if pinned {
        return Err(Refusal::Unavailable);
    }
    usize::try_from(through - floor).map_err(|_| Refusal::Invalid)
}

pub(super) fn trim_records<R, P: Fn(&R) -> (AppendClass, u64, u64)>(
    records: &mut VecDeque<R>,
    trim: usize,
    ordinary: &mut u64,
    maintenance: &mut u64,
    project: P,
) -> (u64, u64) {
    let (ordinary_bytes, maintenance_bytes) = writer::drain_prefix(
        records,
        trim,
        (0, 0),
        |(ordinary_bytes, maintenance_bytes), record| {
            let (class, start, end) = project(&record);
            let charge = end - start;
            match class {
                AppendClass::Data => (ordinary_bytes + charge, maintenance_bytes),
                AppendClass::Maintenance => (ordinary_bytes, maintenance_bytes + charge),
            }
        },
    );
    *ordinary -= ordinary_bytes;
    *maintenance -= maintenance_bytes;
    (ordinary_bytes, maintenance_bytes)
}

pub(super) fn has_live_pin<K, H>(
    holds: &BTreeMap<K, H>,
    through: u64,
    interval: impl Fn(&H) -> (u64, u64),
) -> bool {
    let mut entries = holds.values();
    loop {
        let Some(hold) = entries.next() else {
            return false;
        };
        let (start, end) = interval(hold);
        if pins_suffix(start, end, through) {
            return true;
        }
    }
}
