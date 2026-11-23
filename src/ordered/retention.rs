//! Selection and accounting for a removed replay prefix.

use super::{AppendClass, Refusal, writer};
use std::collections::VecDeque;

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
