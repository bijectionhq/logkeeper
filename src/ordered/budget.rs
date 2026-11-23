//! Byte charges and lane-specific append debits.

use super::admission::debit;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub const MAX_OBJECT_REFERENCES: usize = 16_384;

/// Fixed stream charge for each record's identity and framing. Replica media
/// also budget for staging and their own metadata.
pub const APPEND_RECORD_CHARGE_BYTES: u64 = 217;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
pub enum AppendClass {
    Data,
    Maintenance,
}

impl AppendClass {
    pub(super) fn tag(self) -> u8 {
        match self {
            Self::Data => 0,
            Self::Maintenance => 1,
        }
    }
}

pub(super) struct AppendDebit {
    pub start: u64,
    pub end: u64,
    pub retained: u64,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires match reference_count {
        Some(count) => count <= MAX_OBJECT_REFERENCES,
        None => true,
    },
    ensures
        (out is Some) == (payload_len as int + 217
            + (match reference_count { Some(count) => 4 + 32 * count as int, None => 0 })
            <= u64::MAX as int),
        match out {
            Some(charge) => charge as int == payload_len as int
                + 217
                + (match reference_count { Some(count) => 4 + 32 * count as int, None => 0 }),
            None => true,
        },
))]
pub(super) fn record_charge(payload_len: usize, reference_count: Option<usize>) -> Option<u64> {
    let overhead = match reference_count {
        Some(count) => 4 + 32 * count as u64,
        None => 0,
    };
    (payload_len as u64).checked_add(APPEND_RECORD_CHARGE_BYTES + overhead)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Some) == match class {
            AppendClass::Data => spent as int + charge as int <= window as int
                && ordinary as int + charge as int <= ordinary_capacity as int,
            AppendClass::Maintenance => maintenance as int + charge as int <= reserve as int,
        },
        match out {
            Some(debit) => match class {
                AppendClass::Data => debit.start == spent
                    && debit.end as int == spent as int + charge as int
                    && debit.retained as int == ordinary as int + charge as int,
                AppendClass::Maintenance => debit.start == 0 && debit.end == charge
                    && debit.retained as int == maintenance as int + charge as int,
            },
            None => true,
        },
))]
#[allow(clippy::too_many_arguments)]
pub(super) fn append_debit(
    class: AppendClass,
    charge: u64,
    spent: u64,
    window: u64,
    ordinary: u64,
    ordinary_capacity: u64,
    maintenance: u64,
    reserve: u64,
) -> Option<AppendDebit> {
    match class {
        AppendClass::Data => {
            let end = debit(spent, charge, window)?;
            let retained = debit(ordinary, charge, ordinary_capacity)?;
            Some(AppendDebit {
                start: spent,
                end,
                retained,
            })
        }
        AppendClass::Maintenance => {
            let retained = debit(maintenance, charge, reserve)?;
            Some(AppendDebit {
                start: 0,
                end: charge,
                retained,
            })
        }
    }
}
