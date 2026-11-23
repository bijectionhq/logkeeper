//! Byte charges and lane-specific append debits.

use super::admission::debit;

pub const MAX_OBJECT_REFERENCES: usize = 16_384;

/// Fixed stream charge for each record's identity and framing. Replica media
/// also budget for staging and their own metadata.
pub const APPEND_RECORD_CHARGE_BYTES: u64 = 217;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

pub(super) fn record_charge(payload_len: usize, reference_count: Option<usize>) -> Option<u64> {
    let overhead = match reference_count {
        Some(count) => 4 + 32 * count as u64,
        None => 0,
    };
    (payload_len as u64).checked_add(APPEND_RECORD_CHARGE_BYTES + overhead)
}

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
