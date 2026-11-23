//! Verus entry point for the admission decisions called by Logkeeper.
#![feature(proc_macro_hygiene)]

use vstd::prelude::*;

#[path = "../../../src/ordered/admission.rs"]
mod admission;

#[verus_spec(out =>
    requires used as int + completion_charge as int <= reserve as int,
    ensures out.0 is None,
        match out.1 {
            Some(end) => end as int == used as int + completion_charge as int,
            None => false,
        },
)]
fn maintenance_at_data_ceiling(
    data_ceiling: u64, user_charge: u64, used: u64, completion_charge: u64, reserve: u64,
) -> (Option<u64>, Option<u64>) {
    // Exercise a refused ordinary charge and the isolated maintenance debit
    // on the exact production functions.
    let ordinary = admission::debit(data_ceiling, if user_charge == 0 { 1 } else { user_charge }, data_ceiling);
    let maintenance = admission::debit(used, completion_charge, reserve);
    (ordinary, maintenance)
}

#[verus_spec(out =>
    ensures out.0 == (lower < upper && lower < trimmed_through),
        out.1 == ((now < expires_at || live_hold) && stored@ == offered@),
)]
fn compact_observations(
    lower: u64,
    upper: u64,
    trimmed_through: u64,
    now: u64,
    expires_at: u64,
    live_hold: bool,
    stored: &[u8],
    offered: &[u8],
) -> (bool, bool) {
    let pins = admission::pins_suffix(lower, upper, trimmed_through);
    let exact = admission::retains_receipt(now, expires_at, live_hold)
        && admission::matches_fingerprint(stored, offered);
    (pins, exact)
}

fn main() {}
