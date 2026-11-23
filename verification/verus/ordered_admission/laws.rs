use crate::production;
use vstd::prelude::*;

verus! {

// The spec functions use the names and domains of Logkeeper.OrderedAdmission.
spec fn debit(used: nat, charge: nat, ceiling: nat) -> Option<nat> {
    if used + charge <= ceiling { Some(used + charge) } else { None }
}

spec fn pinsSuffix(start: nat, end: nat, floor: nat) -> bool {
    start < end && start < floor
}

spec fn retainsReceipt(position: nat, expiresAt: nat, ownsLiveHold: bool) -> bool {
    position < expiresAt || ownsLiveHold
}

spec fn matchesFingerprint(stored: Seq<u8>, presented: Seq<u8>) -> bool {
    stored == presented
}

spec fn debit_value(out: Option<u64>) -> Option<nat> {
    match out {
        Some(end) => Some(end as nat),
        None => None,
    }
}

fn debit_matches_reference(used: u64, charge: u64, ceiling: u64) -> (out: Option<u64>)
    ensures debit_value(out) == debit(used as nat, charge as nat, ceiling as nat),
{
    production::debit(used, charge, ceiling)
}

fn maintenance_at_data_ceiling(
    data_ceiling: u64, user_charge: u64, used: u64, completion_charge: u64, reserve: u64,
) -> (out: (Option<u64>, Option<u64>))
    requires
        0 < user_charge,
        used as nat + completion_charge as nat <= reserve as nat,
    ensures
        out.0 is None,
        debit_value(out.1) == Some(used as nat + completion_charge as nat),
{
    (
        production::debit(data_ceiling, user_charge, data_ceiling),
        production::debit(used, completion_charge, reserve),
    )
}

fn pins_suffix_matches_reference(start: u64, end: u64, floor: u64) -> (out: bool)
    ensures out == pinsSuffix(start as nat, end as nat, floor as nat),
{
    production::pins_suffix(start, end, floor)
}

fn retains_receipt_matches_reference(position: u64, expires_at: u64, owns_live_hold: bool)
    -> (out: bool)
    ensures out == retainsReceipt(position as nat, expires_at as nat, owns_live_hold),
{
    production::retains_receipt(position, expires_at, owns_live_hold)
}

fn fingerprint_equality_matches_reference(stored: &[u8], presented: &[u8]) -> (out: bool)
    ensures out == matchesFingerprint(stored@, presented@),
{
    production::matches_fingerprint(stored, presented)
}

}
