use crate::admission::pins_suffix;
use crate::production::{
    has_live_pin, matches_interval, pinsSuffix, projected_pin, trim_length, trim_records,
    trimCredit, well_formed_debits, within_checkpoint,
};
use crate::{AppendClass, Refusal};
use std::collections::{BTreeMap, VecDeque};
use vstd::prelude::*;
use vstd::std_specs::btree::{btree_map_wf, key_obeys_cmp_spec};

verus! {

pub open spec fn trimPrefixSafe(
    floor: int, through: int, checkpoint: int, start: int, finish: int,
) -> bool {
    forall|lsn: int| #[trigger] between(floor, lsn, through)
        ==> lsn < checkpoint && !between(start, lsn, finish)
}

pub open spec fn between(start: int, lsn: int, finish: int) -> bool {
    start <= lsn < finish
}

// LAW TRIM-KEEPS-CHECKPOINT-AND-LIVE-REPLAY.
pub fn trim_preserves_replay(
    floor: u64, through: u64, checkpoint: u64, start: u64, finish: u64,
)
    requires floor <= through,
{
    if within_checkpoint(through, checkpoint) {
        let pinned = pins_suffix(start, finish, through);
        assert(pinned == pinsSuffix(start, finish, through));
        if let Ok(count) = trim_length(floor, through, pinned) {
            assert(count as int == through as int - floor as int);
            assert(trimPrefixSafe(floor as int, through as int, checkpoint as int,
                start as int, finish as int));
        }
    }
}

// LAW EVERY-LIVE-HOLD-CAN-BLOCK-TRIM.
pub fn trim_refuses_a_live_pin<K, H>(
    holds: &BTreeMap<K, H>, held: Ghost<H>, floor: u64, through: u64,
    interval: impl Fn(&H) -> (u64, u64), intervals: Ghost<Map<H, (u64, u64)>>,
)
    requires
        floor <= through,
        btree_map_wf(holds),
        key_obeys_cmp_spec::<K>(),
        matches_interval(interval, intervals@),
        holds@.values().contains(held@),
        projected_pin(held@, intervals@, through),
{
    let pinned = has_live_pin(holds, through, interval, intervals);
    let decision = trim_length(floor, through, pinned);
    assert(decision == Err(Refusal::Unavailable));
}

// LAW TRIM-CREDITS-EXACTLY-THE-REMOVED-PREFIX.
pub fn trim_credit_matches_removed_records<R, P: Fn(&R) -> (AppendClass, u64, u64)>(
    records: &mut VecDeque<R>, count: usize, ordinary: &mut u64, maintenance: &mut u64,
    project: P, debit: Ghost<Map<R, (AppendClass, u64, u64)>>,
)
    requires
        count <= old(records)@.len(),
        well_formed_debits(project, debit@, old(records)@),
        *old(ordinary) as nat == trimCredit(old(records)@, old(records)@.len(), debit@).0,
        *old(maintenance) as nat == trimCredit(old(records)@, old(records)@.len(), debit@).1,
{
    let ghost before = records@;
    let ordinary_before = *ordinary;
    let maintenance_before = *maintenance;
    let (ordinary_credit, maintenance_credit) = trim_records(records, count, ordinary, maintenance, project, debit);
    assert(records@ == before.skip(count as int));
    assert((ordinary_credit as nat, maintenance_credit as nat) == trimCredit(before, count as nat, debit@));
    assert(*ordinary as int + ordinary_credit as int == ordinary_before as int);
    assert(*maintenance as int + maintenance_credit as int == maintenance_before as int);
}

}
