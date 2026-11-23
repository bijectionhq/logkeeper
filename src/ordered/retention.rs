//! Selection and accounting for a removed replay prefix.

use super::{AppendClass, Refusal};
use std::collections::{BTreeMap, VecDeque};

use super::admission::pins_suffix;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::{
    btree::{btree_map_wf, key_obeys_cmp_spec},
    iter::IteratorSpec,
};

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn recordCredit(debit: (AppendClass, u64, u64)) -> (nat, nat) {
        let charge = (debit.2 as int - debit.1 as int) as nat;
        match debit.0 {
            AppendClass::Data => (charge, 0),
            AppendClass::Maintenance => (0, charge),
        }
    }

    pub open spec fn trimCredit<R>(
        records: Seq<R>, count: nat, debit: Map<R, (AppendClass, u64, u64)>,
    ) -> (nat, nat)
        decreases count,
    {
        if count == 0 || records.len() == 0 {
            (0, 0)
        } else {
            let first = recordCredit(debit[records[0]]);
            let tail = trimCredit(records.drop_first(), (count - 1) as nat, debit);
            (first.0 + tail.0, first.1 + tail.1)
        }
    }

    pub open spec fn pinsSuffix(start: u64, end: u64, through: u64) -> bool {
        start < end && start < through
    }

    pub open spec fn live_suffix_pins(holds: Seq<(u64, u64)>, through: u64) -> bool {
        exists|i: int| 0 <= i < holds.len()
            && pinsSuffix((#[trigger] holds[i]).0, holds[i].1, through)
    }

    pub open spec fn in_replay(start: int, lsn: int, end: int) -> bool {
        start <= lsn < end
    }

    pub open spec fn projected_pin<H>(hold: H, intervals: Map<H, (u64, u64)>, through: u64) -> bool {
        pinsSuffix(intervals[hold].0, intervals[hold].1, through)
    }

    pub open spec fn matches_interval<H, P: Fn(&H) -> (u64, u64)>(
        interval: P, intervals: Map<H, (u64, u64)>,
    ) -> bool {
        &&& forall|hold: &H| #[trigger] call_requires(interval, (hold,))
        &&& forall|hold: &H, actual: (u64, u64)|
            #[trigger] call_ensures(interval, (hold,), actual) ==> actual == intervals[*hold]
    }

    pub(super) open spec fn trimPrefixSafe(selection: TrimSelection, holds: Seq<(u64, u64)>) -> bool {
        forall|lsn: int| #[trigger] in_replay(selection.floor as int, lsn, selection.through as int)
            ==> lsn < selection.checkpoint && (forall|i: int| 0 <= i < holds.len()
                ==> !in_replay((#[trigger] holds[i]).0 as int, lsn, holds[i].1 as int))
    }

    pub open spec fn well_formed_debits<R, P: Fn(&R) -> (AppendClass, u64, u64)>(
        project: P, debit: Map<R, (AppendClass, u64, u64)>, remaining: Seq<R>,
    ) -> bool {
        &&& forall|r: R| #[trigger] remaining.contains(r) ==> debit.contains_key(r) && debit[r].1 <= debit[r].2
        &&& forall|r: &R| remaining.contains(*r) ==> #[trigger] call_requires(project, (r,))
        &&& forall|r: &R, d: (AppendClass, u64, u64)| #[trigger] call_ensures(project, (r,), d)
            ==> d == debit[*r]
    }
}

pub(super) struct TrimSelection {
    pub floor: u64,
    pub through: u64,
    pub checkpoint: u64,
    pub exact_cut: bool,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires
        selection.exact_cut ==> 0 <= selection.through as int - selection.floor as int
            <= old(records)@.len(),
        call_requires(has_live_pin, ()),
        forall|pinned: bool| #[trigger] call_ensures(has_live_pin, (), pinned)
            ==> pinned == live_suffix_pins(holds@, selection.through),
        well_formed_debits(project, debit@, old(records)@),
        *old(ordinary) as nat == trimCredit(old(records)@, old(records)@.len(), debit@).0,
        *old(maintenance) as nat == trimCredit(old(records)@, old(records)@.len(), debit@).1,
    ensures
        match out {
            Ok(credit) => {
                let count = selection.through as int - selection.floor as int;
                &&& selection.exact_cut
                &&& trimPrefixSafe(selection, holds@)
                &&& final(records)@ == old(records)@.skip(count)
                &&& (credit.0 as nat, credit.1 as nat) == trimCredit(old(records)@, count as nat, debit@)
                &&& *final(ordinary) as int + credit.0 as int == *old(ordinary) as int
                &&& *final(maintenance) as int + credit.1 as int == *old(maintenance) as int
                &&& (*final(ordinary) as nat, *final(maintenance) as nat)
                    == trimCredit(final(records)@, final(records)@.len(), debit@)
            },
            Err(_) => {
                &&& final(records)@ == old(records)@
                &&& *final(ordinary) == *old(ordinary)
                &&& *final(maintenance) == *old(maintenance)
            },
        },
))]
pub(super) fn trim<R, P: Fn(&R) -> (AppendClass, u64, u64)>(
    selection: TrimSelection,
    has_live_pin: impl Fn() -> bool,
    records: &mut VecDeque<R>,
    ordinary: &mut u64,
    maintenance: &mut u64,
    project: P,
    #[cfg(verus_keep_ghost)] holds: Ghost<Seq<(u64, u64)>>,
    #[cfg(verus_keep_ghost)] debit: Ghost<Map<R, (AppendClass, u64, u64)>>,
) -> Result<(u64, u64), Refusal> {
    if !within_checkpoint(selection.through, selection.checkpoint) || !selection.exact_cut {
        return Err(Refusal::Invalid);
    }
    let pinned = has_live_pin();
    let count = trim_length(selection.floor, selection.through, pinned)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(!live_suffix_pins(holds@, selection.through));
        assert forall|lsn: int|
            #[trigger] in_replay(selection.floor as int, lsn, selection.through as int) implies
                lsn < selection.checkpoint && (forall|i: int| 0 <= i < holds@.len()
                    ==> !in_replay((#[trigger] holds@[i]).0 as int, lsn, holds@[i].1 as int)) by {
            assert forall|i: int| 0 <= i < holds@.len() implies
                !in_replay((#[trigger] holds@[i]).0 as int, lsn, holds@[i].1 as int) by {
                if in_replay(holds@[i].0 as int, lsn, holds@[i].1 as int) {
                    assert(pinsSuffix(holds@[i].0, holds@[i].1, selection.through));
                    assert(live_suffix_pins(holds@, selection.through));
                }
            }
        }
    }
    Ok(trim_records(
        records,
        count,
        ordinary,
        maintenance,
        project,
        #[cfg(verus_keep_ghost)]
        debit,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (through <= checkpoint),
))]
pub(super) fn within_checkpoint(through: u64, checkpoint: u64) -> bool {
    through <= checkpoint
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires floor <= through,
    ensures
        pinned ==> out == Err(Refusal::Unavailable),
        !pinned && through as int - floor as int <= usize::MAX as int
            ==> out is Ok && out->Ok_0 as int == through as int - floor as int,
        !pinned && through as int - floor as int > usize::MAX as int ==> out is Err,
))]
pub(super) fn trim_length(floor: u64, through: u64, pinned: bool) -> Result<usize, Refusal> {
    if pinned {
        return Err(Refusal::Unavailable);
    }
    usize::try_from(through - floor).map_err(|_| Refusal::Invalid)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires
        trim <= old(records)@.len(),
        well_formed_debits(project, debit@, old(records)@),
        *old(ordinary) as nat == trimCredit(old(records)@, old(records)@.len(), debit@).0,
        *old(maintenance) as nat == trimCredit(old(records)@, old(records)@.len(), debit@).1,
    ensures
        final(records)@ == old(records)@.skip(trim as int),
        (out.0 as nat, out.1 as nat) == trimCredit(old(records)@, trim as nat, debit@),
        *final(ordinary) as int == *old(ordinary) as int - out.0 as int,
        *final(maintenance) as int == *old(maintenance) as int - out.1 as int,
        (*final(ordinary) as nat, *final(maintenance) as nat)
            == trimCredit(final(records)@, final(records)@.len(), debit@),
))]
pub(super) fn trim_records<R, P: Fn(&R) -> (AppendClass, u64, u64)>(
    records: &mut VecDeque<R>,
    trim: usize,
    ordinary: &mut u64,
    maintenance: &mut u64,
    project: P,
    #[cfg(verus_keep_ghost)] debit: Ghost<Map<R, (AppendClass, u64, u64)>>,
) -> (u64, u64) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = records@; }
    let mut ordinary_bytes = 0;
    let mut maintenance_bytes = 0;
    let mut removed = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            removed <= trim <= original.len(),
            records@ == original.skip(removed as int),
            well_formed_debits(project, debit@, original),
            *ordinary as nat == trimCredit(original, original.len(), debit@).0,
            *maintenance as nat == trimCredit(original, original.len(), debit@).1,
            *ordinary as nat == ordinary_bytes as nat + trimCredit(records@, records@.len(), debit@).0,
            *maintenance as nat == maintenance_bytes as nat + trimCredit(records@, records@.len(), debit@).1,
            trimCredit(original, trim as nat, debit@).0 ==
                ordinary_bytes as nat + trimCredit(records@, (trim - removed) as nat, debit@).0,
            trimCredit(original, trim as nat, debit@).1 ==
                maintenance_bytes as nat + trimCredit(records@, (trim - removed) as nat, debit@).1,
        decreases trim - removed,
    ))]
    while removed < trim {
        let record = records.pop_front().expect("trim ends at a retained cut");
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(original.contains(record));
            assert(records@ =~= original.skip((removed + 1) as int));
            reveal_with_fuel(trimCredit, 2);
        }
        let (class, start, end) = project(&record);
        let charge = end - start;
        match class {
            AppendClass::Data => ordinary_bytes += charge,
            AppendClass::Maintenance => maintenance_bytes += charge,
        }
        removed += 1;
    }
    *ordinary -= ordinary_bytes;
    *maintenance -= maintenance_bytes;
    (ordinary_bytes, maintenance_bytes)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires btree_map_wf(holds), key_obeys_cmp_spec::<K>(), matches_interval(interval, intervals@),
    ensures out == (exists|hold: H| #[trigger] holds@.values().contains(hold)
        && projected_pin(hold, intervals@, through)),
))]
pub(super) fn has_live_pin<K, H>(
    holds: &BTreeMap<K, H>,
    through: u64,
    interval: impl Fn(&H) -> (u64, u64),
    #[cfg(verus_keep_ghost)] intervals: Ghost<Map<H, (u64, u64)>>,
) -> bool {
    let mut entries = holds.values();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = entries.remaining(); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            matches_interval(interval, intervals@),
            original.unref().to_set() == holds@.values(),
            entries.decrease() is Some,
            entries.remaining().len() <= original.len(),
            entries.remaining() == original.skip(original.len() - entries.remaining().len()),
            forall|i: int| 0 <= i < original.len() - entries.remaining().len()
                ==> !projected_pin(*(#[trigger] original[i]), intervals@, through),
        decreases entries.decrease().unwrap(),
    ))]
    loop {
        let Some(hold) = entries.next() else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(entries.remaining().len() == 0);
                assert forall|hold: H| #[trigger] holds@.values().contains(hold)
                    implies !projected_pin(hold, intervals@, through) by {
                    let i = choose|i: int| 0 <= i < original.len() && #[trigger] original.unref()[i] == hold;
                    assert(original.unref()[i] == *original[i]);
                    assert(!projected_pin(*original[i], intervals@, through));
                }
            }
            return false;
        };
        let (start, end) = interval(hold);
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost index = original.len() - entries.remaining().len() - 1; }
        #[cfg(verus_keep_ghost)]
        proof! { assert(original[index] == hold); }
        if pins_suffix(start, end, through) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(original.unref()[index] == *hold);
                assert(original.unref().contains(*hold));
                assert(projected_pin(*hold, intervals@, through));
                assert(holds@.values().contains(*hold));
            }
            return true;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(!projected_pin(*hold, intervals@, through)); }
    }
}
