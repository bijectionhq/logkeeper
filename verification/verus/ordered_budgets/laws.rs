use crate::admission::debit;
use crate::production::{AppendClass, MAX_OBJECT_REFERENCES, append_debit, record_charge};
use vstd::prelude::*;

verus! {

pub open spec fn referenceCharge(references: Option<usize>) -> int {
    match references {
        None => 0,
        Some(count) => 4 + 32 * count as int,
    }
}

pub open spec fn recordCharge(payload: usize, references: Option<usize>) -> int {
    payload as int + (217 + referenceCharge(references))
}

pub open spec fn fundedBudget(
    spent: int, ordinary: int, maintenance: int, window: int, capacity: int, reserve: int,
) -> bool {
    &&& spent <= window
    &&& ordinary + (window - spent) <= capacity
    &&& maintenance <= reserve
}

// LAW ORDINARY-APPEND-KEEPS-FUNDING.
pub fn admitted_ordinary_append_preserves_funding(
    payload: usize, references: Option<usize>, spent: u64, window: u64,
    ordinary: u64, capacity: u64, maintenance: u64, reserve: u64,
)
    requires
        references is Some ==> references->Some_0 <= MAX_OBJECT_REFERENCES,
        fundedBudget(spent as int, ordinary as int, maintenance as int, window as int,
            capacity as int, reserve as int),
{
    if let Some(charge) = record_charge(payload, references) {
        if let Some(next) = append_debit(
            AppendClass::Data, charge, spent, window, ordinary, capacity, maintenance, reserve,
        ) {
            assert(next.end as int - next.start as int == recordCharge(payload, references));
            assert(next.end <= window);
            assert(fundedBudget(next.end as int, next.retained as int, maintenance as int,
                window as int, capacity as int, reserve as int));
        }
    }
}

// Logkeeper.OrderedBudgets.funded_window_implies_retained_room.
pub fn funded_window_implies_retained_room(
    spent: u64, ordinary: u64, maintenance: u64, window: u64,
    capacity: u64, reserve: u64, charge: u64,
)
    requires fundedBudget(spent as int, ordinary as int, maintenance as int, window as int,
        capacity as int, reserve as int),
        spent as int + charge as int <= window as int,
{
    assert(ordinary as int + charge as int <= capacity as int);
    let admitted = append_debit(
        AppendClass::Data, charge, spent, window, ordinary, capacity, maintenance, reserve,
    );
    assert(admitted is Some);
}

// LAW MAINTENANCE-APPEND-USES-ONLY-RESERVE.
pub fn maintenance_funding_is_independent(
    payload: usize, references: Option<usize>, window: u64,
    ordinary: u64, capacity: u64, maintenance: u64, reserve: u64,
)
    requires references is Some ==> references->Some_0 <= MAX_OBJECT_REFERENCES,
{
    if let Some(charge) = record_charge(payload, references) {
        assert(charge as int == recordCharge(payload, references));
        let attempted = append_debit(
            AppendClass::Maintenance, charge, window, window, ordinary, capacity, maintenance, reserve,
        );
        assert((attempted is Some) == (maintenance as int + recordCharge(payload, references) <= reserve as int));
        if let Some(next) = attempted {
            assert(next.start == 0);
            assert(next.end as int == recordCharge(payload, references));
            assert(next.retained as int == maintenance as int + recordCharge(payload, references));
            assert(next.retained <= reserve);
        }
    }
}

// LAW REF-LIST-CHARGE-AND-OVERFLOW.
pub fn record_charge_matches_reference(payload: usize, references: Option<usize>)
    requires references is Some ==> references->Some_0 <= MAX_OBJECT_REFERENCES,
{
    let charge = record_charge(payload, references);
    assert((charge is Some) == (recordCharge(payload, references) <= u64::MAX as int));
    if let Some(bytes) = charge {
        assert(bytes as int == recordCharge(payload, references));
    }
}

// LAW NEW-WINDOW-RESERVES-RETAINED-PLUS-UNSPENT.
pub fn funding_new_window(
    spent: u64, old_window: u64, new_window: u64, ordinary: u64,
    capacity: u64, maintenance: u64, reserve: u64,
)
    requires fundedBudget(spent as int, ordinary as int, maintenance as int, old_window as int,
        capacity as int, reserve as int),
{
    if let Some(_) = debit(ordinary, new_window, capacity) {
        assert(fundedBudget(0, ordinary as int, maintenance as int, new_window as int,
            capacity as int, reserve as int));
    }
}

}
