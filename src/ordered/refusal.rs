#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
pub enum Refusal {
    WrongPlacement,
    Unauthorized,
    Stale,
    Conflict,
    Invalid,
    Expired,
    Capacity,
    Unavailable,
    CohortSealed,
}
