//! Writer authorization and frontier decisions used by the ordered reducer.

use std::collections::VecDeque;

#[cfg(verus_keep_ghost)]
use vstd::laws_eq::obeys_concrete_eq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

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

/// An exclusive data frontier and the identity of the prefix before it.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, PartialEq, Eq))]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Cut {
    pub next_lsn: u64,
    pub history: [u8; 32],
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<E>(),
    ensures out == if principal != Some(presented.0) { Err(Refusal::Unauthorized) }
        else if current != Some(presented) { Err(Refusal::Stale) } else { Ok(()) },
))]
pub(super) fn authorize<E: Eq + Copy>(
    principal: Option<E>,
    current: Option<(E, u64, u64)>,
    presented: (E, u64, u64),
) -> Result<(), Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<E>>());
        reveal(obeys_concrete_eq);
    }
    if principal != Some(presented.0) {
        return Err(Refusal::Unauthorized);
    }
    let Some((holder, epoch, key_generation)) = current else {
        return Err(Refusal::Stale);
    };
    let (candidate, candidate_epoch, candidate_generation) = presented;
    if holder != candidate || epoch != candidate_epoch || key_generation != candidate_generation {
        return Err(Refusal::Stale);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if epoch < u64::MAX { Ok((epoch as int + 1) as u64) }
        else { Err(Refusal::Capacity) },
))]
pub(super) fn next_epoch(epoch: u64) -> Result<u64, Refusal> {
    epoch.checked_add(1).ok_or(Refusal::Capacity)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if head != expected_next { Err(Refusal::Stale) }
        else if expected_next < u64::MAX { Ok((expected_next as int + 1) as u64) }
        else { Err(Refusal::Capacity) },
))]
pub(super) fn append_next(head: u64, expected_next: u64) -> Result<u64, Refusal> {
    if head != expected_next {
        return Err(Refusal::Stale);
    }
    expected_next.checked_add(1).ok_or(Refusal::Capacity)
}

#[derive(Clone)]
pub(super) struct Authority<G> {
    pub(super) epoch: u64,
    pub(super) key_generation: u64,
    pub(super) grant: Option<G>,
}

impl<G> Authority<G> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).epoch == epoch, final(self).key_generation == key_generation,
            final(self).grant == Some(grant),
    ))]
    pub(super) fn install(&mut self, epoch: u64, key_generation: u64, grant: G) {
        self.epoch = epoch;
        self.key_generation = key_generation;
        self.grant = Some(grant);
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).grant == if holder_matches { None } else { old(self).grant },
            final(self).epoch == old(self).epoch,
            final(self).key_generation == old(self).key_generation,
    ))]
    pub(super) fn withdraw(&mut self, holder_matches: bool) {
        if holder_matches {
            self.vacate();
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).grant == None,
            final(self).epoch == old(self).epoch,
            final(self).key_generation == old(self).key_generation,
    ))]
    pub(super) fn vacate(&mut self) {
        self.grant = None;
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(records)@ == old(records)@.push(record), *final(head) == cut,
))]
pub(super) fn commit_append<R>(records: &mut VecDeque<R>, head: &mut Cut, record: R, cut: Cut) {
    records.push_back(record);
    *head = cut;
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires count <= old(records)@.len(),
        forall|value: A, record: R| accumulate.requires((value, record)),
    ensures final(records)@ == old(records)@.skip(count as int),
))]
pub(super) fn drain_prefix<R, A, F: Fn(A, R) -> A>(
    records: &mut VecDeque<R>,
    count: usize,
    mut accumulated: A,
    accumulate: F,
) -> A {
    assert!(count <= records.len());
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = records@; }
    let mut removed = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant removed <= count <= original.len(),
            records@ == original.skip(removed as int),
            forall|value: A, record: R| accumulate.requires((value, record)),
        decreases count - removed,
    ))]
    while removed < count {
        let record = records
            .pop_front()
            .expect("trim prefix checked against record count");
        accumulated = accumulate(accumulated, record);
        removed += 1;
        #[cfg(verus_keep_ghost)]
        proof! { assert(records@ =~= original.skip(removed as int)); }
    }
    accumulated
}
