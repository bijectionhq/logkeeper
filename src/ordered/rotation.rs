//! Exact-cut checks and selected-state updates for checkpoint publication.

use super::admission::matches_fingerprint;
use super::{checkpoint_guards::matches_preparation, Cut, Refusal};

#[cfg(verus_keep_ghost)]
use vstd::laws_eq::obeys_concrete_eq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
pub open spec fn matches_cut(left: Cut, right: Cut) -> bool {
    left.next_lsn == right.next_lsn && left.history@ == right.history@
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<G>(), obeys_concrete_eq::<C>(),
    ensures out == if !custodian { Err(Refusal::Unauthorized) }
        else if current != Some(grant) || !matches_cut(head, requested_cut) || published == requested {
            Err(Refusal::Stale)
        } else { Ok(()) },
))]

pub(super) fn check_rotation<G: Eq, C: Eq>(
    custodian: bool,
    current: Option<G>,
    grant: G,
    head: Cut,
    published: C,
    requested: C,
    requested_cut: Cut,
) -> Result<(), Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! {
        broadcast use vstd::laws_eq::lemma_option_obeys_concrete_eq;
        assert(obeys_concrete_eq::<Option<G>>());
        reveal(obeys_concrete_eq);
    }
    if !custodian {
        return Err(Refusal::Unauthorized);
    }
    if current != Some(grant) || !same_cut(head, requested_cut) || published == requested {
        return Err(Refusal::Stale);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == matches_cut(left, right)))]
pub(super) fn same_cut(left: Cut, right: Cut) -> bool {
    left.next_lsn == right.next_lsn && matches_fingerprint(&left.history, &right.history)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<C>(),
    ensures out == if !matches_cut(prepared_cut, cut)
        || prepared_root@ != root@ || prepared_custody != custody
        || manifest@ == Seq::new(32, |_: int| 0u8)
        || !(observed_cut matches Some(observed) && matches_cut(observed, cut))
        { Err(Refusal::Conflict) } else { Ok(()) },
))]
pub(super) fn check_preparation<C: Eq>(
    prepared_cut: Cut,
    prepared_root: [u8; 32],
    prepared_custody: C,
    cut: Cut,
    root: [u8; 32],
    custody: C,
    manifest: [u8; 32],
    observed_cut: Option<Cut>,
) -> Result<(), Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(obeys_concrete_eq); }
    let empty_manifest = [0u8; 32];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(empty_manifest@ =~= Seq::new(32, |_: int| 0u8));
    }
    if !same_cut(prepared_cut, cut)
        || !matches_fingerprint(&prepared_root, &root)
        || !matches_preparation(prepared_custody, custody)
        || matches_fingerprint(&manifest, &empty_manifest)
        || !matches!(observed_cut, Some(observed) if same_cut(observed, cut))
    {
        return Err(Refusal::Conflict);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires obeys_concrete_eq::<G>(), obeys_concrete_eq::<C>(),
    ensures out == if !erasure || source != grant || base != published { Err(Refusal::Stale) }
        else if generation == u64::MAX { Err(Refusal::Capacity) }
        else { Ok((generation as int + 1) as u64) },
))]
pub(super) fn successor_generation<G: Eq, C: Eq>(
    erasure: bool,
    source: G,
    grant: G,
    base: C,
    published: C,
    generation: u64,
) -> Result<u64, Refusal> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(obeys_concrete_eq); }
    if !erasure || source != grant || base != published {
        return Err(Refusal::Stale);
    }
    generation.checked_add(1).ok_or(Refusal::Capacity)
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(published) == checkpoint, *final(preparing) == None,
        *final(erasure_floor) == if closes_history { checkpoint_cut.next_lsn } else { *old(erasure_floor) },
))]
pub(super) fn publish_selection<C, P>(
    published: &mut C,
    preparing: &mut Option<P>,
    erasure_floor: &mut u64,
    checkpoint: C,
    checkpoint_cut: Cut,
    closes_history: bool,
) {
    if closes_history {
        *erasure_floor = checkpoint_cut.next_lsn;
    }
    *preparing = None;
    *published = checkpoint;
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (from >= erasure_floor)))]
pub(super) fn admits_history(erasure_floor: u64, from: u64) -> bool {
    from >= erasure_floor
}

pub(super) fn check_writer_open(erasure_pending: bool) -> Result<(), Refusal> {
    if erasure_pending {
        Err(Refusal::Unavailable)
    } else {
        Ok(())
    }
}

pub(super) fn check_settlement_fence(
    current_floor: u64,
    requested_floor: u64,
    disposition_present: bool,
    exact_closed_root: bool,
) -> Result<(), Refusal> {
    if requested_floor != current_floor || !disposition_present || !exact_closed_root {
        Err(Refusal::Stale)
    } else {
        Ok(())
    }
}
