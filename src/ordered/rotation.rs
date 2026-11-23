//! Exact-cut checks and selected-state updates for checkpoint publication.

use super::admission::matches_fingerprint;
use super::{Cut, Refusal};

pub(super) fn check_rotation<G: Eq, C: Eq>(
    custodian: bool,
    current: Option<G>,
    grant: G,
    head: Cut,
    published: C,
    requested: C,
    requested_cut: Cut,
) -> Result<(), Refusal> {
    if !custodian {
        return Err(Refusal::Unauthorized);
    }
    if current != Some(grant) || !same_cut(head, requested_cut) || published == requested {
        return Err(Refusal::Stale);
    }
    Ok(())
}

pub(super) fn same_cut(left: Cut, right: Cut) -> bool {
    left.next_lsn == right.next_lsn && matches_fingerprint(&left.history, &right.history)
}

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
    let empty_manifest = [0u8; 32];
    if !same_cut(prepared_cut, cut)
        || !matches_fingerprint(&prepared_root, &root)
        || prepared_custody != custody
        || matches_fingerprint(&manifest, &empty_manifest)
        || !matches!(observed_cut, Some(observed) if same_cut(observed, cut))
    {
        return Err(Refusal::Conflict);
    }
    Ok(())
}

pub(super) fn successor_generation<G: Eq, C: Eq>(
    erasure: bool,
    source: G,
    grant: G,
    base: C,
    published: C,
    generation: u64,
) -> Result<u64, Refusal> {
    if !erasure || source != grant || base != published {
        return Err(Refusal::Stale);
    }
    generation.checked_add(1).ok_or(Refusal::Capacity)
}

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

pub(super) fn admits_history(erasure_floor: u64, from: u64) -> bool {
    from >= erasure_floor
}
