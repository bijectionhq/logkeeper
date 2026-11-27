//! Pure arithmetic and recovery decisions shared by the segmented WAL paths.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy, Default)]
pub(super) struct LiveBytes {
    pub bytes: u64,
    pub slices: usize,
}

impl LiveBytes {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.bytes as int + len as int <= u64::MAX,
            self.slices < usize::MAX,
        ensures out.bytes as int == self.bytes as int + len as int,
            out.slices as int == self.slices as int + 1,
    ))]
    pub(super) fn add(self, len: u64) -> Self {
        Self {
            bytes: self.bytes + len,
            slices: self.slices + 1,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures
            out.bytes as int == if len <= self.bytes { self.bytes as int - len as int } else { 0 },
            out.slices as int == if self.slices > 0 { self.slices as int - 1 } else { 0 },
    ))]
    pub(super) fn remove(self, len: u64) -> Self {
        Self {
            bytes: self.bytes.saturating_sub(len),
            slices: self.slices.saturating_sub(1),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if keep <= floor { floor - keep } else { 0 },
))]
pub(super) fn cold_before(floor: u64, keep: u64) -> u64 {
    floor.saturating_sub(keep)
}

/// The caller only visits segments below `cold_before`. One strong handle
/// belongs to the scan and one to each live slice.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires usage.slices < usize::MAX,
    ensures out == (usage.slices > 0 && strong as int <= usage.slices as int + 1 && !protected
        && usage.bytes.saturating_mul(100) < size.saturating_mul(share)),
))]
pub(super) fn compactable(
    usage: LiveBytes,
    size: u64,
    share: u64,
    strong: usize,
    protected: bool,
) -> bool {
    usage.slices > 0
        && strong <= usage.slices + 1
        && !protected
        && usage.bytes.saturating_mul(100) < size.saturating_mul(share)
}

pub(super) enum SalvageScope {
    Attributed,
    AllStreams,
    Refuse,
}

/// An untrusted frame can conceal a catalog claim independently of which
/// registered streams happen to be present on this keeper.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        (out is Attributed) == !unattributed,
        (out is AllStreams) == (unattributed && !has_catalog),
        (out is Refuse) == (unattributed && has_catalog),
))]
pub(super) fn salvage_scope(unattributed: bool, has_catalog: bool) -> SalvageScope {
    match (unattributed, has_catalog) {
        (false, _) => SalvageScope::Attributed,
        (true, false) => SalvageScope::AllStreams,
        (true, true) => SalvageScope::Refuse,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (index == next && owner == scope),
))]
pub(super) fn checkpoint_entry(index: u64, next: u64, owner: u128, scope: u128) -> bool {
    index == next && owner == scope
}

/// Join a saved commit row with its matching restored log, if present.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match log { Some(log) => Some((log, saved)), None => None },
))]
pub(super) fn checkpoint_commit<L, C>(log: Option<L>, saved: C) -> Option<(L, C)> {
    match log {
        Some(log) => Some((log, saved)),
        None => None,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match current { Some(known) => known < replayed, None => true },
))]
pub(super) fn advance_commit(current: Option<u64>, replayed: u64) -> bool {
    match current {
        Some(known) => known < replayed,
        None => true,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (current matches Some(known) && known >= since && !still_present),
))]
pub(super) fn loses_commit(current: Option<u64>, since: u64, still_present: bool) -> bool {
    matches!(current, Some(known) if known >= since) && !still_present
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (replayed@ == boundary@),
))]
pub(super) fn matches_boundary(replayed: [u8; 32], boundary: [u8; 32]) -> bool {
    let mut at = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant at <= 32, forall|i: int| 0 <= i < at ==> replayed@[i] == boundary@[i],
        decreases 32 - at,
    ))]
    while at < 32 {
        if replayed[at] != boundary[at] {
            return false;
        }
        at += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(replayed@ =~= boundary@); }
    true
}
