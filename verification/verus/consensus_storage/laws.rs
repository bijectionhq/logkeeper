use crate::production::*;
use vstd::prelude::*;

verus! {

fn dropping_a_shared_slice_reverses_its_charge(usage: LiveBytes, len: u64)
    requires usage.bytes as int + len as int <= u64::MAX, usage.slices < usize::MAX,
{
    let charged = usage.add(len);
    let remaining = charged.remove(len);
    assert(remaining.bytes == usage.bytes && remaining.slices == usage.slices);
}

fn relocation_conserves_live_bytes(from: LiveBytes, to: LiveBytes, len: u64)
    requires
        from.bytes >= len, from.slices > 0,
        to.bytes as int + len as int <= u64::MAX, to.slices < usize::MAX,
{
    let left = from.remove(len);
    let right = to.add(len);
    assert(left.bytes as int + right.bytes as int == from.bytes as int + to.bytes as int);
    assert(left.slices as int + right.slices as int == from.slices as int + to.slices as int);
}

fn compaction_needs_a_cold_unpinned_segment_below_half(
    id: u64, floor: u64, keep: u64, usage: LiveBytes, size: u64, strong: usize, protected: bool,
)
    requires usage.slices < usize::MAX, size as int * 50 <= u64::MAX,
        usage.bytes as int * 100 <= u64::MAX,
{
    let cut = cold_before(floor, keep);
    if id < cut && compactable(usage, size, 50, strong, protected) {
        assert((id as int + keep as int) < floor as int);
        assert(usage.bytes as int * 2 < size);
        assert(usage.slices > 0 && strong <= usage.slices + 1 && !protected);
    }
}

fn unattributed_damage_never_preserves_some_streams(has_catalog: bool) {
    let scope = salvage_scope(true, has_catalog);
    assert(if has_catalog { scope is Refuse } else { scope is AllStreams });
}

fn attributed_damage_uses_the_known_owners(has_catalog: bool) {
    let scope = salvage_scope(false, has_catalog);
    assert(scope is Attributed);
}

fn restoring_a_leaf_accepts_its_exact_owned_suffix(index: u64, next: u64, owner: u128, scope: u128) {
    let accepted = checkpoint_entry(index, next, owner, scope);
    assert(accepted <==> index == next && owner == scope);
}

fn checkpoint_commit_rows_attach_only_to_existing_logs<L, C: Copy>(log: L, saved: C) {
    let absent = checkpoint_commit::<L, C>(None, saved);
    assert(absent is None);
    let attached = checkpoint_commit(Some(log), saved);
    assert(attached matches Some((actual_log, actual_id)) && actual_log == log && actual_id == saved);
}

fn a_replayed_commit_can_only_advance_a_restored_index(restored: u64, replayed: u64, since: u64) {
    let retained = if advance_commit(Some(restored), replayed) { replayed } else { restored };
    assert(retained >= restored && retained >= replayed);
    assert(retained == restored || retained == replayed);
    let truncate = loses_commit(Some(retained), since, false);
    let exact_overwrite = loses_commit(Some(retained), since, true);
    assert(truncate == (retained >= since) && !exact_overwrite);
}

fn a_changed_chain_cannot_open(replayed: [u8; 32], boundary: [u8; 32], at: usize)
    requires at < 32, replayed@[at as int] != boundary@[at as int],
{
    let trusted = matches_boundary(replayed, boundary);
    assert(!trusted);
}

}
