# Consensus storage rules

`proof.rs` imports the shipped `src/stream/consensus/storage/rules.rs`. The segmented WAL calls these functions on its real paths. `storage/objects.rs` keeps each segment's live bytes and slice count with `LiveBytes::add` and `LiveBytes::remove`, and chooses compaction candidates with `cold_before` and `compactable`. `storage/wal/segmented.rs` checks each checkpoint leaf entry with `checkpoint_entry`, restores the checkpoint's commit indexes with `checkpoint_commit`, compares the replayed chain with the trusted boundary with `matches_boundary` on both the open and the salvage paths, and decides what a salvage quarantines with `salvage_scope`. `storage/wal.rs` replays commit records with `advance_commit` and drops a commit index that a truncation or a rewrite removed with `loses_commit`. The harness uses no custom axioms, assumptions or external bodies.

| Law | Property | Shipped functions |
| --- | --- | --- |
| `dropping_a_shared_slice_reverses_its_charge` | Removing a slice undoes exactly what adding it charged | `LiveBytes::add`, `LiveBytes::remove` |
| `relocation_conserves_live_bytes` | Moving a slice between segments keeps the total live bytes and slices | `LiveBytes::add`, `LiveBytes::remove` |
| `compaction_needs_a_cold_unpinned_segment_below_half` | A compacted segment lies before the published checkpoint less the kept segments, is under half live (`share` 50), holds a live slice, is pinned by nothing but the scan and its slices, and no protected scope holds it | `cold_before`, `compactable` |
| `unattributed_damage_never_preserves_some_streams` | Damage that names no stream quarantines every stream, and on a keeper holding catalog records refuses the salvage | `salvage_scope` |
| `attributed_damage_uses_the_known_owners` | Damage every frame of which decoded quarantines only the streams it names | `salvage_scope` |
| `restoring_a_leaf_accepts_its_exact_owned_suffix` | A checkpoint leaf entry is restored only at the next index and only from its own scope | `checkpoint_entry` |
| `checkpoint_commit_rows_attach_only_to_existing_logs` | A saved commit index is restored unchanged onto its log, and onto no other | `checkpoint_commit` |
| `a_replayed_commit_can_only_advance_a_restored_index` | Replay keeps the larger commit index, and a truncation at or below it, or a rewrite of the committed entry, drops it | `advance_commit`, `loses_commit` |
| `a_changed_chain_cannot_open` | One differing byte of the replayed chain refuses the boundary | `matches_boundary` |

## Scope

The proofs cover the decisions. Unverified Rust walks the segments, holds the slice and scope maps, counts `Arc` handles, and classifies each salvaged frame. A frame that decodes names its stream, and every other outcome (a missing or unreadable segment, a bad header, a checksum failure, a frame that does not decode, a torn or short segment) sets the keeper-wide `unattributed` flag. The WAL salvage tests cover that classification. Boundary-slot selection, the checkpoint-within-boundary check and the rollback check in replay are verified in the [consensus admission area](../consensus_admission/README.md) (`newest_slot`, `checkpoint_within`, `replay_step`).

## Controls

`area.json` declares 13 production mutations: count a slice without its handle, keep a dropped slice's bytes, compact the newest segments the scan keeps, compact a segment exactly half live, a pinned one or a protected one, quarantine only the known streams or salvage a catalog keeper after unattributable damage, accept a foreign leaf entry, drop a restored commit index, let a replayed commit at the same index replace it, keep a commit index a truncation removed, and ignore the chain's first byte. The baseline verifies 22 functions, and each control fails exactly its declared contracts or loop invariant.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus consensus_storage
```
