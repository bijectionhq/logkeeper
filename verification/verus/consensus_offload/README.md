# Consensus offload restore planning

`proof.rs` imports the shipped `src/stream/consensus/offload/rules.rs`. `Store::plan` in `offload/mod.rs` builds a restore plan from the object store with these functions: `restore_window` bounds each lineage by its successor and the requested floor, `restore_cursor` decides whether the previous lineage's run continues, `select_restore_object` picks the object that covers the cursor and reaches farthest, or the nearest object after a gap, and `restore_cut` cuts the chosen object at the lineage's window. The monotonic `offloaded_through` and the lineage check on reported progress (`offloaded_through`, `lineage_offload`) are verified in the [consensus admission area](../consensus_admission/README.md). The harness uses no custom axioms, assumptions or external bodies.

| Law | Property | Shipped functions |
| --- | --- | --- |
| `a_deposed_lineage_never_supplies_the_successors_records` | Records from a lineage end before its successor's first record, and above the floor | `restore_window`, `restore_cut` |
| `extending_a_run_never_crosses_a_gap` | A run continues into the next lineage only when it reaches that lineage's window, and then from the record after its end | `restore_cursor` |
| `a_gap_never_discards_an_available_cover` | When any object covers the cursor, the plan takes one, and it reaches at least as far as every other cover | `select_restore_object` |

The contracts of `select_restore_object` also state the gap case: with no cover, it resumes at the smallest first record after the cursor within the window, or ends when there is none.

## Scope

The loop in `Store::plan` that calls these functions, listing the objects and resetting the plan after a gap, is unverified Rust covered by the offload tests. That the uploaded objects of a lineage are committed records is the [Lean `OffloadPrefix`](../../lean/Logkeeper/ConsensusAdditions/OffloadPrefix.lean) property.

## Controls

`area.json` declares 5 production mutations: read the successor lineage's first record from the deposed one, extend a run across a one-record gap, cut an object past its lineage's window, miss an object starting exactly at the cursor, and resume after a gap at a later object than the nearest. The baseline verifies 8 functions, and each control fails exactly its declared contracts or loop invariant.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus consensus_offload
```
