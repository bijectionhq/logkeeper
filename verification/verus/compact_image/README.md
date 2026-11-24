# Compact image row admission

This area imports [the shipped guards](../../../src/ordered/codec/snapshot_checks.rs) called by the [LKBASE08 decoder](../../../src/ordered/codec/snapshot.rs).

| Lean definition in [Logkeeper.CompactImage](../../lean/Logkeeper/CompactImage.lean) | Verus obligation and projection |
| --- | --- |
| `generationInRange` | `generation_in_range` bounds the stored generation independently of whether a grant is present. |
| `holdReceiptMatches` | `hold_receipt_matches` requires a receipt at the exact admission position. The caller supplies a position only when the retained outcome at the hold's origin and request ID has the right kind and contains the exact hold. |
| `leaseRowValid` | `lease_row_valid` requires a bounded nonzero enrollment serial, a retained owner, lease-end bounds and a key greater than the previously retained key. The caller supplies membership and key comparison. |
| `fenceRowValid` | `fence_row_valid` requires a nonzero position within the image position, a time within the image time, and a key greater than the previously retained key. The caller supplies the key comparison. |
| `rootReferenceRowValid` | `root_reference_row_valid` requires a known root and a revision greater than the previous revision. The caller resolves the revision against the selected, preparing and retained roots. |

For machine-representable lease ends, the Rust comparison against a saturating sum is equivalent to comparison against the mathematical sum used by Lean.
The Lean law `every_checked_hold_has_a_matching_receipt` composes the row checks over an arbitrary finite list.
The Lean law `strictly_increasing_keys_are_unique` gives uniqueness when a list is strictly ascending.
The Rust collection traversals, membership and comparisons on composite keys, and the coverage and aggregate budget of object references still require production refinement.
The [ordered codec area](../ordered_codec/README.md) verifies the count and byte extent of the object names in each reference list.
The Lean vacancy model carries its generation independently of the holder. Native acceptance exercises rotation, vacancy, `LKBASE08` recovery and a replacement grant with that generation.

Two reachable snapshot fixtures exhibit accepted encodings that differ from the encoder output.
A snapshot without object controls also decodes with two appended zero counts.
Two distinct retained old-root rows can be reversed and decode to the same ordered map.
A duplicate old-root revision is rejected.
The native tests also reject a retained hold with a missing or wrong-kind admission receipt.

The [manifest](area.json) records six source mutations and their expected diagnostics.
The pinned baseline verified ten items and all six mutations failed at their declared obligations.

## Reducer collection invariant

`allSnapshotRowsValid` in [Logkeeper.CompactImage](../../lean/Logkeeper/CompactImage.lean) maps to the production `all_snapshot_rows` traversal. The verifier checks every value in the actual ordered map. The decoder calls it to check the hold-to-receipt join and the withdrawal-receipt-to-fence join. The Rust closures supply exact key and row equality, outcome-kind matching, and the positions. Verus checks the traversal and the separate hold-position guard. The new control bypasses one-row checks and fails `one_invalid_hold_prevents_recovery`.

`reducerInvariant` is the reusable specification on `ReducerImage`. Lean lists and Verus sequences use the same projections. Ordered maps contribute their key sequences in iteration order. Composite keys and names use order-preserving integer representations. Bounds come from the decoder configuration and admission limits. Leases contribute exact enrollment membership and end time. Root membership, reference coverage, object-control bytes, and withdrawal receipt equality come from the corresponding state queries. A hold contributes its exact matched receipt position, or no position when the join fails. The [writer area](../ordered_writer/README.md) separately checks that the shipped vacancy transition preserves the stored generation.

The decoder accepts multiple distinct receipt keys with the same decision position. A native test fills the retry book to its decode bound with those rows, applies one decision, and observes that the resulting encoding fails to decode. The reference invariant requires unique receipt positions, as an applied decision records at most one receipt. F4 calls for rejecting this image and the two accepted aliases above under the existing format tag. The decoder change is tracked in PL3c. Whole-image acceptance still needs a proof that the Rust parser and state construction implement the projections above.

The expanded baseline verifies 13 items. All seven source controls fail at their declared obligations.
