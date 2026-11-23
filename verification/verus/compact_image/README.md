# Compact image row admission

This area imports [the shipped guards](../../../src/ordered/codec/snapshot_checks.rs) called by the [LKBASE07 decoder](../../../src/ordered/codec/snapshot.rs).

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
The Lean vacancy model carries its generation independently of the holder. Native acceptance exercises rotation, vacancy, `LKBASE07` recovery and a replacement grant with that generation.

Two reachable snapshot fixtures exhibit accepted encodings that differ from the encoder output.
A snapshot without object controls also decodes with two appended zero counts.
Two distinct retained old-root rows can be reversed and decode to the same ordered map.
A duplicate old-root revision is rejected.
The native tests also reject a retained hold with a missing or wrong-kind admission receipt.

The [manifest](area.json) records six source mutations and their expected diagnostics.
The pinned baseline verified ten items and all six mutations failed at their declared obligations.
