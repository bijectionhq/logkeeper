# Compact-image recovery

This area imports the [shipped row checks and insertions](../../../src/ordered/codec/snapshot_checks.rs)
used by the [LKBASE08 decoder](../../../src/ordered/codec/snapshot.rs).
The Lean reference is in [CompactImage](../../lean/Logkeeper/CompactImage.lean)
and [CodecDomains](../../lean/Logkeeper/CodecDomains.lean).

| Lean definition | Checked Verus boundary |
| --- | --- |
| `generationInRange` | `generation_in_range` checks the stored generation independently of grant occupancy. |
| `oldRootKeyIncreases` | `old_root_key_increases` requires the candidate revision to exceed the largest previously retained revision. |
| `objectControlTrailerCanonical` | `object_control_trailer_canonical` requires the presence bit inferred from remaining input to agree with the encoder's condition for emitting the two counts and rows. |
| `leaseRowValid` | `lease_row_valid` requires a bounded positive enrollment serial, a retained owner, lease-end bounds, and an increasing key. Saturation of the Rust time sum gives the same comparison for a representable lease end. |
| `fenceRowValid` | `fence_row_valid` requires bounded position and time and an increasing object name. |
| `rootReferenceRowValid` | `root_reference_row_valid` requires known root membership and an increasing revision. |
| `holdReceiptMatches`, `allSnapshotRowsValid` | `hold_receipt_matches` checks the exact admission position. `all_snapshot_rows` traverses every map value for the hold-to-receipt and withdrawal-receipt-to-fence joins. The Rust closures supply the exact origin, request ID, outcome kind and value equality checks. |
| `receiptPositionFresh`, `receiptRowValid`, `receiptPartition`, `receiptExpiryPartition` | `insert_snapshot_receipt` derives the exact retry key from the typed receipt, checks order, horizon and liveness, and uses the matching decision position as the uniqueness key. It preserves a bijection between retained retry keys and seen positions. The deadline index contains exactly the retained keys whose deadline is future. Verus takes the deadline as a projection of the request identifier and live-hold ownership as an input to the row check. |
| `boundedMap`, `reducerInvariant` | `insert_snapshot_row` inserts at the supplied key and preserves the predicate on all other map entries. The decoder supplies a worker UUID, checkpoint revision, hold request ID, enrollment, root revision or object name. The function under proof is generic over those key and value types. |

The [manifest](area.json) includes mutations that accept a repeated decision position,
an explicit empty object-control trailer, or an out-of-order old-root revision.
Native acceptance tests derive usable compact images from reducer decisions and then
exercise each of these changes to the image. They also check the unchanged spelling,
including decode and re-encode of the old-root fixture. The image tag stays `LKBASE08`.

## Round-trip statements

`compactImageBytesAdmissible` is the layout projection of the accepted-byte domain.
`accepted_compact_image_bytes_reencode_exactly` proves the layout identity for every
finite input with that projection. It uses an exact consumed-byte decomposition and
the correspondence between old-root rows and map entries as hypotheses. The Lean
model orders the rows by revision. The Verus law uses the actual ordered BTreeMap
iterator to recover their order from the same revision/row pairs. The layout models
the rest of the accepted frame by its consumed bytes. Equality between those bytes
and the bytes produced from each typed field remains a parser and encoder refinement
obligation.

`compactImageAdmissible` is a typed-domain specification over `ReducerImage` and
the remaining parser and reconstruction checks. Encode from a state belonging to
the same fresh installation passed to `decode_base`. Placement, limits, initial
window/checkpoint, voter scope, and the object-control budget come from that
installation. The state must pass the decoder's coordinate, collection, reference,
lease, hold and receipt checks. The retained records must form the checked history
and carry the matching fingerprints, byte charges and window coordinates.
Map keys, receipt placement, the expiry index and retained-byte totals must agree
with what the decoder derives from the serialized values. The genesis state at
position zero is outside this compact-image domain.

## Remaining refinement

`reducerInvariant` is the reusable specification on `ReducerImage`. Lean lists and Verus sequences use the same projections. Ordered maps contribute their key sequences in iteration order. Composite keys and names use order-preserving integer representations. Bounds come from the decoder configuration and admission limits. Leases contribute exact enrollment membership and end time. Root membership, reference coverage, object-control bytes, and withdrawal receipt equality come from the corresponding state queries. A hold contributes its exact matched receipt position, or no position when the join fails. The [writer area](../ordered_writer/README.md) separately checks that the shipped vacancy transition preserves the stored generation.

The decoder accepts multiple distinct receipt keys with the same decision position. A native test fills the retry book to its decode bound with those rows, applies one decision, and observes that the resulting encoding fails to decode. The reference invariant requires unique receipt positions, as an applied decision records at most one receipt. F4 calls for rejecting this image and the two accepted aliases above under the existing format tag. The decoder change is tracked in PL3c. Whole-image acceptance still needs a proof that the Rust parser and state construction implement the projections above.

The expanded baseline verifies 13 items. All seven source controls fail at their declared obligations.
The whole Rust parser still needs a proof connecting byte consumption, every tag
and field, the typed map projections and the encoder traversal to these contracts.
The current checks establish the insertion algebra and receipt partition. They take
the other per-row guards, composite key orders and membership queries from the
decoder. Closing the implication to the full `reducerInvariant` also requires
proving the roster and old-root coordinate checks, the hold partition and cut
coverage, the exact joins to receipt outcomes, record history and liveness accounting,
and global reference coverage and aggregate budget. The [writer area](../ordered_writer/README.md)
checks generation preservation through vacancy.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
