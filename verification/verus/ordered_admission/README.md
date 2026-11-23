# Ordered admission

The harness includes the shipped [admission helpers](../../../src/ordered/admission.rs)
used by the ordered reducer and the compact-image decoder. The Verus laws
call those functions and compare their results with the named definitions
in [`Logkeeper.OrderedAdmission`](../../lean/Logkeeper/OrderedAdmission.lean).

| Lean definition or theorem | Verus law | Production decision |
| --- | --- | --- |
| `debit` | `debit_matches_reference` | Return the exact sum when it fits the supplied ceiling. |
| `maintenance_at_data_ceiling` | `maintenance_at_data_ceiling` | Refuse a positive debit at an exhausted ordinary ceiling and accept a separately funded maintenance debit. |
| `pinsSuffix` | `pins_suffix_matches_reference` | Protect a nonempty held suffix if it intersects the prefix below the proposed exclusive trim floor. |
| `retainsReceipt` | `retains_receipt_matches_reference` | Retain a receipt before expiry or while its live hold remains. |
| `matchesFingerprint` | `fingerprint_equality_matches_reference` | Require equal byte sequences. |

Rust's unsigned counters map to Lean naturals and optional debit totals
map through `debit_value`. Slice views map to lists of bytes in their original
order. Verus covers all `u64` inputs and slices admitted by Rust. The Lean
theorems range over all naturals and finite byte lists. For example, a
ceiling of 1 with usage 1 and charge 1 exhausts ordinary credit, while
usage 0 and charge 1 exactly fill a separate reserve of 1. A hold over
`[1, 2)` first intersects the removed prefix at trim floor 2. At receipt
position and expiry 1, a live hold changes the result. The one-byte lists
`[0]` and `[1]` witness an equal-length fingerprint mismatch.

The pinned Verus baseline reported 10 verified items and zero errors.
All eight controls failed at the postconditions declared in
[`area.json`](area.json). Four change the function bodies, and four
also weaken the shipped contracts to exercise the independent laws.
The Lean runner checks four reference theorems and four corresponding
mutations.

The proof covers the local predicates and debit arithmetic. Full reducer
receipt handling, trim refunds (`Protocol.trimCredit`), per-command charge
derivation and accounting, selection of valid holds and ceilings, and
compact-image preservation remain separate obligations.

Run the [Verus runner](../README.md) with `ordered_admission` and the
[Lean reference control runner](../../lean/README.md) for both layers.
