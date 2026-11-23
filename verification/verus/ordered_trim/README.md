# Ordered trim (L5)

`Command::Trim` uses the shipped `retention::trim` transition in
`src/ordered/retention.rs`. The transition checks the checkpoint bound, the
exact-cut observation, and the live-suffix observation before changing the
queue or its counters. A successful trim removes exactly the prefix of length
`through - floor`. Its receipt credits and counter decrements equal the
removed charges, per class. A refusal leaves the queue and the counters
unchanged. The proof includes the production queue loop, the traversal of all live hold
map entries, and the shipped `admission::pins_suffix`.

| Lean reference | Rust projection and Verus law |
| --- | --- |
| `Logkeeper.Protocol.pinsSuffix` and `trimPrefixSafe` | Each live hold contributes its half-open start and end LSNs. The selected checkpoint and trim cut contribute their exclusive LSNs. `trim_preserves_replay` also checks the shipped pin predicate at these endpoints. |
| `Logkeeper.Protocol.trimCredit` and `trim_credit_matches_removed_records` | Drop the already-trimmed prefix of the append history to obtain the retained queue. The record projection maps `AppendClass::Data` to ordinary and computes the charge as `byte_end - byte_start`. The Verus `trimCredit` sums the same prefix by class, and `trim_credit_matches_removed_records` checks the queue and both refunds. |

The State adapter supplies exact cut identity from `State::cut`, contiguous
queue positions, the LSN fields of each live hold, and the two retained-charge
totals. The Verus contracts state those inputs explicitly.
The adapter's projection of `State` and the invariant for all accepted
snapshot encodings remain separate refinement obligations.

The controls ignore the checkpoint, bypass the suffix predicate or the hold
scan, drop a record beyond the removed prefix, and omit the maintenance
counter refund. Lean
supplies the safe-cut witness and counterexamples for ignoring a pin, passing
the checkpoint, or refunding the wrong class.
