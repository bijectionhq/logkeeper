# Ordered checkpoint custody

The harness imports [the shipped checkpoint guards](../../../src/ordered/checkpoint_guards.rs).

| Reducer input or decision | Lean reference in [OrderedGuards](../../lean/Logkeeper/OrderedGuards.lean) | Verus control and failing law |
| --- | --- | --- |
| Publication custody and the exact pending custody | `OrderedCheckpoint.matches_preparation` | `ignore-publication-custody` → `publication_keeps_prepared_custody` |
| Proposed preparation revision and the selected revision | `OrderedCheckpoint.next_revision` | `reuse-preparation-revision` → `preparation_revision_advances` |
| An exact old root is still a preparation source or named by a hold | `OrderedCheckpoint.may_close` | `close-despite-hold` → `a_held_checkpoint_cannot_close` |
| An exact retained root is above the erasure floor and open to new acquisition | `OrderedCheckpoint.may_acquire` | `admit-closed-root` → `a_closed_checkpoint_refuses_new_acquisition` |

`State::prepared_checkpoint` compares the full `Custody` value, including its allocation UUID, revision and provider fingerprint. Separate checks enforce the exact cut, root and nonzero manifest.
`PrepareCheckpoint` applies the successor-number check only when installing a new preparation. An exact retry may return the existing preparation.
`CloseCheckpoint` evaluates the live hold query over the exact old checkpoint after checking its identity.
`State::checkpoint_open` applies the retained-root and closure queries to the requested custody and is used for preparation and fresh hold acquisition.
The Verus laws take the query results as inputs and the Rust callers compute them from ordered state.

These predicates verify the ordered authorization for checkpoint custody.
[Study 20](../../20-registration-recovery/report.md) models an original custodian's receiver floor across cancellation and compaction.
[RecoveryCertificate.Binds](../../lean/Logkeeper/RecoveryCertificate.lean) also requires the physical version of each member, supplied in RTDB by the archive manifest and the provider observations.
The receiver floor, physical borrows, provider effects and manifest member bindings remain separate proof obligations.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
