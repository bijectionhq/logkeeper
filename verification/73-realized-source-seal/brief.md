# Study 73 · Bind a source move to the exact pool-issued extents

2026-11-23

## Question

Can an ordered move preserve the exact allocation issued by each pool through handoff and replay while keeping writer window order independent of physical allocation order?

## Sources

Use the [ordered source](../49-unified-source-history/report.md), [chosen funded appends](../64-chosen-append-recovery/report.md), [move recovery](../66-move-recovery/report.md), and [pool-local issuance](../72-pool-local-issuance/report.md).

## Models

Track a logical plan, local prepared receipts, the realized seal, target installation and exact cleanup.
Compare physical and source-scoped window ordering, equal-price substitutions, live resolution on takeover, and cleanup without exact identity and role.
Bind the exact prepared vector to the real source and activation reducers.
Use TLC 2.19 and Lean 4.35.0.
