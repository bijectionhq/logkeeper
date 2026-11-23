# Study 108 · Recover copy withdrawal without re-admitting its bytes

2026-11-23

## Question

Can the original custodian recover an ordered withdrawal, preserve all other exact holds, and safely settle an already dispatched provider effect through either crash-selectable checkpoint?

## Sources

Use S02, S06, S89 and S92 in the [requirements](../requirements.md).
Compose the [shared custody graph](../19-shared-object-custody/report.md), [journal rotation](../26-journal-rotation/report.md), [provider closure](../40-provider-io-closure/report.md), and [ordered withdrawal](../107-protection-handoff/report.md).
Use the existing original-debit settlement rules.

## Model and comparisons

Compare durable withdrawal in the exact version's original custody phase against rebuilding that phase from on-disk presence or a checkpoint without its chosen continuation.
Check whether a pending withdrawal can be counted when issuing a second withdrawal.
Keep the obligation of the older still-selectable root, a live reader and a distinct delivery represented at the original custodian.
Compare positive dispatch from a chosen withdrawal against dispatch from a staged request.
Compare settlement by stable provider evidence against credit reuse on a probe.
Test whether effect execution requires the coordinator to remain online after dispatch.

Use safety invariants for recovery equality, retaining exact holds, effective authorization, stable charge release and the surviving input.
Use a temporal property for settlement when the custodian recovers, all exact holds finish and the provider can fence and perform the issued effect.
Use reachability witnesses for an older and a newer valid custody checkpoint.
In Lean, compose a deterministic custody reducer and physical provider execution with existing custody and replay proofs.

## Boundaries

TLC 2.19 models an exact copy in each of three AZs, one original version under withdrawal, one competing withdrawal, two custody checkpoint choices, at most one crash and one AZ loss.
Lean 4.35.0 checks arbitrary finite interleavings of the modeled chosen custody frames and exact authorized effects.
The study fixes the acknowledged input set, eligible exact-copy inventory and fault envelope.
Treat root-release permission, ownership of provider-write fences, authenticity of provider receipts and completeness of registered dependencies as premises.
Use the existing 60-second command limit in the study runner.
