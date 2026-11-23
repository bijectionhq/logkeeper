# Study 80 · Certify a chosen read marker's applied result

2026-11-23

## Question

What exact evidence lets RTDB accept a fresh barrier after the result issuer disappears, while refusing a chosen marker that never succeeded or a signed packet transplanted from another journal scope?

[Study 28](../28-ordered-application/report.md) proves the read marker's applied result under ordered application.
[Study 79](../79-rtdb-failover/report.md) uses that result through an abstract authentication predicate at the RTDB delivery gate.
This study replaces that predicate's abstract success condition with a reference issuer and canonical receipt tied to the exact chosen marker and the result of the actual source reducer.

## Comparison

Separate choice, successful application, receipt issuance, and delivery.
Test a chosen marker before application, a chosen refusal after retirement, a successful marker with a later append, and a genuine foreign signature for the same numeric fields.
Remove the result cut, ordered position, or source scope from the checked signature.
Require an already-issued result to survive issuer loss with verification material and protected data available.
Test a successful overlapping invocation after retirement without reopening eligibility for new calls.

Use TLC for the finite decisions and one temporal comparison.
Use Lean for exact fixed-width representation, deterministic application at the chosen ordered slot, and issuer-to-receiver refinement.
Reuse the chosen source reducer and the existing RTDB receiving gate.

Abstract cryptographic enforcement, attestation transport and trust metadata, nonce allocation, and actual snapshot materialization.
The [report](report.md) records the evidence and its limits.
