# Study 110 · Derive an RTDB recovery closure and retain its custody proof

2026-11-23

## Question

Can the installed journal derive the complete recovery obligation from an exact RTDB checkpoint and chosen suffix and recover its physical custody evidence after publisher replacement?

## Sources

Use S02, S06, S40, S57 and S94 in the [requirements](../requirements.md).
Read the relevant RTDB Allium and Rust paths in the [pinned source audit](source-audit.md).
Compare [certified checkpoint reconstruction](../16-checkpoint-reconstruction/report.md), [checkpoint envelope](../51-checkpoint-envelope/report.md), [joint recovery protection](../54-joint-recovery-protection/report.md), and [registered publication](../109-dynamic-protection/report.md).

## Model and comparisons

Derive the base dependency names from a typed projection of the actual RTDB table registry and trie-detail shapes.
Include physical custody of the necessary external payload objects of the exact retained suffix.
Compare the complete derived set with using only the checkpoint inventory, dropping retained and auxiliary dependencies, and checking only the latest selector.
Compare exact physical generations against a logical-path-only receipt, and bound a legacy table body using authenticated inventory evidence.
Compare retaining the exact receipt set in the chosen publisher decision against retaining its cut alone and recontacting the previous publisher.

Use invariants for complete coverage, authenticated table bodies, exact carrier generation and distinct failure-domain evidence.
Use a temporal check for recovery under a reachable current majority and unavailable prior publisher.
Use Lean to verify typed enumeration against independent declared reads and compose existing ranked membership and crash-selector proofs.
Use TLC 2.19 and Lean 4.35.0 with the study runner's 60-second per-command limit.

## Boundaries

The TLC closure and replacement cases abstract cryptographic verification, each exact receipt's physical backing and current group installation.
They compare two root choices and one physical relocation or publisher replacement.
The typed Lean model does not verify the production Rust parser or provider implementation.
