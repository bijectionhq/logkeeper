# Study 56 · Encode and exhaust the incarnation inventory

2026-11-23

## Question

How can the incarnation inventory use fixed-width IDs and bounded checkpoint bytes while preserving exact custody and exclusion of delayed proofs when counters exhaust or an older checkpoint is selected?

## Sources

Use [selectable checkpoint and evidence protection](../50-joint-checkpoint/report.md), [canonical checkpoint framing](../51-checkpoint-envelope/report.md), and [bounded incarnation inventory](../55-pool-incarnations/report.md).

## Comparison

Compare refusal at issuer exhaustion and terminal quarantine at access-epoch exhaustion with wrapping or reusing exhausted values.
Check checkpoints with exact suffix recovery against opening a stale image as the current control state.
Use one fixed-width record layout with sorted incarnation IDs and a bounded row parser.
Leave the separately charged custody book and physical effects in the preceding reference.

## Properties

- Every fault can close eligibility, including at the largest access epoch.
- Exhaustion leaves existing custody and its settlement rules executable.
- No later issue or return can reuse a retired scope or access proof.
- The inventory section decodes uniquely and obeys a byte cap for both selectable images.
- Recovery uses the chosen issued watermark and terminal phase before resuming admission.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap, and a 60-second case limit.
Use Lean 4.35.0 for codec, byte bound, and finite counter laws.
