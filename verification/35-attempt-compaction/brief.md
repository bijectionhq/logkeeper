# Study 35 · Compact activation attempt fences

2026-11-22

## Question

Can a target forget individual discarded-attempt markers while retaining exact readiness, unresolved physical cleanup, and the ability to refuse late commands?

## Sources

Use the [requirements](../requirements.md), [bounded registration](../20-registration-recovery/report.md), [custody channel lifecycle](../21-custody-channel-lifecycle/report.md), and [pending activation reducer](../34-pending-activation/report.md).

## Model

Keep one already authorized target intent with monotonically issued attempt serials.
Represent exact ready bindings, a cutoff for absent attempts, and charged cleanup separately.
Compare a cutoff that can cross a live ready row with a cutoff restricted to spent rows.
Let a target voter replacement carry the same logical admission state.
Treat exact physical registration and cleanup acknowledgments as authenticated decisions from the earlier custody contracts.

## Properties and acceptance

- Preserve historical replay and every future result when compacting spent markers.
- Preserve an exact ready binding and allow its later installation when it is still eligible.
- Refuse delayed admission for an absent attempt behind the cutoff.
- Keep its physical cleanup obligation even when its individual terminal marker is compacted.
- Replace voters before settling a compacted attempt, then settle its exact physical interest.
- Replenish credit only from the installed cutoff and bound physical pins independently.

## Tools and evidence

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for representation equivalence, delayed refusals over arbitrary replay, and the issued-window bound.
Each weakening must fail the named invariant or proof site.
