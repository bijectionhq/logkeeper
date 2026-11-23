# Study 75 · Replay one realized source history from either checkpoint

2026-11-23

## Question

Do an older base that must replay the seal and a newer base that already contains it recover the same exact writer, physical window, append receipts, and outstanding control obligations?

## Sources

Use the [chosen source](../64-chosen-append-recovery/report.md), [retained receipts](../69-retained-receipts/report.md), [realized seal](../73-realized-source-seal/report.md), and [canonical realized checkpoint](../74-realized-checkpoint/report.md).

## Models

Rank and select complete source frames including the original seal and installation evidence.
Run the original source decisions under an augmented replay image with a bounded realized slot table, exact window bindings, and retained append results.
Compare incomplete checkpoints, position-only suffix matching, replay through a current pool route, and rollback to a selected base without its chosen suffix.
Use TLC 2.19 and Lean 4.35.0.
