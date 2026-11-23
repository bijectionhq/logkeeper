# Study 64 · Replay funded commands from the exact chosen basis

2026-11-23

## Question

Does a physical recovery path reproduce the exact chosen append and window decisions under speculative frames, selector ambiguity, and changes to the allocator after choice?

## Sources

Use [canonical checkpoint envelopes](../51-checkpoint-envelope/report.md), [joint replay protection](../54-joint-recovery-protection/report.md), [funded appends](../62-funded-appends/report.md), and [staged vote isolation](../63-staged-votes/report.md).

## Model and comparisons

Order window installation, append, other source decisions, and window-release decisions together.
Use a canonical frame with lineage and ordered position independent of its logical data LSN.
Connect checked frame evidence to the existing funded append reducer, actual ranked acceptor protocol, and exact checkpoint envelope.
Compare exact selected control and data with using the newest window cursor, taking any intact frame at the right position, trusting a different lineage, and applying intact unchosen data past the installed cutoff.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- Two valid chosen certificates agree on each common exact frame.
- Replay from every certified selectable checkpoint restores the same final source and window book and the original outcomes in its suffix.
- A conflicting staged frame, another lineage, an incomplete suffix, or any durable suffix past the chosen cut cannot produce a different successful recovery.
- An appended frame uses its exact original request and position and spends the original funded range.
