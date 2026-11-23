# Study 43 · Reserve concurrent recovery across failure domains

2026-11-23

## Question

Can concurrent handoffs acquire exact cross-domain capacity, complete once sealed, and preserve each other's claims through contention and crash recovery?

## Sources

Use the [requirements](../requirements.md), [move cancellation](../10-cancel-move/report.md), [physical provider closure](../40-provider-io-closure/report.md), and [recovery capacity composition](../42-recovery-capacity/report.md).

## Model and comparison

Compare an atomic capacity vector with per-domain holds acquired in one durable order or in arbitrary order.
Model ordinary admission, independent residency and workspace needs, and an already charged obsolete copy.
Keep the per-move terminal decision independent of a coordinator restart.
Exercise cancellation of partial prepares and a strictly funded source seal.
Check pointwise capacity and scope, including layouts with aggregate room in the wrong failure domain.

## Properties and acceptance

- Preserve each committed reservation and every retained physical charge under competing ordinary and recovery work.
- Refuse a source seal until its complete exact capacity vector is held.
- Admit a move under an atomic vector or ordered partial reservations without cyclic wait in the modeled contention case.
- Abort and return partial holds from a durable exact decision, including after coordinator replacement.
- Keep old custody charged through timeout or unrelated settlement.
- Read the exact cut with its earlier outcomes using a current recovery majority when funded.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 for pointwise capacity, scoped accounting, ordered wait dependencies, and composition with Study 42.
