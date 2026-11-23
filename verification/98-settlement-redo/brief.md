# Study 98 · Reuse a refund through crash-selectable checkpoints

2026-11-23

## Question

When may a full pool spend the credit from an exact refund, and what must it reserve to recycle that credit through repeated crashes and checkpoint rotations?

## Sources

Use the [exact media barriers](../25-media-crash-consistency/report.md), [repeated rotations](../26-journal-rotation/report.md), [recovery capacity](../42-recovery-capacity/report.md), [pool-local ledger](../72-pool-local-issuance/report.md), [receipt selector lifetime](../91-receipt-selectors/report.md), and [settlement workspace](../97-settlement-workspace/report.md).
Hold exact physical disposition, ordered local authority, full ordinary occupancy and the crash outcomes fixed across candidates.

## Models and comparisons

Compare a whole-image publication with a stable selector before reporting refund, and an exact refund command in the owner's durable ordered suffix.
Keep the initial stable image as prepaid residency in both variants.
Account for one additional image and a reserved redo frame when they overlap.
Test a volatile selector, durable bytes without durable discovery, early reclaim based on visibility, and insufficient overlap reserve.
Pause the selector barrier independently of the durable log to compare first refund and bounded turnover.
Use an actual `PoolState.Step.refund` and `JournalRotation.Step.append` in one Lean transition system.
Keep pre-refund custody checks and exact provider observation as inputs.

## Properties and programs

- Every legal crash choice reconstructs the exact confirmed refunds and any dependent ordinary reuse in the same order.
- A refund only returns its own physically closed and absent original charge.
- Both the older base and required redo can survive while a replacement selector is unstable.
- Recycle workspace at full ordinary capacity with local durability paths available.
- Bound reserved space by the sum of distinct overlapping physical allocations.

## Bounds and tools

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
TLC uses one original debit at a time, three generation intervals, unit-sized redo and a two-unit alternate base, and at most two crashes.
Lean checks the exact reducer, ordered sequences and crash-selection refinement over arbitrary finite histories.
Run deliberate weakenings before passing cases and retain commands, raw traces and proof diagnostics under .results/.
