# Study 55 · Bound outstanding pool incarnations

2026-11-23

## Question

Can a bounded regional inventory allow repeated physical replacements while preserving each unavailable pool's original custody, and what evidence allows a returned pool to rejoin?

## Sources

Use [provider fencing and compaction](../41-provider-ticket-compaction/report.md), [exact pool authority](../45-pool-authority/report.md), [pointwise physical accounting](../52-shared-extent-accounting/report.md), and [independent evacuation](../53-pool-evacuation/report.md).

## Comparison

Compare allocating a durable incarnation slot before first exposure with refunding on loss or charging only for eligible pools.
Check return with exact incarnation, access epoch, and current book validation against accepting stale proofs.
Keep provider terminal evidence, the durable inventory, and physical capacity as independent resources.
Model exact provider commands using the existing Lean physical ledger.

## Properties

- Failure needs no new control slot and preserves the original allocation scope.
- Bounds hold after any number of unsettled replacements.
- A returned address remains quarantined until exact current evidence passes.
- A retired namespace and its outstanding proof identities stay closed.
- Exact settlement and successful validation remain possible at the limit.
- Determine when finite inventory and continued replacement become incompatible.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and a 60-second case limit.
Use Lean 4.35.0 for exact physical ledger composition and the replenishment bound.
