# Study 54 · Certify an entire recoverable cut

2026-11-23

## Question

Which coverage rule allows every crash-selectable checkpoint and tail to recover the exact installed history after any one AZ loss, when journal voters and physical object pools scale separately?

## Sources

Use [ranked membership recovery](../32-configuration-closure/report.md), [checkpoint supersession](../50-joint-checkpoint/report.md), [canonical checkpoint opening](../51-checkpoint-envelope/report.md), and [physical evacuation](../53-pool-evacuation/report.md).

## Model and comparison

Compare a common-cut certificate for distributed input coverage with requiring every surviving recovery quorum to include a voter that holds the entire recovery image locally.
Use the same current voter family, eligible zones, old and new checkpoint selectors, and separately placed components and suffix attachments.
Check reconfiguration, a cached certification request, checkpoint publication before selector durability, and exact input withdrawal.
Use Lean to join canonical envelope opening, ranked quorum recovery, and the shared physical ledger for arbitrary numbers of inputs and selectable views.

## Properties

- The same admissible AZ removal leaves an eligible current recovery quorum and exact readable coverage of every input of every crash-selectable view.
- A compatible checkpoint and suffix reconstruct precisely the chosen installed history.
- Cached authority and cut evidence cannot certify a successor scope.
- Protect old-only tail attachments until the last crash selector that needs them is excluded.
- Show a program with independent physical placement and no voter that stores all required objects locally.

## Tools

Use TLC 2.19 with a 512 MiB heap, a single worker and a 60-second case limit.
Use Lean 4.35.0 for the general reference composition and independence controls.
