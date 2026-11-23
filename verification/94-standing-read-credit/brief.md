# Study 94 · Spend standing read credit at choice

2026-11-23

## Question

Can an installed authority choose an atomic first delivery from prepaid standing custody through window replacement and handoff without depending on acknowledgments from the old preparation path?

## Sources

Use [standing custody](../31-standing-custody/report.md), [funded window moves](../65-funded-window-move/report.md), [provider-local issuance](../72-pool-local-issuance/report.md), [retained delivery handoff](../89-sealed-delivery-handoff/report.md), and [atomic read capture](../93-atomic-read-capture/report.md).

## Model and comparisons

Compare reserving a lineage-wide delivery serial in asynchronous physical preparation with assigning it in the installed journal's choice.
Bind the physical charge and reserved serial range to the original paid window.
Compare successor activation when an old preparation or notification is lost, and release after an exact fence that contains a hidden chosen delivery.
Compare a correctly funded rotation with reuse of the original window, early refund, and publication that blocks ordinary service on optional read funding.
Use the existing atomic capture reducer for successful choice and bound the issuance arithmetic in Lean.
Use one move, one original borrow at most, and two distinct windows in TLC.

## Properties and programs

- Physical preparation reserves a bounded provider-local serial range.
- Journal choice assigns the next exact delivery key and its local physical borrow in the same step.
- A new paid window can serve while an old unassigned preparation remains unreachable.
- Replacing a window preserves its exact chosen assignments and original custody.
- Every old charge remains until exact fence and settlement evidence authorizes its original refund.
- An old generation stays spent after replacement.
- Losing optional fused-read funding does not block ordinary append or a separately funded split read.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
Run negative controls first.
Keep commands, configurations and traces under .results/.
