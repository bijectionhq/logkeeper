# Study 70 · Derive the sealed source from the two pool preparations

2026-11-23

## Question

Do separate durable pool preparations suffice to order the actual source seal, survive coordinator loss, and reach the existing successor and receipt program?

## Sources

Use [ordered partial preparation](../43-concurrent-capacity/report.md), the [funded seal](../46-funded-source-seal/report.md), the [physical allocation ledger](../52-shared-extent-accounting/report.md), the [funded destination window](../65-funded-window-move/report.md), and [retained receipt recovery](../69-retained-receipts/report.md).

## Model and comparisons

Keep source planning and terminal choice in the existing ordered reducer.
Check per-pool preparations with exact independent receipts, including delayed delivery after abort.
Use the actual shared pool ledger in the Lean allocation and claim projection.
Compare exact custody with a timed return, dropped debit or fence on pool recovery, and a seal from only one receipt.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- Each prepared receipt corresponds to exactly paid live custody in its pool until the source's exact terminal result allows settlement.
- A partial vector cannot seal, and a delayed prepare cannot reopen an aborted scope after its local fence.
- Coordinator replacement preserves both prepared capacity and the possible exact continuation.
- The actual reserve and funded seal produce the original source image and replies expected by the successor receipt program.
