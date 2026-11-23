# Study 96 · Settle standing credit at its original provider

2026-11-23

## Question

Can the original provider install a recovered standing-window fence, honor a hidden chosen borrow, and refund the original charge without accumulating terminal window records?

## Sources

Use [provider effect closure](../40-provider-io-closure/report.md), [provider ticket compaction](../41-provider-ticket-compaction/report.md), [pool-local issuance](../72-pool-local-issuance/report.md), [standing credit](../94-standing-read-credit/report.md), and [standing checkpoint and seal recovery](../95-standing-read-recovery/report.md).

## Model and comparisons

Bind original provider admission to positive membership of the exact charged allocation.
Install the authenticated frozen delivery book while preserving provider operation states.
Apply the existing physical refund only after exact frozen drain and stable absence.
Compare fence selection from local observations, issuing against a missing frozen row, terminal replay, early physical refund, absence-as-permission, per-window tombstones, and cleanup that needs spare headroom.
Use three consecutive windows and one charged slot in TLC.
Compose the exact chosen source seal, original effect gate and pool refund over arbitrary finite traces in Lean.

## Properties and programs

- Delayed work after fence is eligible only when it exactly matches the frozen chosen row and still-live original charge.
- A terminal borrow cannot restart or take a later effect.
- Installing the same fence preserves earlier provider work, and a different fence cannot replace the installed evidence.
- A refund requires authenticated frozen drain, lower provider closure, and exact physical absence.
- Refund at full capacity creates new room.
- A retired allocation remains ineligible through later pool histories without keeping a terminal enforcement record for it.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
Run negative controls before reference checks.
Keep commands, configurations and traces under .results/.
