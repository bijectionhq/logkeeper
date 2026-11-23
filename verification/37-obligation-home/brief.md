# Study 37 · Move the home of unresolved activation obligations

2026-11-23

## Question

Can all old target endpoints shut down while a source still needs its exact installation result and an original custodian may still receive a queued copy?

## Sources

Use the [requirements](../requirements.md), [custody issuer handoff](../23-custody-authority-handoff/report.md), [configuration closure](../32-configuration-closure/report.md), and [activation intent retirement](../36-intent-retirement/report.md).

## Model and comparisons

Use the same sealed cut and successor installation protocol for three routing policies.
Compare a stable home that resolves directly to a published owner, former owners that forward, and former owners that keep forwarding until all debts settle.
Represent the original result and physical copy key separately.
Check stale publication, pending transfer, delayed settlement, acknowledgment, and shutdown.
Abstract the distributed seal, exact provider fence, target capacity reservation, and authentication into explicit action premises.

## Properties and acceptance

- Move the exact unresolved book and its charges under a unique authority fence. Keep the original physical key.
- Publish only an installed owner and keep the stable route monotone across delayed announcements.
- Shut down old coordinators while the source and physical custodian cannot respond. Reconnect and settle both obligations through the stable home after repeated moves.
- Check which routing and endpoint availability premises give eventual reconciliation or shutdown.
- Check the route and book invariants for arbitrary finite owner histories, and isolate the information needed to discover a successor when the original endpoint has disappeared.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for the reference reducer and the information bound.
Exercise negative controls before the baseline checks in each tool.
