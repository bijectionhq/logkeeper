# Study 53 · Separate evacuation from physical disposition

2026-11-23

## Question

Which facts allow Logkeeper to restore the one-AZ protection of an immutable recovery input while its old pool stays unreachable or has outstanding physical obligations?

## Sources

Use [current-membership durability](../13-install-durability/report.md), [checkpoint residence transfer](../22-residence-transfer/report.md), [pool authority](../45-pool-authority/report.md), and [pointwise physical accounting](../52-shared-extent-accounting/report.md).

## Model and comparison

Model an exact immutable recovery image, independent pool debits, scoped staging evidence, placement, and the current failure domains of eligible copies.
Compare independently funded replacement with moving the old debit, requiring access to the old custodian at cutover, and substituting pool count for fault-domain coverage.
Represent provider effects and exact terminal disposition by the existing custody and accounting relation in Lean.
Abstract the image bytes to their exact bound identity and model authentication and durable observation as premises.

## Properties and acceptance

- A fault or routing change grants no reusable credit and does not rebind an old physical borrow.
- Restored protection requires charged exact copies across independent AZs.
- Planned withdrawal preserves the full protection contract.
- With a stable surviving source, independently funded eligible destination, and fair reachable operations, ordinary progress can restore protection without the old pool.
- A fully used surviving pool cannot spend failed-pool capacity. Distinct spare capacity must exist in a suitable fault domain.
- Old scoped settlement and access to the replacement can advance independently.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 to check arbitrary-domain placement properties against the accounting reducer from Study 52.
