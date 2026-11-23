# Study 100 · Recover returned capacity in the installed quorum

2026-11-23

## Question

Can a successor reconcile a chosen refund after an AZ loss without spending the refund again when it also funded a hidden chosen charge?

## Sources

Use the [ranked handoff](../32-configuration-closure/report.md), [pool-local authority](../72-pool-local-issuance/PoolTakeover.lean), [local settlement redo](../98-settlement-redo/report.md), and the [contract review](../architecture-reopening/contract-review.md).

## Model

Use three AZs with two surviving voters, one installed basis, two crash-selectable media paths per voter and a full one-unit pool.
Compare a hidden refund, a hidden refund followed by committed reuse, raw staging with no accepted vote, and a qualifying minority acceptance included by ranked recovery.
Check dropping the hidden vote, stripping its newest command, using an exact historical receipt as credit, selecting a same-length rival, trusting one selector, and funding a side effect before a new debit is chosen.
Lean composes ranked quorum intersection with the existing typed local ledger and journal replay over arbitrary finite handoff and media histories.

## Bounds

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
The bounded model holds the old accepted records and one failure fixed during each run.
The final policy and media premises remain explicit.
