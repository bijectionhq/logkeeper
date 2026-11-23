# Study 46 · Decide the funded seal at the source

2026-11-23

## Question

Can a capacity authority irrevocably bind a prepare before a separate source seal without stranding capacity if the stream retires first?

## Sources

Use the [requirements](../requirements.md), the [stream reference](../07-reference/report.md), [move cancellation](../10-cancel-move/report.md), and the [numeric capacity](../43-concurrent-capacity/report.md), [prepared debit](../44-prepared-capacity/report.md), and [pool authority](../45-pool-authority/report.md) studies.

## Model and comparison

Compare a single ordered source seal that commits an existing vector with a binding decision at another authority followed by the source seal.
Use the same state for both candidates.
Model two separately moving pools, exact reservation attempts, delayed prepares and receipts, ordinary pressure, abort, source retirement, and retirement after target activation.
Assume local prepare and controller replacement preserve the ledger as in Study 45.
Treat certified target installation evidence as a premise.

## Properties and acceptance

- Every seal has its own immutable exact vector, including after either pool changes owners.
- Retirement before seal gives durable disposition for an outstanding attempt and can finish before pool reconciliation.
- Retirement after seal goes through the installed successor while its ordinary and recovery budgets remain charged.
- An exact canceled attempt eventually closes every local key under fair reachable reconciliation and cannot recreate a hold after closure.
- Old or partial receipts cannot authorize a distinct move.
- A sealed and funded move can finish while ordinary capacity is full and the source is unreachable.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 for a projection to the reference stream kernel and scoped capacity laws.
