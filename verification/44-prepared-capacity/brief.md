# Study 44 · Make provisional capacity visible at admission

2026-11-23

## Question

Can an ordered preparation hold be represented as an invisible implementation step when ordinary pool admission is observable?

## Sources

Use the [requirements](../requirements.md), [concurrent capacity comparison](../43-concurrent-capacity/report.md), and [ticket issuance model](../41-provider-ticket-compaction/report.md).

## Model and comparison

Compare an atomic vector abstraction that omits prepared holds with one that charges local prepared capacity before it authorizes a seal.
Start with a pool whose ordinary work fits before one move's provisional hold.
Block the move's remaining component in a different pool and issue ordinary work at the first pool.
Model a complete prepare-to-reservation transition so the charge moves between categories with no change in total occupied capacity.
Check that the representation preserves admission checks and that a complete prepared charge can become a durable committed charge without admitting new capacity.
Then connect the accounting representation to exact local admission, abort reconciliation, and authority changes.

## Properties and acceptance

- A successful ordinary admission fits after all prior partial holds.
- A complete transfer from partial to committed capacity preserves pointwise usage and the result of ordinary capacity checks.
- A prepare in one pool confers no seal authority by itself.
- Model a locally full pool with an incomplete move and compare the ordinary admission outcome with both representations.

## Tools

Use Lean 4.35.0 for the numeric refinement and a mutation of the charge projection.
Carry forward the distributed preparation assumptions from Study 43.
