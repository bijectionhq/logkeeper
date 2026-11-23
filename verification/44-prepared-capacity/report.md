# Study 44 · Make provisional capacity visible at admission

2026-11-23

## Verdict

A local prepare changes ordinary admission before the move can seal.
The abstract capacity ledger must expose that debit if its ordinary admission decision is exact.
An exact seal commitment changes the classification of the complete held vector with no change to pool usage.

## Properties and comparison

| Property | Evidence |
| --- | --- |
| A successful ordinary capacity check fits after charging all prepared holds. | Lean proves `a_prepared_hold_is_visible_to_ordinary_admission`. |
| Attributing already prepared credits to the seal preserves each pool's usage and ordinary admission decision. | Lean proves `moving_owned_credit_to_sealed_accounting_preserves_usage` and `moving_owned_credit_preserves_ordinary_admission` for arbitrary pool types and natural-number amounts. |
| One missing vector component bars seal authority. | Lean proves `an_incomplete_vector_refuses_seal`. |
| Hiding a provisional debit can change which ordinary requests must be admitted under exact available-capacity semantics. | Lean proves `omitting_prepared_capacity_cannot_preserve_maximal_ordinary_admission` with two unit pools. |

Both representations use the same ordinary and committed usage.
The fully charged representation also includes prepared usage.
An abstraction that allows any additional admission refusal could mask this example by refusing the operation.
That abstraction would leave the ordinary availability contract unspecified at the disputed point.
The design keeps the physical debit explicit and leaves queueing and scheduling to their own contracts.

The negative control leaves the prepared credit in place when attributing it to the seal.
Lean rejects the conservation law because the same credit is counted in both categories.
The unmutated model checks five reported theorems with standard axioms only.

## Amendment

[A171](../amendments.md#study-44--2026-11-23) makes provisional debits explicit and keeps exact seal commitment as one semantic decision.

## Acceptance programs

P46 starts with two unit pools.
Put one unit of ordinary work in the second pool.
Prepare the first pool for a move that needs one unit from each.
The complete-vector guard refuses to seal, and a new ordinary unit fails its capacity check at the first pool because its only unit is held.
The abstraction that charges only sealed and ordinary work offers that unit again.

When all needed components have been prepared, bind the existing vector to the exact move.
Each pool exposes the same available capacity before and after that decision.
An ordinary caller needs no new operation or result variant for this reclassification.

## Residue

This is a numeric refinement of the commitment transition under its stated ownership premise.
It leaves open how independent authorities certify that ownership, keep it through handoff, and compact aborted identities without accepting stale requests.
The two-pool argument concerns the capacity check after any queue and policy decisions, with no timing or starvation claim.

## Reproduction

Run from the Logkeeper repository with Lean 4.35.0 and Python 3.13.

```sh
LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/44-prepared-capacity/run.py
```
