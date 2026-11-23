# Study 52 · Charge shared physical extents across concurrent uses

2026-11-23

## Verdict

An immutable physical allocation has one debit at its actual pool.
Each logical user has its own durable custody reference.
Sharing the allocation can leave physical usage unchanged even at capacity.
A repack or independent copy needs a new debit even if it stores the same content.

Closing a reference leaves the physical debit with the original extent.
An old borrow can retain that extent while another use switches to a new copy.
The debit returns after the original version's stable disposition and survives replacement of its pool controller.

## Bounded comparison

[SharedExtents.tla](SharedExtents.tla) uses two independently admitted references, physical borrows, ordinary traffic, a pool capacity of two units, and up to three exact physical extents.
Two extents can share a pool and a third can occupy a different pool.
The extents can store the same logical content.
Every physical extent costs one unit in the finite comparison.
The per-reference policy bills an additional physical unit when a second reference registers against the same extent.

| Policy and case | Extents | Distinct states | Checked result |
| --- | ---: | ---: | --- |
| Exact physical debit | 2 | 7,914 | Five safety laws hold at the bound. |
| Additional physical billing per reference | 2 | 6,288 | The same safety laws hold. The full-pool sharing program is excluded. |
| Exact physical debit across both pools | 3 | 111,588 | Five safety laws hold at the bound. |
| Exact physical debit with the old custodian unreachable | 3 | 73,690 | Same safety laws hold. The old debit can persist while a separately funded copy serves. |

The laws cover pointwise capacity, charging possible or actual allocations, retaining active borrows, protecting all live references, and exact absence for refunds.
Provider disposition is atomic in this comparison. It stands for validated closure of the exact operation path and stable physical absence.
The bounded checks establish safety and feasible programs.
Provider availability and unconditional disposal are outside their temporal scope.

| TLC weakening | Shortest safety counterexample |
| --- | --- |
| Deduplicate by logical content | Reserve a second physical extent while continuing to charge only the first. One transition. |
| Return credit when a reference closes | Register and close a reference while the physical extent remains. Two transitions. |
| Dispose with a live borrow | Register, borrow, close the reference, fence and dispose. The borrower loses its exact bytes in five transitions. |
| Use another copy's receipt | Dispose a copy and use its absence to refund the other still-allocated extent. Five transitions. |
| Lose debits at controller recovery | Recover the controller and drop an existing allocation's debit. One transition. |

## General proofs

[SharedExtentAccounting.lean](SharedExtentAccounting.lean) composes live manifest references and borrows with version-scoped provider actions and a numeric ledger.
It checks eight theorems using standard axioms only.
The pointwise capacity and unique charge invariants hold after each modeled transition and over arbitrary admitted finite traces.
Before a provider effect can execute, its exact allocation has a debit.
Publication requires actual provider bytes.
A live checkpoint or evidence root and an independent old borrow both keep their physical backing and debit.
A borrow precludes a valid refund for its extent.

The additional-reference program leaves pointwise usage unchanged.
A fresh allocation increases usage by its own footprint at its actual pool.
The numeric model draws the available byte budget from exact allocation identities and keeps logical acquisitions in the custody reducer.
The two Lean controls remove the exact scope of a refund and the debit requirement for a provider event.
Both fail their corresponding laws.

## Amendments

[A200–A202](../amendments.md#study-52--2026-11-23) require exact allocation charging, exact durable disposition before refund, and recovery of the debit book.

## Acceptance programs

- P63. Charge an existing extent and fill the rest of its pool. Attach two uses, take a borrow, close the borrower's use, and recover the controller with the independent borrow and the other use still active. TLC reaches this in six transitions. The per-reference policy excludes the same program at the same bound.
- P64. Reserve and materialize a same-content copy in the other pool and then recover both controllers. Both copies keep their debits in a four-transition witness. Repack in the original pool and retain the old borrow alongside the newly charged extent in a separate five-transition witness.
- P65. Close the original use and its extent while the original custodian is unavailable, then materialize a separately funded copy and register a surviving use. The old bytes stay charged in a six-transition witness.

## Residue

The Lean model takes a stable and exact allocation identity, its pool, and its measured cost as inputs.
A physical pack can realize this allocation unit, with the pack's full footprint while any constituent survives.
The proof assumes each logical physical version maps to its exact allocation and the provider respects durable effect and disposition scope.
The reference and borrow gates model already-authorized, separately metered control work.
Controller replacement is exact book recovery in the reference.
The study still needs byte-accurate admission, bounded metadata representation and a separate evacuation contract for physical pool loss.

## Reproduction

Run with Python 3.13, Java 21.0.13+9, TLC 2.19 and Lean 4.35.0.
The runner saves configurations, traces and diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/52-shared-extent-accounting/run.py
```
