# Study 70 · Derive the sealed source from the two pool preparations

2026-11-23

## Verdict

A preparation receipt remains backed by capacity at its original pool through coordinator replacement.
The source orders either abort or seal.
It can seal only against the full exact vector, and its seal binds the successor at the same ordered position.
After abort, each custodian installs an effective local fence before returning any charge.
A delayed prepare arriving before that fence can still acquire a charged hold.
It cannot authorize a seal, and local reconciliation closes and settles it.

## Bounded comparison

[DistributedPrepare.tla](DistributedPrepare.tla) checks two pools of capacity two, one pre-existing debit, one possible ordinary debit per pool, one move, and at most one coordinator loss.
Two TLC baselines each explored 272 distinct states.
The safety baseline checks pointwise capacity, live backing of delivered receipts, the full committed vector, and monotone closure at each pool.
The temporal baseline checks that a pending decision eventually resolves, a sealed move eventually installs, and an aborted move eventually closes both scopes and settles all holds.
It uses weak fairness for coordinator recovery, a continuously enabled choice of seal or abort, installation, and each local fence and return.
The finite witness for coordinator loss after a partial preparation reaches the original installation in seven transitions.
The abort witness orders cancellation before delayed prepares, then fences and settles both pools in eight transitions.

| Weakening | Counterexample |
| --- | --- |
| Seal after one pool responds | Order the plan, prepare one pool, and seal with the other pool unfunded. Three transitions. |
| Expire a live hold | Plan, prepare, and return the live debit while the source still has its receipt. Three transitions. |
| Lose a live hold on pool restart | Plan, prepare, and recover a pool without its debit. The independently delivered receipt still exists. Three transitions. |
| Lose an abort fence on pool restart | Plan, abort, fence one pool, and recover it without its fence. The original request can become admissible again. Four transitions to loss of closure. |
| Remove fair coordinator recovery | TLC finds an execution with a permanent coordinator outage after partial preparation. Even the second local receipt can arrive while the source never orders an outcome. |

## General proofs

[PrepareLedger.lean](PrepareLedger.lean) checks six theorems using the existing paid ledger transitions.
Creating a local preparation adds its exact charge alongside live append windows and old held claims.
For a sound starting state and two eligible extents with a pending exact plan, two existing allocation and claim steps construct the complete vector.
The resulting local statements establish the exact owner, claim and live debit for each planned extent.
Authentic receipts supplied for those statements satisfy the existing source seal rule.

[ChosenMove.lean](ChosenMove.lean) checks four theorems in the same ordered source that implements funded appends.
The actual plan reservation at position 3 creates the pending row.
The actual funded seal at position 4 takes the source to the sealed image with that row committed and the matching ordered anchor.
With the stated funding and installation premises, the full chosen history installs the original window, appends once, reserves and seals the move, and installs the successor with the newly prepared window.
It preserves the exact original history and returns cut 1.
The successor reconciles the lost original append result and refuses changed bytes.
The final theorem requires that the destination grant names the exact prepaid extent in the plan.

## Amendments

[A273–A276](../amendments.md#study-70--2026-11-23) bind receipt survival, abort fencing, and final source authority to the durable decisions of the original parties.

## Acceptance coverage

- P07 and P115. The chosen-source program starts before the original append and reaches successor activation and exact result lookup under the stated custody and installation premises.
- P118. Recover the same move after a coordinator crashes with one receipt, finish its vector, and install without paying for that receipt twice.
- P119. Abort before a delayed prepare arrives, account for the hold it creates before the local fence, then close its exact scope and return its charge.
- P120. Refuse a decision based on only one of the two required receipts.

## Residue

The Lean ledger orders fresh physical versions using a monotone abstract ordinal.
A distributed issuer must refine that model using independent authenticated pool incarnation identities and exact immutable extent scopes.
The proof composes a shared-ledger linearization with a chosen-source acceptance program whose initial regional and source projections agree.
It uses a live pending source to construct the local claims.
The TLC model separately covers delayed local preparation after the source has aborted.
That branch still needs a general refinement that binds delayed admission, authenticated receipts, and exact settled custody across authorities.
The generalized installed receipt and complete dependency graph are premises of the chosen-source program.
The study leaves real ranked certificate formation, fault-dependent custody, and multi-move fairness open.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records the commands, configurations, checked theorems, and failing traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/70-distributed-preparation/run.py
```
