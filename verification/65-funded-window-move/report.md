# Study 65 · Install the move using its already charged window

2026-11-23

## Verdict

Prepare a move as a set of exact owned extents in the shared pool ledger.
Derive the numeric need at each pool from those extents.
The source seals against the complete vector, and the destination can publish its exact prepared append window with unchanged pool occupancy.
Old readers keep their original physical backing.
The fresh append allocation is separate from every extent that stores the recovered image, so its initial offset zero preserves the image.

## Bounded comparison

[FundedWindowMove.tla](FundedWindowMove.tla) models two pools, two competing moves, one ordinary unit per pool, and a live predecessor borrow.
Each move needs two exact one-unit extents, one in each pool.
The model abstracts authenticated receipts as exact scope checks and abstracts fenced physical absence as an atomic disposition step.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Capacity two per pool | 318 | All five safety invariants hold. |
| Capacity three per pool | 780 | The same laws hold with room for greater overlap between moves and ordinary traffic. |
| Require a second capacity purchase at installation | 260 | Safety holds, and the full-pool installation program is excluded. |

| Weakening | Shortest counterexample |
| --- | --- |
| Seal on a partial vector | Prepare one pool and seal before the second pool has its extent. Two transitions. |
| Substitute other moves' paid extents | Prepare enough bytes at both pools under other ownership, then seal with the wrong vector. Three transitions. |
| Substitute the window by pool | Prepare and seal the correct move but install another extent from the right pool. Four transitions. |
| Return the predecessor charge on installation | Install the replacement while a predecessor borrower still holds the old bytes, returning their debit early. Four transitions. |
| Use recovered-image space as the fresh window | Prepare and seal, then choose the recovered image's physical extent for fresh appends at offset zero. Four transitions. |

## General proofs

[FundedWindowMove.lean](FundedWindowMove.lean) checks thirteen theorems with standard axioms only.
Each extent belongs to its original stream and move key, and an active claim keeps its exact debit in the existing pool ledger.
An arbitrary finite trace of the modeled competing moves and appends preserves the existing regional stream, pool, and window invariants.
Before its exact terminal result, a prepared claim stays held.

The charged extent list determines each receipt's numeric component.
The exact source plan, its admitted receipts, and the existing ordered seal reducer bind the original move at its exact seal position.
The destination uses the existing activation reducer and its exact anchor, then derives the window grant's paid premise from the existing debit.
Installation retains the original debit list and preserves pointwise usage even at the capacity limit.
A live predecessor borrow remains backed.
For any independently owned old borrow and complete replacement vector, the combined exact charges fit each pool alongside ordinary occupancy.
The two Lean negative controls remove move ownership and allow settlement before its exact terminal decision.

## Amendments

[A253–A257](../amendments.md#study-65--2026-11-23) connect the exact prepared vector to source sealing, destination installation, and the existing pool and custody ledger.

## Acceptance programs

- P105. Starting with a live old borrow, prepare both pools, seal, and install at full serving-pool capacity. TLC finds a four-transition trace. Lean constructs the installation with the exact admitted activation and window premises even when the pool is full.
- P106. Prepare an incomplete vector or supply equally sized charges from the wrong move. Refuse seal or destination substitution while preserving existing custody.
- P107. Install a replacement with a fresh append window and a nonempty recovered image. The chosen window is disjoint from all image extents, so its initial append space remains independently usable.

## Residue

The Lean model takes exact immutable allocation ownership and trustworthy participant receipt checks as premises.
It assumes the existing activation predicate certifies the complete durable ranked image and that ready destination storage binds the designated physical range.
The move wrapper models activation and window publication together at the activation decision.
The exact frame and checkpoint refinement still needs to encode this combined decision and its complete custody state.
The one-pool claimant interface still needs a refinement from authenticated placement and storage operations, including repeated authority changes and stable disposition.
Several roles may use disjoint charged ranges in a common preallocated workspace.
Measured sizes and the complete dependency enumeration determine the production vector.
The full-pool witness is a feasible program under its premises, with no fairness or latency result for preparing the vector under contention.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/65-funded-window-move/run.py
```
