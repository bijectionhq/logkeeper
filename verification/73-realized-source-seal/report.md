# Study 73 · Bind a source move to the exact pool-issued extents

2026-11-23

## Verdict

Order the exact logical plan before collecting preparations.
The complete receipt vector resolves each planned scope to its original paid physical extent.
The source chooses that vector and seals the old writer at one ordered position.
A retry, successor, or replay uses those original bindings even if the old pool routes have changed.

Use a source-scoped window identity ordered by activation position.
Bind that identity to the exact physical append extent in the sealed vector.
Pool-issued physical identities supply exact equality for custody, while ordered source positions supply writer-window succession.

Once the certified successor has installed the exact cut, recovery cleanup uses the original move anchor, physical pool incarnation, local serial, custody key, and immutable binding.
It can return an exact recovery charge after verified stable absence.
The serving append window retains its charge and has its own disposition path.

## Bounded comparison

[RealizedMove.tla](RealizedMove.tla) checks one move with two required extents and an independent disposition at a third pool.
It includes alternative charged scopes at the same price, a route change before recovery, and a successor physical serial of 1 with an earlier source window alias of 9.
TLC checked all four invariants and the fair installation property in separate baselines of 40 distinct states each.
The temporal check uses weak fairness for sealing the exact vector and applying its continuously eligible installation.
The six-transition witness chooses the seal, loses its original route, recovers the same vector, installs, and settles only the recovery allocation.

| Weakening | Counterexample |
| --- | --- |
| Accept only pointwise byte totals | A charged receipt for an unrelated scope at the same pool and price can be chosen in one transition. |
| Resolve the vector again at recovery | Choose, change routes, and replay using the replacement receipt lookup. The recovered vector differs in three transitions. |
| Compare only the local serial during cleanup | Evidence for the same serial at a third pool returns the original recovery allocation's charge. Four transitions. |
| Allow recovery cleanup for the append role | After installation, exact disposal of the append extent becomes admissible and returns the active window's backing. Four transitions. |
| Use the physical serial as the window order | The source seals, but an eligible installed successor can never publish physical serial 1 after window 9. TLC finds a fair execution stuck at the seal. |

## General proofs

[AllocationVector.lean](AllocationVector.lean) checks five theorems.
A successful actual local preparation yields its exact registered, charged receipt.
The complete vector lists the original scopes and roles with no duplicate physical identity.
Its exact demands supply the previous reducer's pointwise funding requirements.
Equal prices do not permit a different scope.

[RealizedSource.lean](RealizedSource.lean) checks eight theorems.
The actual accepted source reservation retains the exact plan.
The seal uses that plan and adds the exact vector and anchor to the accepted source decision at the same position.
An exact installation supplies the source-scoped alias while preserving the chosen append extent.
A different installed vector is refused.
Exact cleanup for the activated record reaches the existing local refund rule only with the original pool, key, binding, and stable absence.
The append extent and every other physical row remain untouched by that refund.
The Lean negative control removes the realized vector comparison at installation and fails the replay refusal proof.

[RealizedProgram.lean](RealizedProgram.lean) checks three theorems.
Two independently eligible pool ledgers produce the exact paid vector.
The program then reserves the plan, seals on those receipts, and activates logical window 10 using pool 2's physical serial 1.
It uses the same chosen source reducer to replay the earlier append and the move.
Replay recovers the original append receipt and the same committed history.

## Amendments

[A285–A289](../amendments.md#study-73--2026-11-23) bind realization to the chosen plan, separate source ordering from physical identity, and restrict cleanup to the original recorded recovery obligation.

## Acceptance coverage

- P127. Replace one exact prepared scope with another of the same price. Refuse the seal.
- P128. Recover the original realized vector after its lookup route changes. Activate the successor against its original writer history and recover the original append result.
- P129. Activate a newer source window backed by a lower physical serial.
- P130. Reject same-serial evidence from another pool and recovery cleanup of the append window. Apply a verified exact cleanup to the named recovery row only.

## Residue

The source proof projects the augmented plan and seal to the existing ordered source reducer and checks the recovered binding over the original record.
It assumes the ordered source checkpoint or suffix authenticates that full record.
Canonical command, checkpoint, and signature encoding still needs refinement, including compatibility of this typed source window identity with the older numeric window book.
The projected pointwise funding check assumes authenticated receipts from the real original pools, and activation assumes a certified installation of the exact cut and vector.
The cleanup theorem verifies exact local disposition and refund from an activated record.
It leaves provider effect admission, continuing replay dependency transfer under faults, and source compaction after all participant scopes settle to their adapter and composition proofs.
The proof does not establish progress for repeatedly moving pools with competing installations.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records exact commands, configurations, theorem checks, and traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/73-realized-source-seal/run.py
```
