# Study 66 · Recover the funded move with independent custody

2026-11-23

## Verdict

Choose the destination writer and its exact prepaid window in one ordered activation.
Replay that decision from the selected source checkpoint using the original authenticated installation and funding evidence.
The source replay restores only that stream's state and window rows.
Each pool retains its own recovered custody state, including independently settled workspace, and each neighboring stream retains its current cursor.
Opening fresh service verifies the newly recovered window against current physical custody.

## Bounded comparison

[MoveRecovery.tla](MoveRecovery.tla) models a single chosen activation, two selectable source bases, a destination window, separate workspace, a predecessor borrow, and up to two neighbor cursor advances.
Workspace settlement is an independent exact terminal action in this comparison.
TLC checked all six safety invariants across 3,476 distinct states.

| Weakening | Shortest counterexample |
| --- | --- |
| Publish a bare activation | Choose activation and apply the destination writer while the logical window still identifies the predecessor. Two transitions. |
| Requote an earlier installation | Choose and apply, settle its workspace, then replay from the old source checkpoint against the current pool. The original success is lost in four transitions. |
| Restore custody from the source | Choose and apply, settle the workspace, then reopen an older source image and recreate the settled charge. Four transitions. |
| Replace the neighboring cursor | Choose, advance the neighbor, and reopen the source's old book. The neighbor's cursor regresses in three transitions. |
| Admit service on historical evidence | Choose and apply, lose current pool eligibility, and serve on the old evidence. Four transitions. |

## General proofs

[MoveRecovery.lean](MoveRecovery.lean) checks eleven theorems with standard axioms only.
The funded activation is a command in the chosen replay machine.
The legacy activation path refuses without changing writer or window.
The scoped command checks the exact original plan and window, and missing historical authority refuses both effects.
For an admitted live move with the original authenticated attachments, the combined replay decision produces the same source state and window book as the funded regional move at the same ordered position.

The exact chosen replay theorem establishes equivalent source results from either selectable checkpoint.
The regional merge preserves every other stream's state, cursor, and window rows, and leaves the current pool, outstanding claims, recorded installation evidence, and old borrows intact.
With the explicit final backing and source validity conditions, this merge preserves the previous regional ledger invariants.
The authentic installation receipt can authorize settlement of only its own still-held claim and does not itself return capacity.
A delayed receipt cannot create a new claim after that key has cleared.
Fresh service requires the current physical debit, current pool eligibility, and the exact installed window.
The two Lean controls independently remove the original window binding and the current backing check.

## Amendments

[A258–A262](../amendments.md#study-66--2026-11-23) bind writer and window at activation, distinguish historical replay from admission, and preserve the scopes of pool and stream recovery.

## Acceptance programs

- P108. Choose and apply activation, keep two source bases selectable, settle the original workspace, and advance a neighboring stream. Recover both bases after settlement while the predecessor borrow remains live. TLC reaches this in seven transitions.
- P109. Restore one stream after another stream has consumed additional window ranges. Preserve the neighbor's cursor and each independent pool obligation. A delayed authenticated installation receipt for a fully settled move is refused.
- P110. Recover the exact historical activation, then refuse fresh service when current custody or pool eligibility is absent. Historical recovery retains its exact prior result.

## Residue

The source attachment verifier still needs authenticated encoding of the exact applied frame, its cut and non-reused lineage, the immutable plan, and its original custody receipts.
The model's physical readiness predicate covers the current append window. Whole-service readiness still requires each exact recovery dependency under the existing joint coverage contract.
The pool-facing receipt intake checks an already authenticated applied result. The provider journal must make that intake durable and compact its evidence once independent closure is recoverable.
The regional merge uses the current scoped state as its input. Production must serialize publication with conflicting changes to the recovered stream and validate the live pool scope at admission.
No unbounded temporal progress or production storage behavior is inferred from the finite comparison.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/66-move-recovery/run.py
```
