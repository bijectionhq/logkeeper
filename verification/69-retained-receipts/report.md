# Study 69 · Recover the exact retained append result after a move

2026-11-23

## Verdict

Retain the logical request identity and its original result with the committed range.
A successful chosen append supplies that identity and its ordered position.
A checkpoint that replaces the chosen append frame still carries or references the receipt while its LSN remains retained.
Reconciliation is an authorized lookup at the current certified source.
It preserves the stream history, accepts only the original binding, and returns the retention floor once the result has been trimmed.

## Bounded comparison

[RetainedReceipts.tla](RetainedReceipts.tla) models one chosen append with a lost reply, one source seal and successor activation, and two checkpoint selectors.
It distinguishes the old physical frame, the newer checkpoint's receipt metadata, and the logical retention floor.
TLC checked all three safety invariants across 17,433 distinct states.
The witness for both selectors, followed by successful lookup at the new base after reclaiming the old frame, takes nine transitions.

| Weakening | Shortest counterexample |
| --- | --- |
| Publish the new checkpoint without exact receipt identity | Choose the record and publish a second selectable basis. The new basis has no retained receipt in two transitions. |
| Match by LSN alone | Choose, seal, activate, and reconcile a different request at the occupied LSN. Four transitions. |
| Match by LSN and payload alone | A different grant or lineage at the same payload can use the prior result. Four transitions. |
| Reappend on reconciliation | Choose, seal, activate, and retry the exact request. History grows on lookup in four transitions. |
| Answer with the old result after trim | Choose and move, select a retained checkpoint, trim the original range, and serve the old receipt. Seven transitions. |

## General proofs

[ReceiptReplay.lean](ReceiptReplay.lean) checks eight theorems with standard axioms only.
The receipt book folds the actual applied results of the existing chosen reducer.
Only a successful append result installs a row.
Closing older receipt metadata at an earlier checkpoint preserves the exact final retained book because the logical trim floor is monotone.
Opening either certified selectable checkpoint gives the same final receipt view and lookup outcomes.
The lookup requires authorization, exact lineage and binding, and a position within the retained committed range.
For an authenticated lookup below that range, the result is the retention floor even when a stale physical row survives.
The Lean negative control reduces identity to LSN alone and fails the exact-binding proof.

[MoveProgram.lean](MoveProgram.lean) checks three constructive theorems with standard axioms only.
The funded append program from Study 68 creates the exact receipt row.
From a sealed source image carrying the retained row, applying an authenticated funded activation installs the new writer and window at the exact original cut.
The successor reports that cut and the original receipt and refuses changed bytes, with the original history unchanged.

## Amendments

[A269–A272](../amendments.md#study-69--2026-11-23) couple receipt identity to retained data, preserve it through checkpoint replay, and keep reconciliation scoped and read-only.

## Acceptance coverage

- P02 and P115. Recover a lost append result from either selectable checkpoint after the writer moves. The bounded witness includes reclaiming the physical command frame. The Lean program checks the exact funded append and successor activation under their stated funding and seal premises.
- P07. The checked activation reaches the new window with the same committed history and reports its next LSN. The complete distributed sequence from preparation through lost activation reply still needs composition.
- P116. Lookup at an occupied LSN with changed bytes, lineage, or original grant fails to confirm the original result.
- P117. After trim, a lookup reports the actual cut even if a stale row survives.

## Residue

The model binds logical identity by exact equality of lineage, original writer grant, starting LSN, and canonical payload.
Storage can represent these facts with an authenticated canonical commitment and a fixed-size retained metadata row.
Frame and checkpoint encoding, exact manifest retention, and charging those bytes against the existing log budgets still need refinement.
The lookup's authorization premise is supplied by a current authenticated read at the recovered scope.
The Lean move program starts from a certified sealed image and assumes original receipt and funding evidence.
Distributed preparation, recovery quorum reachability, and measured successor lookup latency remain open.
The bounded comparison covers one append and one move.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/69-retained-receipts/run.py
```
