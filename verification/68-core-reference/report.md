# Study 68 · Consolidate logical stream validity and acceptance

2026-11-23

## Verdict

The funded chosen-command reducer refines the original logical stream kernel for every replayed frame history.
Window decisions and refused commands can advance the ordered position while the logical stream stutters.
Successful logical transitions preserve bounded replay, certified trim, the committed history, and the terminal retirement fence.
The same reducer executes the checked writer and replay programs below.

## General proofs

[CoreReference.lean](CoreReference.lean) checks four theorems.
Each funded append, combined activation, window install or prune, and ordinary source decision projects to a permitted kernel transition or an unchanged logical stream.
This projection composes over arbitrary finite successfully replayed histories.
The existing kernel invariant then proves the recovery and retention bounds, the live replay floor, preservation of the committed prefix, and terminal retirement.

[CorePrograms.lean](CorePrograms.lean) checks six constructive theorems.
The writer program installs a certified funded window, appends the exact record, reads the original cut with a specific invocation, fences to a higher epoch, refuses a delayed older writer, records retirement, and refuses a later read.
The final closed stream retains the exact record and the ordered replies correlate to their original frames.
The replay program publishes a checkpoint, acquires a hold, refuses a trim across that hold, releases it, refuses delayed readmission, and trims the now unprotected range.
Its prefix also constructs the exact live-held state used by the countermodel.

## Mechanism checks

[Weakening.lean](Weakening.lean) checks five constructive countermodels in the same logical state space.
Each variant retains every original kernel transition and adds the indicated operation with only one guard removed.
The starting states come from the checked ordered programs, with enough capacity for their first append.
The original models refuse the operation at the same state.

| Mechanism and removed guard | Checked violation |
| --- | --- |
| M02, exact installed writer | The old writer appends at the correct head with both budgets available after the higher epoch. S03 fails. |
| M05, published checkpoint floor | Trim advances past the certified recovery basis without any live hold blocking it. The logical trim invariant for S06 fails. |
| M05, active replay floor | Trim crosses a live admitted read even with a correct published checkpoint. S06 and the logical part of S11 fail. |
| M08, recovery bound | With one record of recovery debt, the next append exceeds that bound while retained debt still fits. The recovery component of B01 fails. |
| M08, retained bound | The converse configuration exceeds retained debt while recovery debt still fits. The retention component of B01 fails. |

Lean reports fifteen theorems and only standard axioms across the three files.
The countermodels substantiate guard dependence within the logical kernel.
Changing all layers that enforce an end-to-end mechanism still requires a separate independence argument.

## Acceptance coverage

| Existing program | Checked part | Remaining evidence |
| --- | --- | --- |
| P01 | Install the certified window, append, and recover the exact retained record and read cut. | Actual writer election, quorum choice, and physical read-back in the deployed path. |
| P04 | Fence the writer and return the precise committed cut. A delayed old command at the valid head leaves the history unchanged. | Staging and delayed delivery under actual replicated authority. |
| P06 and P13 | Publish, hold, refuse unsafe trim, release, refuse delayed reuse, and trim. | Physical snapshot evidence, the stale-cursor response with its floor, and carrying the permit across a distributed move. |
| P08 | Record terminal retirement and refuse a later invocation. The retirement fence survives every successfully replayed continuation. | Establish custody and exact provider disposition of the interrupted copy in the same end-to-end program. |

## Amendment

[A268](../amendments.md#study-68--2026-11-23) records why the recovery and retained bounds and the two trim guards remain individually necessary in the logical reference.

## Residue

The constructive append program assumes the original installed writer, authenticated funding, and enough room for one append.
The frame interpreter consumes exact attributed chosen input from the existing consensus and recovery refinements.
This study proves validity over the logical projection and part of the required expressiveness and independence.
Physical custody, resource limits outside the logical stream, full failure and recovery programs, and the remaining mechanism-independence cases still need evidence in the consolidated reference.

## Reproduction

Use Python 3.13.15 and Lean 4.35.0.
The runner records commands and results below `.results/`.

```sh
LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/68-core-reference/run.py
```
