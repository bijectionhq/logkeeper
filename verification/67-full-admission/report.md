# Study 67 · Verify complete admission within the remaining AZ fault allowance

2026-11-23

## Verdict

Fresh admission requires the exact recovered source and its current paid window, the installed voter family, and every dependency of every still-selectable checkpoint and suffix.
The quorum and dependency checks use the same failure case.
For a known single-AZ outage, the admissible case is that existing loss.
Healthy admission covers each possible single-AZ loss, and a return to the healthy mode requires verified protection again.
Counting a second AZ loss as part of the first outage blocks the intended three-voter service even when both survivors and every required input remain available.

## Bounded comparison

[FullAdmission.tla](FullAdmission.tla) models three AZs, one voter in each AZ, seven typed input identities, and independent copies for the old tail, new tail, and activation attachment.
It explores checkpoint selection, scope replacement, missing inputs, a single AZ fault, revalidation, and healthy renewal.
The active append window occupies a specific AZ.

| Case | Distinct states | Result |
| --- | ---: | --- |
| One-AZ envelope | 3,126 | Both safety invariants hold. Fresh admission reaches the known-outage case in three transitions. |
| Require another possible AZ loss during the first | 1,722 | Safety holds. Fresh admission during the outage is excluded. |
| Stable outage with both survivors and all required inputs | 4 | Under weak fairness of the fault, observation, and admission actions, the finite run admits fresh work. The extra-fault guard produces a temporal counterexample in the same scenario. |

| Safety weakening | Shortest counterexample |
| --- | --- |
| Check the window alone | Lose a required input, observe the healthy window, and admit. Three transitions. |
| Check only the visible selector | Publish a new view, lose the stable view's old-only input, observe, and admit. Four transitions. |
| Omit the activation attachment | Lose the attachment and admit using the incomplete dependency set. Three transitions. |
| Reuse an old scope | Observe, change the installed scope, and admit with the original stamp. Three transitions. |
| Clear degradation before restoring protection | Lose an AZ and renew healthy mode without the required full evidence. Two transitions. |

## General proofs

[FullAdmission.lean](FullAdmission.lean) checks eleven theorems with standard axioms only.
The fresh append proposal binds its exact stream, next ordered position, and current paid window.
The successful gate establishes the current scope, replayed logical cut, window health, distinct installed voters, and availability of every selectable input for each permitted failure case.
Any available majority intersects the installation quorum at an exact-basis donor.
The other inputs have independently eligible exact allocations with live registered custody and actual debit entries in the shared ledger.
The proof uses the same failure for the quorum and every dependency, including source activation attachments.

The current window must be outside the already failed domain.
The degraded guard requires coverage for that existing failure, and the healthy renewal guard requires all single-failure cases.
In Lean, two survivors out of three form a majority while the extra-fault comparison has only one voter and fails.
The two negative controls remove the current scope match and reset the allowed faults during degraded operation.

## Amendments

[A263–A267](../amendments.md#study-67--2026-11-23) establish the full current admission scope and preserve the remaining fault allowance.

## Acceptance programs

- P111. Preserve both selectable paths while the selector is unresolved. Refuse a fresh append when the old-only tail input or an original activation attachment is absent.
- P112. Lose one AZ while two installed voters, the active window, and every input remain available in surviving custody. Admit fresh work. The finite program checks eventual admission under the stated stable-scope fairness assumptions.
- P113. Present an observation for a prior voter, selector, or custody scope. Refuse its use for the current operation.
- P114. Renew healthy mode only when every single-AZ failure case again has complete exact support.

## Residue

The model requires trustworthy identification of the existing AZ failure, non-reused scope revisions, authenticated exact image and membership binding, and complete enumeration of selector and tail dependencies.
The admission proof applies at its decision boundary. Continued execution relies on the existing fencing and custody contracts, and actual failures can still interrupt I/O.
A running implementation can use a preverified scope and durable holds. It must make scope invalidation and current admission agree, including across custody changes.
The stable-outage model holds the admissible scope and surviving inputs fixed. Election, diagnosis, window relocation, repeated outage recovery, latency, and general liveness still need wider evidence.
The degraded guarantee lasts while that identified outage defines the current scope.
A loss in another AZ before full protection is reverified requires a new readiness decision and may make service unavailable.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/67-full-admission/run.py
```
