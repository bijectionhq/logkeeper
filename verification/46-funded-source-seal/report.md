# Study 46 · Decide the funded seal at the source

2026-11-23

## Verdict

The pool coordinator cannot promise irrevocable use of a vector independently of the source's seal.
The split design can bind both pools, then let the source retire before it has produced any seal.
The retired source cannot seal, and the irreversible bind authorizes neither install nor release.
Moving the vector commitment into the ordered source seal eliminates that intermediate outcome.

The pools reserve capacity provisionally before the decision.
When retirement wins, the source records the outstanding move's exact abort with terminal closure and returns the receipt before pool reconciliation.
When seal wins, the installed successor can order retirement and the old seal remains binding.
Exact prepared receipts stay backed until their own abort can take effect, so the source can use them during pool controller changes.

## Properties and comparison

[FundedSeal.tla](FundedSeal.tla) models two unit components of a move vector against a capacity of two units per pool.
An ordinary unit or an acquired hold consumes one of those units.
The model has one stream, one outstanding move decision at a time, up to two successive exact attempts, and independent controller transfers for both pools.
Pool transfer preserves exact local charges and refusal state by the contract from Study 45.
Target installation treats certified readiness as available.
The temporal cases give weak fairness to eligible retirement, installation, replacement of a sealed pool controller, and local abort application.

| Candidate or case | Distinct states | Result |
| --- | ---: | --- |
| Independent irreversible binding, then source seal | Shortest witness in eight transitions | A terminal source can strand the commitment. |
| Source-ordered seal, one attempt and two moving pools | 6,877 | Five safety and three temporal laws hold up to the bound. |
| Source-ordered seal, two attempts and fixed pools | 9,332 | Same laws hold up to the bound. |
| Source-ordered seal, two attempts and two moving pools | 115,977 | Five safety laws hold up to the bound. |

The safety laws cover pointwise usage, retained exact vectors, closed local keys, absence of stranded terminal commitments, and disposition of outstanding plans at retirement.
The temporal laws require pending retirement to complete, chosen aborts to close both local keys, and a funded seal to install under the stated readiness and fairness.
Fresh preparation is subject to available capacity.
Retiring after the seal depends on the successor installing under those premises.

| TLC weakening | Shortest safety counterexample or temporal trace |
| --- | --- |
| Bind before the source decision | Request retirement, prepare both pools, bind externally, and retire before seal. The vector is stranded in eight transitions. |
| Accept a partial vector | Prepare one pool and issue its receipt, then seal in four transitions. |
| Borrow a previous vector | Obtain both receipts for the first attempt, abort it, and seal a second attempt using the first receipts in eight transitions. |
| Drop the outstanding plan at retirement | Plan, request retirement, and retire without recording abort in three transitions. |
| Treat a retirement request as authority to return a committed hold | Seal and release one component against the retirement request in eight transitions. |
| Reopen a canceled key | Abort, fence a local key, and reacquire it in four transitions. |
| Require another source reply for installation | Seal, lose source access, and stutter while installation is disabled. |

[FundedSeal.lean](FundedSeal.lean) checks twelve theorems using standard axioms only.
The source lifecycle projects onto arbitrary finite traces of the reference stream kernel.
Seal and abort outcomes persist across later choices, including activation and retirement.
A complete exact vector can freeze the source and move its existing charges between accounting categories with the same usage in every pool.
Retiring an active source yields its outstanding attempt's exact abort without any premise of pool availability.
The issued-receipt model proves across arbitrary finite traces that each pool keeps a receipt backed while its exact abort is unavailable, and that a pending source intent can validate the complete vector from those receipts.
The two Lean negative controls reject a target-only receipt match and returning a hold without exact source abort evidence.

## Amendments

[A176–A179](../amendments.md#study-46--2026-11-23) couple irreversible commitment with source seal, keep receipt identity and funding exact, settle pre-seal retirement with exact abort, and allow installation from the existing certificate during source loss.
Provisional receipt collection can run independently of the source ordering decision.
Participants can apply the outcome asynchronously while the reserved debit remains charged.

## Acceptance programs

- P49. Partially prepare one pool while a controller changes. Retire at the source, install the replacement controller, close both local keys, and refuse the delayed prepare. TLC reaches this in nine transitions.
- P50. Fund both components, fill the remaining capacity with ordinary work, seal, lose source access, and install and retire at the target. The vector stays charged through retirement. TLC reaches this in twelve transitions.
- P51. Abort the first attempt, fence both of its keys, and fund and seal a fresh attempt. TLC reaches this in ten transitions. The separate stale-receipt control shows why the prior vector cannot be substituted.

## Residue

The local controller change in the Lean model abstracts exact pool-ledger replacement.
Authentication and the relationship between issued receipts and charged physical bytes still depend on the pool and provider refinements.
The outcome table denotes exact history in the reference.
The production design still needs a bounded representation and recovery rules for settled outcomes that can be forgotten and exact evidence still owed to participants.
The finite model distinguishes terminal retirement from release of physical custody. It leaves final disposal to the earlier physical settlement contract.
The progress proof for a funded seal is bounded and assumes the certified cut and target remain usable.
The findings leave the wider common-reference validity, expressiveness, and independence obligations open.

## Reproduction

Run from the Logkeeper repository with Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner records every configured case and diagnostic in `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/46-funded-source-seal/run.py
```
