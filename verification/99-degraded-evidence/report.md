# Study 99 · Diagnose a failure or choose an exclusion

2026-11-23

## Verdict

Study 67's degraded admission assumes that the owner has correctly identified an existing AZ loss.
Two replies can establish a surviving quorum in a current three-voter family when the third AZ is either slow or unreachable.
Without an independent observation, those replies cannot distinguish the worlds.
Requiring certainty of physical failure from those replies can indefinitely block degraded admission even when the installed quorum and all necessary recovery inputs are reachable.

One candidate is to order an explicit operating mode at the current installed authority.
An approved exclusion certifies the responding quorum and exact current recoverable dependencies outside the excluded domain.
It spends the current interval's allowance and reports degraded protection.
It asserts no physical failure.
This requires agreement on whether deliberate exclusion may consume the allowance, how previously acknowledged protection survives exclusion, and how a verified repair renews it.
Keep the fault interval and healthy renewal conditions from the existing design.

## Evidence

Lean 4.35.0 checked two theorems with standard axioms only.
`identical_observations_do_not_decide_actual_failure` proves that a deterministic decision based on equal observations cannot guarantee both true physical diagnosis and admission on actual failure for that pair.
The control weakens sound diagnosis and the impossibility proof fails.
`a_decision_about_exclusion_depends_on_its_own_evidence` verifies the conjunction of policy approval and readiness in the candidate decision.

TLC 2.19 used a fixed current owner, one eligibility decision, one admission, and weak fairness of enabled actions.
The comparisons keep the two responding voters fixed, with exact recovery inputs present unless removed by a control.

| Policy and world | Result |
| --- | --- |
| Infer full physical failure from the timeout when the AZ is slow | False diagnosis in one transition. |
| Infer full physical failure and happen to guess correctly in the failed case | Three states pass. This success has the same observations as the false diagnosis. |
| Wait for independent confirmation when none is available and the AZ is unreachable | Temporal counterexample. |
| Use explicitly authorized exclusion in either world | Three states pass in each case, including admission. |
| Use exclusion without policy approval | Admission remains unavailable, as expected. |
| Ignore exact recovery inputs in the authorized candidate | Admission without the required inputs in two transitions. |

## Acceptance and limits

Under the existing desired offline dependency boundary, a funded installed group should continue when its verified survivors suffice.
The comparison shows why requiring an external service to confirm physical failure would add another availability premise.
The bounded candidate checks only the shape of a decision at one fixed scope.
A full refinement must serialize the operating-mode transition, bind it to the lineage and recovery cut, preserve existing acknowledged durability, refuse swapping the excluded AZ before requalification, and recover the mode through leader and voter changes.
A distinct power-loss fault or more than one excluded AZ is outside this study.
Agree the protection semantics before adopting the candidate.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/99-degraded-evidence/run.py
```

[run.py](run.py) records commands, configurations, counterexamples and proof diagnostics under .results/.
