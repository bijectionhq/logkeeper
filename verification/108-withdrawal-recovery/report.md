# Study 108 · Recover copy withdrawal without re-admitting its bytes

2026-11-23

## Verdict

Use the original allocation's durable custody phase to represent withdrawal.
One chosen change closes fresh holds, excludes the version from recoverable coverage, and authorizes its exact provider effect.
Require release of every exact root reference and independent borrow before that change.
The exact dispatched effect can run while the original custodian is down.
The charge remains until the custodian orders settlement against authenticated stable absence for the same physical version.

Recovery replays the chosen phase and references from either selectable image.
A pending deletion and a live copy can both leave bytes physically present.
A storage scan therefore cannot tell which bytes remain eligible as witnesses.
Using the original row keeps eligibility and effect authorization in the same recovery decision.

## General proofs

Lean 4.35.0 checked thirteen theorems with standard axioms only.
`each_accepted_frame_preserves_custody_and_zone_coverage` composes the existing shared root and borrow rules with the AZ protection rule.
`interleaved_provider_effects_preserve_physical_backing` proves that arbitrary finite interleavings of chosen custody updates and exact authorized provider effects preserve the backing of every open version.
`an_acknowledged_input_has_a_surviving_backed_version_after_interleaved_effects` derives a physically backed copy in a surviving AZ for each configured loss case.
`either_exact_checkpoint_recovers_the_chosen_withdrawal_state` applies the existing crash-selector and suffix theorem to that custody reducer.
`a_delayed_exact_settlement_stays_absent` composes original-version matching with the provider's existing stable-absence rule.
The proof control omits the receipt's exact physical version comparison and fails at the law requiring it.

## Bounded comparison

TLC 2.19 checks two custody checkpoint choices, three AZs, one acknowledged input, separate root, read and delivery holds, and at most one custodian crash.
The ordinary-read scenario starts with one old root hold and one live physical read. It has no exact delivery hold.

| Weakened design | Counterexample |
| --- | --- |
| Consider only the visible checkpoint | Erase A while the older selectable root still needs it in six transitions. |
| Ignore only an ordinary physical read | Release the old root and erase A while the physical read still has a hold. `ExactHolds` fails in five transitions. |
| Treat the delivery as released once the ordinary read closes | Erase A despite the outstanding delivery in six transitions. |
| Dispatch from staging | A provider deletes A in four transitions without a chosen withdrawal. |
| Reopen the earlier image without its chosen suffix | The recovered authority has the wrong phase in seven transitions. |
| Recount a copy because a provider scan still finds its bytes | Authorize A and dispatch, crash, count A from the scan, authorize C, apply both effects, then lose B. Twelve transitions. |
| Settle on a probe | Return the original charge in five transitions without proven fenced absence. |
| Require the original authority online during the effect | A dispatched effect and subsequent settlement can stall despite fair service and a working provider. |

| Reference case | Bounded evidence |
| --- | --- |
| Recover pending A and check a competing withdrawal and loss of B | All five invariants hold in 440 states. |
| Execute A during a custodian outage, recover and settle | Eventual settlement under weak fairness in 130 states. |
| Keep a paid delivery when the other holds release | Withdrawal stays unavailable in five states. |
| Normal verified terminal settlement | Eventual settlement under weak fairness in 82 states. |
| Competing staging before authority is chosen | The safety invariants hold in 92 states. |
| Ordinary physical read stays protected | The invariants hold in 15 states. A six-transition witness finishes the read and deletes the old copy. |

The older and newer crash selectors each reach deletion during the outage and settlement after recovery.
Their shortest witnesses take ten and eleven transitions respectively.
The temporal cases assume eventual completion of the relevant exact holds, a reachable provider that can close writes, and fair service through recovery.

## Amendments and acceptance

[A434–A439](../amendments.md#study-108--2026-11-23) set the original custody phase and state the remaining provider and accounting requirements.
P220 covers refusing competing removal while the old exact effect remains pending, even after crash.
P221 covers independent hold release and exclusion of staging.
P222 covers offline effect execution and exact stable settlement.

## Residue

The common proof models complete registered uses, exact immutable version IDs, the existing provider closure contract and a fixed acknowledged input set and fault envelope.
It abstracts the concrete registration across authorities, the canonical bytes for each named custody checkpoint, the provider token and fence implementation, and allocation-row collection under a real capacity bound.
The pure reducer leaves existing open identities unchanged or closes them.
Registering replacement versions and changing the required-input set or fault envelope need a joint proof with the withdrawal state.
The modeled provider effect uses the same original identity as the recovered authority.
That agreement still needs to be demonstrated against the actual storage adapters.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/108-withdrawal-recovery/run.py
```

[run.py](run.py) saves the TLC configurations and traces and the Lean proof-control diagnostics under .results/.
