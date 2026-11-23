# Study 106 · Recover the ordered AZ protection interval

2026-11-23

## Verdict

Order changes to the protection interval in the installed journal.
Name each interval by the lineage and chosen position of its establishing decision.
The current control image needs that position and one optional confirmed lost AZ.
A confirmation carries its exact interval and independent evidence.
A renewal carries proof of full coverage of the current acknowledged inputs, voters and custody.
The journal resets the allowance at the chosen renewal position.
Writer and voter changes carry the existing interval.
Recovery opens the selected control image and applies the complete chosen continuation with its inline evidence.

An interval identity is the stable name for a confirmed loss across voter changes.
A renewal proof has narrower reuse because it can become false whenever the committed dependencies or physical coverage change.
Keep the exact current-basis check when choosing renewal.
Give a fully prepared renewal a fair local turn.
Carry earlier repair evidence through intervening commits only when the reducer can establish that the exact new coverage still holds.

## Properties and comparisons

Lean 4.35.0 checked twelve theorems with standard axioms only.
`a_current_majority_and_its_crash_selector_recover_the_chosen_interval` composes ranked membership change, later quorum intersection, the current voter's precise journal, a certified checkpoint image and exact suffix media.
It applies to arbitrary finite frame lists and chains of ranked voter changes.
`replay_never_reuses_an_older_interval` proves the interval position never moves backward through any accepted history.
`renewal_never_reopens_an_old_incident_ticket` refuses an incident ticket from the earlier interval, and `a_replacement_can_use_the_original_incident_ticket` retains the prior ticket's validity across voter replacement within the same interval.
`chosen_renewal_lifts_to_full_coverage` connects an applied renewal to the prior study's quorum and data coverage law under the evidence-verification premise.
The Lean control removes the interval equality and fails at the proof of exact confirmation.

TLC 2.19 runs two finite models.
The interval model uses one initial confirmation, two selectable checkpoint cuts in the restart cases, one optional voter change, one optional custody change, and one renewal.
The traffic model allows repeated covered appends and adds one uncovered dependency in the safety cases.

| Weakening or alternative | Counterexample |
| --- | --- |
| Read an older checkpoint without applying the chosen confirmation | Crash and reopen at the old cut. The journal forgets the existing loss in two transitions. |
| Read an older checkpoint without applying the chosen renewal | Crash, reopen at the spent cut, then acknowledge new B-only work in the renewed interval. Three transitions. |
| Require live loss diagnosis on reopen | Crash after the confirmation is chosen. With the detector offline, serving can stall forever under weak fairness. |
| Reset protection on a voter replacement | Replace the voters after confirmation. The recovered authority forgets the loss in one transition. |
| Treat a previously authentic confirmation as current after renewal | Deliver the previous interval's ticket and acknowledge B-only work. Two transitions. |
| Use renewal evidence that ignores the frontier, voters or custody | Obtain a certificate, change the corresponding part of the basis, then renew. Three transitions each. |
| Invalidate every pending renewal on each covered append | With recurring covered appends, a fair renewal can be repeatedly disabled before it acts. Temporal counterexample. |
| Reuse repair evidence through an added uncovered obligation | Qualify the existing basis, acknowledge an additional B-only input, then renew using the old proof. Three transitions. |

| Reference case | Bounded evidence |
| --- | --- |
| Reopen confirmation with the detector offline | Eventual B-only acknowledgment in the existing confirmed interval under weak fairness, seven states. |
| Reopen through a replacement majority | The same conditional progress, 12 states. |
| Reopen a renewal through either crash-selectable base | Exact interval and acknowledgment invariants hold, five states. |
| Deliver an old confirmation after renewal | The request has no transition, one state. |
| Race renewal with acknowledgment, repair, custody and voters | Exact current-basis invariants hold, 66 states. A four-transition witness reaches acknowledgment, repair, certification and renewal. |
| Carry evidence through checked covered appends | Eventual renewal under weak fairness, six states. An uncovered append clears its eligibility, eight states in the safety check. |
| Reserve a local turn once renewal is fully ready | Eventual renewal under weak fairness, six states. |

## Amendments and acceptance programs

[A422–A427](../amendments.md#study-106--2026-11-23) specify checkpoint and suffix recovery, invariant interval identity across voter changes, current renewal evidence and local scheduling.
P213 records A's loss, replaces the voters, crashes to either root and serves on the recovered basis with the original detector offline.
P214 renews and recovers from an older spent root, then refuses the late confirmation and a new B-only acknowledgment.
P215 races repair certification with fresh dependencies and requires a fully ready renewal to receive a fair turn through covered traffic.
The programs add no RTDB caller operation.
They change the installed journal's control decisions and recovery obligations.

## Residue

The proof assumes exact historical verification relations, an authenticated checkpoint summary of its named cut, and exact mounted media for the installed basis.
It leaves provider evidence collection and stable authentication, canonical control framing, fixed-width exhaustion, atomic physical custody withdrawal and reserve sizing open.
[Study 107](../107-protection-handoff/report.md) treats transfer to a different group as a new placement of the same deployment lineage and adds the seal and installation rule.
A local ready turn requires either held support or exact revalidation before the decision.
The traffic model abstracts the duration and implementation of that turn and assumes stable quorum and custody.
The delta-based alternative needs a reducer proof that every intervening change preserves or reconstructs the required coverage.
Neither comparison establishes a throughput bound or unconditional renewal under churn that continually adds uncovered work.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/106-ordered-fault-interval/run.py
```

[run.py](run.py) saves configurations, counterexamples and proof diagnostics under .results/.
