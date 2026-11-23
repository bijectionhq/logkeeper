# Study 38 report · Compose activation with its home handoff

2026-11-23

## Verdict

Freeze only the target's own state during a home move.
The source can durably learn a previously certified result and the original custodian can finish an authorized fence while the target cut is staged.
The successor inherits the exact target obligations and applies each external fact as a new ordered command.
A stale address can delay delivery of evidence without changing its binding or giving the predecessor authority to apply it.

## Bounded comparison

The same TLC model starts with one chosen activation result, a closed admission handle, and one outstanding copy plan.
It explores source receipt, custodian fence, copy of the sealed target cut, predecessor shutdown, cached routing, acknowledgment, exact settlement, and duplicate delivery.
The source and custodian commit separate durable facts in the model.
The custodian action represents an already authorized fence for the exact copy key.

| Owners | Distinct states | Checked result |
| --- | ---: | --- |
| 2 | 1,386 | Nine safety laws and both conditional progress properties hold. |
| 3 | 10,097 | Same laws hold across two owner changes. |

Safety covers exact result coverage, monotone source and provider evidence, stable completion, the original copy key, retired admission and issuance, current write authority, and discovery.
The temporal checks cover completing a staged cut and applying acquired external facts with weak fairness of install, publish, shutdown, refresh, acknowledgment, and settlement.
There are finitely many moves at either bound.

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A137 | `send_discharges` | Sending the reply loses the target's only retained result in one transition. |
| A145 | `restore_source` | Restoring the staged source view erases a durable result recorded after staging in five transitions. |
| A145 | `restore_provider` | Restoring the staged provider view erases a fence completed after staging in four transitions. |
| A146 | `ack_while_sealed` | Accept after staging and resurrect the discharged result on successor install in six transitions. |
| A146 | `settle_while_sealed` | Accept cleanup after staging and resurrect its plan on successor install in five transitions. |
| A146 | `apply_at_stale_revision` | Apply the acknowledgment through an obsolete owner revision in six transitions. |
| A146 | Stop refreshing after a stale delivery | The source and custodian have the required durable facts. After a cached endpoint stops, the client never refreshes and the current owner cannot discharge either obligation. |
| A135, A140 | `reset_issuance` | Inherit the target image without its issuance fence and readmit the retired handle in four transitions. |
| A147 | `duplicate_reopens` | Deliver the same result after acknowledgment and recreate the cleared target obligation in four transitions. |

Two acceptance witnesses stage a cut, then durably record the result and fence the original copy before installation.
They shut down the old endpoints, attempt delivery through a stopped cached endpoint, refresh to the successor, acknowledge the result, replay the exact source reply, and settle the copy.
The traces take thirteen transitions for one move and eighteen for two moves.

## General proofs

Lean checked fourteen theorems using standard axioms only. [Proof source](ActivationComposition.lean)
A composed trace projects to an actual trace of the Study 36 activation reducer and to the routing transitions of the Study 37 reducer.
The target image type carries the target fields alone.
Installing its exact image is a stuttering step at the logical activation layer after joining it with the current source record.
The proof checks that source intake from a delayed exact reply can take the original result-recording step or stutter when the source already recorded it.

Across arbitrary finite traces, an unrecorded chosen result retains its exact target record, an acknowledged result stays cleared, and a retired handle stays closed.
The source record and exact custodian fence each survive every subsequent move.
A physical plan retains its original binding until there is exact external fence evidence for it.
The acceptance theorem constructs source intake and custodian fencing during a staged cut, followed by installation, route publication and predecessor shutdown.
Both target obligations remain present at installation for the new owner to discharge.

Four Lean controls fail at the expected proof sites when restoration discards the source record, a mutation can use a stale owner, a mutation can cross the target seal, or changing a live copy plan needs no exact external fence.

## Remaining obligations

The routing projection uses the Study 37 owner and locator decisions.
The activation projection carries the obligation contents and issuance fence.
The proof assumes the Study 36 evidence premises, including authentic original physical settlement and a valid exact installation image.
It models one logical home and abstracts the durable source and provider state, transport and the target quorum.
The chosen map and previously sent reply relation record proof history. Physical retention uses the outstanding records, admission fences, and specific certificates still needed for recovery.
The activation-attempt gates and physical dispatch path still need refinement into this composition.
The Lean acceptance proof reaches a stopped predecessor with external evidence and retained obligations. The bounded witnesses apply those facts at the successor.
[Study 39](../39-certified-activation-replay/report.md) grounds original custodian evidence and checks ordered acknowledgment and cleanup under ranked quorum recovery.

Apply [A145–A147](../amendments.md#study-38--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner saves checker settings, traces, and Lean diagnostics in the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/38-activation-composition/run.py
```
