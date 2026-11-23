# Study 49 · Order funded moves and settlement in one source history

2026-11-23

## Verdict

The source applies its authority change and exact reserved result at one command position.
An acknowledgment carries its exact evidence in that command.
Recovery can then reproduce both state and replies from the chosen prefix without contacting participants.

A seal anchors the exact funded decision at its command position.
Several commands can leave the data LSN unchanged, so that LSN is insufficient to identify the seal.
The checkpoint used to trim the journal must carry both the stream state and source result book at the same ordered position.

## Properties and comparison

[UnifiedHistory.tla](UnifiedHistory.tla) models one stream and one reservation.
It separates chosen commands and reference outcomes, a lagging learner, participant evidence availability, and the replaying successor.
The data LSN is constant across the finite model's control commands.
The proof field abstracts authentication of each attachment.

| Case | Chosen command bound | Distinct states | Checked result |
| --- | ---: | ---: | --- |
| Unified exact replay | 4 | 2,947 | Exact recovered state and outcomes, authority and result consistency, and eventual recovery hold up to the bound. |
| Unified exact replay | 6 | 23,777 | Same laws hold up to the bound. |

The temporal cases give weak fairness to starting recovery, applying the next retained command, and publishing the completed state.
The successor has the exact retained command sequence.
Ranked agreement and installed quorum coverage are separate Lean premises.

| TLC weakening | Shortest safety counterexample or temporal result |
| --- | --- |
| Copy the learner | Choose a command, close while the learner lags, and install its old state in three transitions. |
| Reread evidence | Choose a successful acknowledgment, disconnect the participant, and replay it as a refusal in ten transitions. |
| Enrich earlier commands with late evidence | Choose a refusal, then receive the evidence and replay that refusal as success in ten transitions. |
| Freeze authority without its result | Replay a funded seal with the writer fenced and its reserved result still planned in eight transitions. |
| Install using the data LSN only | Replay an installation of the wrong seal position as successful in ten transitions. |
| Require a live participant call to recover | Close and disconnect. Even a recoverable cut can fail to install indefinitely. |

## General proofs

[UnifiedSource.lean](UnifiedSource.lean) checks eleven reported theorems using standard axioms only.
The ordered reducer combines routine stream commands, move reservation, the funded seal, abort or retirement, exact installation, participant acknowledgment, and result compaction.
Routine dispatch enumerates the allowed commands and excludes the lifecycle operations that need unified admission.
Every command and arbitrary finite replay project to the reference stream kernel.

A successful funded seal records its authority and reserved result in one transition.
A successful prepared retirement does the same for its exact abort.
The installation guard checks the original decision and its seal position.
The composed acknowledgment uses the settlement certificate interpretation from Study 48, with its exact result and binding checks at the current row.

Given a joint checkpoint equal to the certified prefix result, replaying its suffix gives the same state and suffix replies as replaying the whole history.
The ranked theorem proves that any current recovery majority contains an installed exact copy whose history extends the older chosen prefix.
The original ordered replies remain a prefix of the recovered replies across arbitrary finite membership changes.
The two Lean controls reject substituting an unattached receipt and omitting the ordered seal position.

## Amendments

[A188–A191](../amendments.md#study-49--2026-11-23) require joint application, attached evidence, certified joint checkpoint recovery, and command-position binding for installation.

## Acceptance programs

- P56. Choose a plan, retire with its exact abort, acknowledge, and compact while the learner has yet to apply the history. Recover with the participant disconnected. TLC reaches a retired stream with the source result closed in thirteen transitions.
- P57. Choose an acknowledgment without evidence. Make evidence available later, then recover while disconnected and preserve the previously ordered refusal. TLC reaches this in eleven transitions.
- P58. With the data frontier unchanged, reject an install certificate addressed to a position other than the ordered seal. The bounded negative control and the general Lean guard theorem check the distinction.

## Residue

The abstract rules verify immutable proof values.
They assume canonical certificate encoding, certificate availability for the retained tail, and the binding between a proof's anchor and the complete certified lineage.
The checkpoint theorem reasons about exact reference state, including logical history. It does not establish a bounded physical encoding of that state.
The model has one outstanding move and abstracts the actual number of physical obligations.
Multi-intent byte accounting, production effect boundaries, and the common checkpoint's physical custody and trim protocol remain to be composed.

## Reproduction

Run from Logkeeper with Python 3.13, Java 21.0.13+9, TLC 2.19 and Lean 4.35.0.
The runner saves configurations, traces and Lean diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/49-unified-source-history/run.py
```
