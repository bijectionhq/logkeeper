# Study 75 · Replay one realized source history from either checkpoint

2026-11-23

## Verdict

Rank the complete source frame, including its original realization, evidence, and physical binding.
Authenticate the entire selected source image at its actual ordered cut.
Replay the exact chosen suffix against that image.
The resulting state includes the same writer, current and retained window bindings, retained append receipts, plans, realized seals, and outstanding source outcomes from every selectable base.

Pool and target acknowledgment settle their recorded obligations.
The handoff itself independently needs the realized vector until the source applies its ordered activation.
A source can receive complete acknowledgments before it has applied that activation.
Compaction must preserve a live handoff even when every participant has acknowledged.

## Bounded comparison

[JointRealized.tla](JointRealized.tla) checks one six-command history with two selectable checkpoint cuts, route replacement, rival physical bytes, and prefix reclamation.
TLC checked 8,296 distinct states.
Two ten- and eleven-transition witnesses recover from different cuts after route loss or physical frame reclamation.
[HandoffRetention.tla](HandoffRetention.tla) checked six distinct states and a four-transition witness that accepts the acknowledgments early, applies activation, and then compacts.

| Weakening | Shortest counterexample |
| --- | --- |
| Drop the realized vector from a new checkpoint | Choose reservation and seal, capture the incomplete basis, and recover an image missing the original vector. Four transitions. |
| Select suffix frames by position alone | Choose a seal, replace the physical attachment with a rival at its position, and open the wrong vector. Four transitions. |
| Resolve a historical seal through the current pool route | Choose a seal, change the route, and apply a different realized vector on replay. Four transitions. |
| Use the selected body without the chosen suffix | Choose a command and recover only the older image. Two transitions. |
| Permit compaction once all participants acknowledge | Seal, acknowledge, and compact before activation. The pending handoff has lost the vector it needs. Three transitions. |

## General proofs

[JointSource.lean](JointSource.lean) checks six theorems over an executable augmented source reducer.
Its source effects use the existing chosen append, realized reserve and seal, funded activation, and verified settlement decisions.
The reducer authenticates the canonical seal body against the exact successful seal before it stores or exposes that result.
Append binds the ordered request to the exact historical physical window in that replay image.
Compaction preserves every window binding and refuses while its exact source handoff remains live.
The reducer also carries the original plan for cancellation evidence, delegates retirement to the ordered source, and retains exact append receipts under the ordinary trim floor.
The Lean control removes the handoff check and fails the compaction law.

[RankedJointReplay.lean](RankedJointReplay.lean) checks six theorems.
Replay can be split at any certified prefix.
Either named control and data envelope recovers the exact same full image once its actual chosen suffix is supplied.
Every accepted replay checks the same complete augmented frames, including all original ordered attachments, and a missing or rival suffix is refused.
Spurious physical surplus beyond the chosen head supplies no effect.
Ranked installation after arbitrary modeled owner changes contains the exact earlier chosen frames and attachments through the current recoverable basis.
Each recovery majority has a voter with that basis under the existing installed coverage premise.

## Amendments

[A295–A298](../amendments.md#study-75--2026-11-23) specify what the ranked frames and selectable checkpoints must certify, and keep the realized result until its local handoff consumes it.

## Acceptance coverage

- P134. Recover the same exact source state from bases with different cutoffs and suffix lengths, after route change or reclamation of safely superseded frames.
- P135. Refuse a rival attachment at the same ordered position and ignore physical surplus beyond the chosen cut.
- P136. Receive all acknowledgments before the local ordered activation. Keep the exact vector, apply activation, and then compact the source result independently of the current window.

## Residue

The augmented reducer checks canonical bytes for the realized seal body.
The rest of the command and control envelope is typed reference data.
Storage must authenticate its canonical encoding and prove that its opened bodies are the exact ranks and prefixes certified here.
The old and new named envelopes are independently tied to the exact chosen prefixes as theorem premises.
This work does not establish raw replica media serialization, actual evidence acquisition, or fresh admission following a new fault.
The general replay theorems are over all finite augmented histories that meet the stated certification and custody premises.
The bounded traces check one six-command history and one simplified early-acknowledgment race.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records exact commands, configurations, theorem checks, and traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/75-joint-realized-replay/run.py
```
