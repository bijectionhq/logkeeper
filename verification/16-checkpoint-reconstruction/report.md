# Study 16 report · Checkpoint reconstruction

2026-11-22

## Verdict

Certified recovery binds a root to the stream incarnation, format, exact ordered prefix, and its exclusive replay start.
The decoded root must provide the continuation state for that prefix and its dependencies must have durable custody.
Replay reconstructs a captured cut with its exact suffix.
A child can reuse immutable parent objects with a new certificate at child genesis, under the child's own decoding and custody conditions.

## TLC results

All five laws hold across 4,503 distinct states with two records and 32,523 with three records.
Both bounds include two values per record, inherited child genesis, one staged checkpoint, and one captured read.
The four-transition fork witness recovers inherited state at child cut zero.
The ten-transition recovery witness captures the second position, appends a third record, publishes and trims a certified prefix, and then serves the captured cut.

| Amendment | Weakened rule | Shortest counterexample |
| --- | --- | --- |
| A47 | `numeric_scope` | Admit a parent receipt at the same numerical cut into the child catalog. Three transitions. |
| A48 | `by_state` | Commit two different values and certify their reversed prefix because the decoded aggregate agrees. Five transitions. |
| A48 | `loose_root` | Publish a fully covered root whose decoded value differs from the correct state. Three transitions. |
| A48 | `manifest_only` | Publish even though a manifest dependency lacks custody. Three transitions. |
| A48 | `ignore_format` | Publish a valid root under an unsupported format. Three transitions. |
| A49 | `newer_root` | Capture a cut, commit and publish a newer cut, and answer from that future root. Seven transitions. |
| A49 | `follow_head` | Select a root, append after capture, and use the live head when reading. Five transitions. |
| A49 | `omit_tail` | Capture a committed record and return the genesis root without replaying it. Five transitions. |

## General model proofs

Twelve [Lean theorems](CheckpointReconstruction.lean) check the reconstruction algebra, prefix stability for arbitrary finite logical traces, refusal of foreign receipts and uncovered gaps, and the parent-to-child rebase at genesis.
Constructive programs publish and trim under the certificate and replay guards, then recover a requested cut from the published image and exact suffix.
The typed catalog trace refines the existing kernel and preserves its certified-cut invariant at each step.
Weakening receipt scope, exact suffix binding, or the certified-only publication path breaks the corresponding proof.
The checker reports only standard axioms.

## Residue

The reducer state stands for all continuation information RTDB needs, including any intake position supplied by the boundary record.
RTDB currently retains that record on certified trim.
Determine the actual exclusive replay start from codec and reopen behavior before changing the legacy `checkpoint.lsn` boundary.
The model's ordered prefix is a ghost witness.
An authenticated prefix commitment may discharge that obligation without storing the entire prefix in a receipt.
Cold recovery, checkpoint open against concurrent provider reaping, manifest authentication and closure including actual fork ownership still require RTDB refinement.
The Lean recovery program assumes its published image precedes the requested cut and the caller can obtain the exact retained suffix.
If publication overtakes an unprotected captured cut, the newest image can be too recent.
An admission protocol that promises completion for a fixed cut must protect a suitable root and journal range before that race can close both options.
[Study 18](../18-snapshot-admission/report.md) checks a reservation-based resolution for ordinary latest reads and states its remaining refinement premises.
The TLA+ recovery model uses ghost history to calculate the suffix and checks its retention floor separately.
Lean treats durability and decoding as premises for the recovery basis under protection.
The [physical custody model](../14-read-custody/report.md) studies removal and borrows.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/16-checkpoint-reconstruction/run.py
```
