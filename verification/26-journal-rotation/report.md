# Study 26 report · Repeated journal rotations and recovery

2026-11-22

## Verdict

Treat the visible selector and the last durable selector as separate facts during recovery.
A verified warm opener can resume replica service while both selectors still have exact coverage.
Reclamation protects their combined dependencies and independently live physical reads.
Before publishing a second replacement, durably resolve the first.
This bounds power-loss recovery to two choices even across repeated rotations.

A prepared candidate whose predecessor has changed needs a fresh decision.
A publication can use a matching predecessor receipt or validate an exact forward base and its still-available suffix.
Choose predecessor binding for the base design because its receipt can validate the immutable cut and reuse established suffix coverage without scanning the suffix on the publication path.

## Bounded results

Each bound has two replacement generation identities and up to one live physical borrow.
The primary comparison includes up to two power losses and any number of warm restarts within the finite state space.

| Candidate | Records | Power losses | Distinct states | Result |
| --- | ---: | ---: | ---: | --- |
| Bound predecessor | 2 | 2 | 30,862 | Four safety laws hold. |
| Bound predecessor | 3 | 2 | 150,000 | Four safety laws hold. |
| Revalidate a forward candidate | 3 | 2 | 206,794 | Four safety laws hold. |
| Wait for durability before warm reopen | 2 | 1 | 8,710 | Four safety laws hold and early warm service is excluded. |
| Drain before publication | 2 | 1 | 9,369 | Four safety laws hold and reclamation of an intermediate base with a pinned original is excluded. |

| Amendment | Weakening | Shortest counterexample |
| --- | --- | --- |
| A90 | `trust_warm_name` | Stage and expose a replacement, warm restart, reopen, then reclaim the predecessor from the visible name. A still-possible crash result has lost its root in five transitions. A six-transition trace selects the missing root on power loss. |
| A91 | `stack_unstable` | Expose two replacements without a barrier. Three roots are possible after five transitions. Removing the intermediate root breaks recoverability in six. |
| A92 | `stale_base` | Prepare one base including record 2 and another stopping at 1. Durably install the former, remove the tail extent for 2, then install the stale base. Seven transitions. |
| A93 | `forget_borrow_after_restart` | Borrow the original base, restart while its successor is visible but volatile, sync the selector, then reclaim the still-borrowed base. Seven transitions. |

The main candidate reaches a verified warm reopen before selector sync in four transitions.
In seven, it also votes for another record, loses power, and reopens through the predecessor with the exact new suffix.
The revalidating candidate installs a forward base prepared against an earlier predecessor in six.
In ten, the main candidate retains a pin on the original while settling two rotations and reclaiming the intermediate durable generation.
In twelve, it recovers after power losses at two different installed generations and reclaims both older roots and a covered tail extent.
These acceptance traces establish that the operations can occur within the modeled bounds.
They give no performance or fairness guarantee.

## General proofs

Lean checked fourteen theorems with standard axioms only. [Proofs](JournalRotation.lean)
The model represents the media's possible power-loss choices independently of the two selectors known to the replica.
Every transition preserves exact agreement between these representations.
Every permitted recovery view reconstructs the same acknowledged history from its own base and the exact shared suffix.
All physical pins keep their original bytes through arbitrary finite traces, including appends, stage, restart, publication and reclamation.
A verified warm reopen preserves predecessor eligibility.
The proof covers arbitrary record lists, generations and traces under its media and custody premises.
The direct exact-closure guard is the Lean publication interface.
The theorem for a complete forward base derives that guard from the preceding exact view, the captured image, and the cut ordering.
The explicit predecessor comparison and the alternate policy are checked in TLC.

The quorum proof connects a certified retained record to a readable exact base entry or tail extent on an available current voter after arbitrary local rotation traces.
It uses the previous quorum intersection theorem and assumes each certified abstract copy corresponds to the exact local acknowledged history at the start of the trace.
The local histories can extend while the proof preserves their earlier records.

Four Lean controls weaken serialization of uncertain publication, protection for the durable selector, protection for exact borrows, or the exact correspondence of a quorum copy to its local journal.
Each fails its specified proof.
During trace review, two early acceptance assertions were found to admit histories in which a middle base was staged but never installed.
The checked versions require actual durable installation and, for the double-loss scenario, power-loss outcomes at two distinct installed generations.
The stable-open observation also records the reopen action itself so it cannot confuse it with a later unrelated publication.

## Remaining obligations

The model takes local bytes and namespace durability from the [media study](../25-media-crash-consistency/report.md).
A power loss resolves the modeled namespace choices to the identity that survived.
A warm restart preserves both choices while process-local evidence is rebuilt.
The borrow table represents the aggregate live custody on each immutable extent.
Its release assumes completion or an effective stop for every underlying borrow.
Competing processes, stale asynchronous delete permits, actual filesystem rename and flush behavior, staging quotas, and qualification of the incumbent opener need further refinement.
Two selectable roots bound recovery choices.
Staging and pinned extents remain separate charges against the journal's physical capacity.
Group commit certification and authorized stream trim are at their separate logical authorities.
The proof bridges current quorum recovery for each retained record.
It leaves actual vote formation and concurrent changes of the quorum configuration to the consensus and membership refinement.

Apply [A90–A93](../amendments.md#study-26--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner records exact commands, logs, and counterexamples under the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/26-journal-rotation/run.py
```
