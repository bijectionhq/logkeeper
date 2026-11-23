# Study 35 report · Compact activation attempt fences

2026-11-22

## Verdict

Record an installed issuance cutoff in each live activation intent.
Advance it over exact ready or spent attempts.
Retain exact ready rows and every unsettled physical cleanup obligation.
An absent row at or below the cutoff has the same admission semantics as an individual spent marker.
Voter replacement preserves the cutoff and the remaining obligations.

Issuer credit comes from the installed cutoff.
Limit physical pins separately so that a ready grant or pending cleanup consumes physical capacity even after its serial leaves the issuance window.
This reuses the previously checked custody-floor rule in the ordered target activation path.

## Bounded comparison

Each case has one intent and at most one voter replacement.
An attempt serial identifies its exact authorized binding in the model.
The checker explores admission, exact discard, offered and installed cutoffs, independent physical settlement, replacement, and final selection.

| Candidate | Attempts / width / pins | Distinct states | Checked result |
| --- | --- | ---: | --- |
| Advance through ready or spent | 3 / 1 / 1 | 223 | Seven safety laws hold. |
| Advance through spent only | 3 / 1 / 1 | 127 | Seven safety laws hold. |
| Advance through ready or spent | 5 / 3 / 2 | 12,451 | Seven safety laws hold. |
| Advance through spent only | 5 / 3 / 2 | 4,665 | Seven safety laws hold. |

The seven laws cover refusal of closed attempts, unresolved preparations, retained physical obligations, selected images, issued credit, individual terminal markers, and physical pins.
The ready-or-spent policy can issue a later serial after advancing across a live ready row, then select the original row in six transitions at width one.
The spent-only policy excludes that sequence across all 127 states at that bound.
Another witness keeps charged cleanup after marker compaction and voter replacement in six transitions.
An execution also settles it after both steps and leaves another image selected in ten transitions.

| Amendment | Weakening | Shortest bounded failure |
| --- | --- | --- |
| A131 | `ignore_floor` | Compact a discarded attempt and admit its delayed registration in five transitions. |
| A131 | `forget_floor` | Lose the installed cutoff at replacement, then admit the delayed registration in six transitions. |
| A131 | `skip_unresolved` | Install a cutoff over an unresolved issued serial in three transitions. |
| A132 | `forget_live` | Remove the selected image's ready row during compaction in five transitions. |
| A133 | `forget_cleanup` | Compact a closed marker and lose the only settlement obligation for a held pin in five transitions. |
| A134 | `offer_is_credit` | Allocate beyond the installed credit window using an offered cutoff in five transitions. |
| A134 | `unmetered` | Acquire a second physical pin at a limit of one in four transitions. |

## General proofs

Lean checked seven theorems with standard axioms only. [Proofs](AttemptCompaction.lean)
Compaction leaves the interpreted activation reducer state exactly equal to its old state for arbitrary attempt tables.
Consequently every later command sequence has the same outcomes and final logical state.
The interpreted state covers reducer decisions over authorized commands.
Issuing new credit remains a separate check against the installed cutoff.
An exact ready ticket remains eligible under the same ordered revision and grant checks.
An absent row at or below the installed cutoff becomes a spent row in the interpreted machine.
The earlier replay invariant then refuses its delayed registration after any later command sequence.

Physical cleanup remains independent of the compacted table.
The arithmetic proof places every remaining explicit terminal marker at a distinct index in the issued credit window.
Three Lean controls fail when compaction crosses unresolved rows, removes live readiness, or erases cleanup.

## Remaining obligations

The Lean proof checks representation equivalence and marker bounds.
The finite search checks physical quota and exact cleanup interleavings under a single replacement.
Authentication of issuance and exact holder settlement, staged copies waiting for registration, byte accounting, and provider failure progress use the other custody contracts.
The proof leaves terminal reclamation of an entire intent to a durable fence on that intent's non-reused identity.
Study 36 checks [retirement of that exact admission](../36-intent-retirement/report.md).

Apply [A131–A134](../amendments.md#study-35--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, checker traces, and mutation diagnostics under the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/35-attempt-compaction/run.py
```
