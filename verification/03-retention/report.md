# Study 03 report · Bounded retention and replay admission

2026-11-22

## Verdict

Both races are real.
Prechecking trim and prechecking cursor admission do not keep a range safe when their writes can interleave.
Serialize the final logical trim and replay grant against one authoritative floor and hold set.
Checkpoints and live holds constrain two different backlogs.

Lean proves that with a fixed certified cut a finite recovery budget caps eventual commits.
It proves the same conflict between a fixed exact cursor, finite retained work, and unbounded commit progress.
A separate capacity theorem shows how reserving space keeps a checkpoint control operation admissible when ordinary admission stops.

## Properties and comparison

The baseline satisfies all four invariants at five LSNs across 1,446 states and eight LSNs across 3,366 states.
The replay budget is two records and the retained budget is three.
The [brief](brief.md) defines which properties were checked and which failures are abstracted.

| Amendment | Mutation | Property | Shortest counterexample |
| --- | --- | --- | --- |
| A13 | `use_uploaded` | `PublishedBeforeTrim` | Append → upload → prepare trim → trim without publication. Four transitions. |
| A14 | `stale_replay` | `ReplayProtected` | Append → stage a cursor at LSN 0 → upload and publish through LSN 0 → prepare and commit trim → admit the now-unreadable cursor. Seven transitions. |
| A14 | `stale_trim` | `ReplayProtected` | Append → stage a cursor at LSN 0 → upload and publish → prepare trim → admit the cursor → commit stale trim over its live hold. Seven transitions. |
| A15 | `no_recovery_cap` | `RecoveryBound` | Append three records without publishing a checkpoint. Three transitions. |
| A15 | `no_retained_cap` | `RetainedBound` | Append twice and advance publication, then append twice without advancing the retention floor. Six transitions. |

## Acceptance programs and developer cost

The caller supplies a published checkpoint receipt and the cursor's first required LSN.
The proposed stream authority orders logical trim and replay admission together.
A refused cursor gets the current floor and can reopen a checkpoint or switch to history.
RTDB still owns checkpoint authorization and object leases.
Coordinating both leases to the same checkpoint remains a cross-component refinement obligation.

With every record checkpointed, an admitted old cursor can still block ordinary append at the retained cap.
TLC reaches that state in nine transitions.
The baseline can close a hold at the cap, advance its floor, and accept a fourth record in eleven transitions.

## General proofs and controls

| Theorem | Strength |
| --- | --- |
| `checkpoint_stall_forces_backpressure` | For every possible committed-head predicate and finite cap, a fixed reconstructable cut and bounded replay exclude unbounded progress. |
| `exact_cursor_caps_head`, `indefinite_pin_forces_backpressure` | A fixed live cursor and a finite retained suffix cap committed head, irrespective of checkpoint progress. |
| `full_budget_excludes_positive_control`, `reserved_capacity_admits_control` | A full budget refuses positive-cost control work. With a reserved slice, a control charge within that slice fits after ordinary admission. |

Lean checks all five with only `propext` and `Quot.sound`.
The arithmetic controls remove the recovery bound, cursor protection, or reservation premise and require the corresponding proof to fail.

## Residue

The Lean model counts increasing LSNs and assumes exact replay of each required record.
It excludes alternate recovery representations or a distinct durable history service.
The TLC capacity model is logical, with byte charges, group-wide resource pressure, live holds across transfers, and physical reclamation remaining to be modeled.
A real recovery marker in the log consumes bytes and must be covered by the reserved progress lane.
Permit expiry, backpressure thresholds, and fair service need a separate proof and operational budget.

## Reproduction

Use Python 3.13, Temurin Java 21.0.13+9, and the pinned Lean 4.35.0 toolchain.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/03-retention/run.py
```

The runner saves generated configurations, commands, and logs under `.results/`.
