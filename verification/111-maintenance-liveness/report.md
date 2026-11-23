# Study 111 · Keep the maintenance lane live under repeated writer replacement

2026-11-23

## Verdict

The fixed maintenance reserve can stall checkpoint progress permanently.
RTDB appends the term's claim `NoOp`, block boundaries and block uploads, including recovery confirmations, as maintenance records (`replication/src/logs.rs:183-188` at RTDB `fd3d6dcb32`).
Only trim through a published checkpoint refunds the reserve.
Each writer replacement before the next checkpoint adds a claim, so enough replacements fill any fixed reserve.
Publishing the next checkpoint then needs a boundary and an upload that no longer fit.

In an installed journal the Logkeeper grant already fences terms, refuses appends from a superseded grant, and makes the successor replay through the granted cut.
Deriving the RTDB term from the grant removes the per-term claim and the recovery confirmation.
The maintenance lane then needs three records: the retained previous upload, and the in-flight boundary and upload.
The bound is independent of the number of replacements.

## General proofs

Lean 4.35.0 checked four theorems with standard axioms only.
`grant_fencing_bounds_maintenance_by_three` holds for every reachable lane under any number of replacements.
`a_three_record_reserve_always_admits_progress` shows the next progress record always fits.
`per_term_claims_exceed_any_fixed_reserve` shows the incumbent has no fixed bound.
The Lean control charges a record on every replacement and fails at the shape proof.

## Bounded comparison

| Case | Result |
| --- | --- |
| Per-term claim with the documented five-record reserve | Progress headroom lost in five transitions, and checkpoint progress stalls after four replacements. |
| Grant without journal fencing | A superseded holder's upload enters the log in four transitions. |
| Grant-fenced lane with a three-record reserve and six replacements | Safety and eventual checkpoints hold in 231 states. |
| Per-term claim without replacements | Holds in nine states. |

Temporal checks assume weak fairness for the claim, boundary, upload and publication actions and a finite number of replacements.

## Amendments

[A459–A460](../amendments.md#study-111--2026-11-23).

## Residue

The model counts records, not bytes, and assumes the maximum record size used by RTDB's reserve sizing.
The RTDB driver change derives the installed term from the grant and must keep the Kafka path's claim election unchanged.
Its refinement against the production driver is open.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/111-maintenance-liveness/run.py
```
