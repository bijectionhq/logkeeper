# Study 113 · Dispose a withdrawn worker's holds without operator evidence

2026-11-23

## Verdict

Logkeeper's `DisposeWorker` removes a worker's holds on operator evidence alone (`src/ordered.rs:1080-1105`).
A wrong report lets a partitioned worker keep serving readers on a checkpoint that the custodian then closes and trims.
Without disposal, a superseded worker's read and recovery holds block trim indefinitely, because grant change and withdrawal leave holds in place (`src/ordered.rs:864-911`).

The worker should serve only within a serving lease that the journal renews while it holds an enrolled grant.
The worker checks the lease at each read admission against its monotonic clock.
After withdrawal, the journal disposes the worker's holds automatically once the lease end plus the drift bound has passed.
A fence that runs separately from read admission is not enough: the worker can admit a read after its lease has lapsed.

This adds an environment premise: worker and journal clocks have bounded rate error over the lease interval.
RTDB already accepts this premise for reader lifetime (bounded monotonic leases in RTDB's `verification/PROGRAMME.md`).

## General proofs

Lean 4.35.0 checked two theorems with standard axioms only.
`no_read_is_admitted_once_disposal_is_allowed` holds for any lease end and drift bound.
`without_the_drift_margin_a_lagging_worker_still_admits` shows the margin is necessary.
The Lean control drops the margin and fails at the first proof.

## Bounded comparison

TLC 2.19 uses a lease of two ticks, a drift of one tick and a six-tick horizon.

| Weakened design | Result |
| --- | --- |
| Dispose on operator evidence | A reader reads trimmed bytes in four transitions. |
| Lease with an unbounded slow clock | A reader reads trimmed bytes in seven transitions. |
| Fence asynchronously instead of at each read | A reader reads trimmed bytes in seven transitions. |
| Never dispose without evidence | Temporal stall: a withdrawn worker's holds block trim forever. |

The reference holds in 256 states, and a withdrawn worker's holds are eventually trimmed under fairness of time, fencing, disposal and trim.
A witness reaches trim in six transitions.

## Amendments

[A464–A466](../amendments.md#study-113--2026-11-23).

## Residue

The model has one worker and one checkpoint, and abstracts lease renewal into the withdrawal time.
The Logkeeper serving lease, its renewal command and automatic disposal, and RTDB's per-read lease admission on installed workers are implementation work.
Qualification needs a measured clock rate bound.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/113-worker-disposal/run.py
```
