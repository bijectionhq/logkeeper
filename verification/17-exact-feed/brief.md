# Study 17 · Exact historical feed

## Question

If Bijection requires exact events after a cursor falls behind the bounded WAL, what must be durable and how can a reader join historical events to a live suffix while trim advances?

## Sources

Use the [bounded retention result](../03-retention/report.md), [permit contract](../15-replay-permits/report.md), and [checkpoint semantics](../16-checkpoint-reconstruction/report.md).
RTDB Multi marks the behavior of a `changes` subscriber behind the retained floor as an open product question in `allium/rtdb-multi.allium`.

## Model and properties

TLC models one exact archived prefix, a bounded journal suffix, checkpoint publication, trim, and one reader with a frozen upper cut.
Check that archive publication is gap-free, trim never passes available exact history, and every successful response returns the exact ordered events in the captured window.
Lean checks the two-source concatenation for arbitrary finite lists, a countermodel to generic reconstruction from state, and the admission limit imposed by a stalled archive.
The model assumes a stable archive prefix and omits archive expiry, authentication, physical custody, and the actual RTDB history representation.

## Comparison

Compare contiguous archival with a gapped publisher, checkpoint-only trim, a planned join without floor revalidation, and an overlapping join.
Require constructive witnesses for replanning across a trim and for using both physical sources in one successful read.
The runner checks deliberately weakened proofs and bounded controls before the matching positive result.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/17-exact-feed/run.py` from the checkout with tool paths as in the [verification index](../README.md).
See the [report](report.md) for results and scope.
