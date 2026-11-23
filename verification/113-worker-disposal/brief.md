# Study 113 · Dispose a withdrawn worker's holds without operator evidence

2026-11-23

## Question

When can the journal release a withdrawn worker's holds, so that a partitioned worker never serves bytes that were trimmed and a dead worker never blocks trim?

## Model and comparisons

Compare operator-evidence disposal, a never-disposed worker, an asynchronous self-fence, and a lease with an unbounded clock against a journal-issued serving lease checked at each read and disposal after its end plus the drift bound.
Use TLC 2.19 with discrete time and Lean 4.35.0 for any lease and drift.
