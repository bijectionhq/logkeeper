# Study 69 · Recover exact retained receipts across a writer move

2026-11-23

## Question

Can the successor reconcile an exact lost append reply through either selectable checkpoint after the original chosen frame leaves ordinary replay, without authorizing another write?

## Sources

Use the [joint checkpoint evidence rules](../50-joint-checkpoint/report.md), [funded chosen replay](../64-chosen-append-recovery/report.md), [atomic activation](../66-move-recovery/report.md), and [consolidated stream reference](../68-core-reference/report.md).
Test the original P02 and P07 acceptance programs at their chosen-operation and recovery boundaries.

## Model and comparisons

Attach the exact logical request and original outcome to each retained committed LSN.
Derive rows only from successful chosen application, and preserve rows in the selected basis or its exact suffix.
Keep delivery evidence and current physical placement separate from the original logical request.
Compare retention with dropping reply identity on checkpoint publication, matching only logical offset or payload, reappending a reconciliation, and answering with Logkeeper's result after trim.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- The exact original request recovers its original application result and ordered position without extending history.
- Changed bytes, lineage, or original writer grant cannot reuse the result.
- Every selectable recovery basis retains or reconstructs exact identity while the LSN remains retained.
- Trim ends Logkeeper's receipt authority and reports the retention floor.
- A fully funded successor can expose the same committed cut and the retained original result.
