# Study 66 · Recover an activation without restoring another authority's book

2026-11-23

## Question

Can either certified source checkpoint recover the exact funded activation after the pool settles independent workspace and a neighboring stream advances its own cursor?

## Sources

Use [joint checkpoint evidence](../50-joint-checkpoint/report.md), [exact physical extent accounting](../52-shared-extent-accounting/report.md), [chosen append and window recovery](../64-chosen-append-recovery/report.md), and [live funded installation](../65-funded-window-move/report.md).

## Model and comparisons

Put an atomic activation and window decision in the existing ordered stream reducer.
Refine its live effect against the charged regional move transition.
Recover source and pool state through their own certified authorities and merge only the affected stream's logical control state.
Compare atomic publication with an activation-only path, use of current pool evidence for historical replay, restoration of old pool claims from the source, and replacement of a neighbor's cursor from a stale book.
Keep fresh service subject to the destination's current physical readiness.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- A successful authorized activation publishes the exact destination window at the same ordered position.
- Either selectable source base recovers the same combined result.
- Historical replay leaves current physical claim and settlement state unchanged.
- Recovering one stream preserves the other stream's window cursors.
- The recovered result authorizes fresh service only with independently verified live window custody.
