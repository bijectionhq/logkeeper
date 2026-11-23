# Study 50 · Replace replay evidence with a certified continuation

2026-11-23

## Question

Which evidence can leave the command journal after a joint checkpoint when participants still need an exact outcome?

## Sources

Use the [checkpoint reconstruction](../16-checkpoint-reconstruction/report.md), [selector recovery](../26-journal-rotation/report.md), [source result](../47-source-outcomes/report.md), and [joint replay](../49-unified-source-history/report.md) studies.

## Model and comparison

Separate evidence still needed by a replay suffix, evidence borrowed by an endpoint, and an outstanding result that can be reissued from a certified checkpoint.
Compare retaining the original result receipt with certifying its exact equivalent from the current checkpoint.
Compare retirement of evidence at the visible cut with retirement after every crash-selectable cut covers it.
Model bounded control metadata separately from the logical data history and physical dependencies.

## Properties and acceptance

- Every selectable checkpoint and its surviving suffix recover the same committed state.
- Exact decision evidence stays obtainable for outstanding participants after eligible journal trim.
- Earlier proof bytes stay while reachable replay bases or physical borrows need them.
- Recovery preserves the original scope, outcome, and ordered command cut without fresh participant evidence.
- The control image and retained evidence have separate explicit budget parameters.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 for replay and statement equivalence and an independent finite metadata bound.
