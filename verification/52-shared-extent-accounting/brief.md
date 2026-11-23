# Study 52 · Charge shared physical extents across concurrent uses

2026-11-23

## Question

Can concurrent checkpoints, replay evidence, and moves share a physical debit without losing capacity accounting when references, controller ownership, or provider state change?

## Sources

Use the [shared object custody](../19-shared-object-custody/report.md), [concurrent capacity](../43-concurrent-capacity/report.md), [settlement composition](../48-settlement-composition/report.md), and [checkpoint evidence](../50-joint-checkpoint/report.md) studies.

## Model and comparison

Compare exact physical allocation accounting with charging separately for each logical use.
Include same-content copies, distinct versions in the same pool, a cross-pool copy, independent controls for references and physical borrows, and possible writes after a move is canceled.
Model exact provider disposition and metadata controller replacement separately.
Treat immutable version identification, authenticated durable presence, and true extent sizes as premises.

## Properties and acceptance

- Two authorized uses of the same charged physical extent can share it at full byte capacity.
- An additional physical allocation has its own charge even if its bytes match another extent.
- Charge the full physical allocation while it exists or a previously issued write can still materialize it.
- Closing one use preserves other uses, standalone physical borrows, and all outstanding physical debits.
- Returning one extent's charge requires its exact durable absence and excludes later recreation.
- A controller replacement preserves active charges and their original physical scopes.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 for pointwise capacity, custody refinement, and exact release across arbitrary admitted traces.
