# Study 91 · Bind terminal receipts to selectable recovery

2026-11-23

## Question

Can a receipt survive publication, crash and exact ranked recovery, then leave storage as soon as no recoverable history or borrower needs its original copy?

## Sources

Use [local rotation](../26-journal-rotation/report.md), [joint checkpoint proof protection](../50-joint-checkpoint/report.md), [the retained delivery reducer](../88-retained-delivery/report.md), and [terminal delivery evidence](../90-terminal-delivery-witness/report.md).

## Model and comparisons

Compose the local journal rotation and its exact stable and visible selector with receipt bytes, a durable name and a borrow pin.
Bind each admitted dependency to the exact proof in that selector's recipe.
Run ranked recovery from the authenticated base and exact durable ordered suffix.
Compare inline ordered settlement with a detached proof that remains a selectable path dependency.
Check publishing after only the bytes barrier, wrong proof bytes, reclamation on logical clear, visible-only reclamation of receipts or ordered tail, ignoring borrowers, and retaining every receipt forever.
In TLC model one switch and one crash.
In Lean use arbitrary traces, finite per-path receipt tables and typed exact frames.

## Properties and programs

- Every crash-selectable view can find the exact receipt bytes at its stable name.
- Replay of an inline settlement uses the exact attached evidence without an independent receipt lookup.
- A selected path's named receipt can supply the exact terminal witness, without changing the recovered ranked book.
- A detached receipt remains charged through all selectable paths and pins that need it.
- Once roots are stable and borrowers finish, fair cleanup can reclaim redundant receipts and raw frames.

## Reproduction

Use TLC 2.19 with Java 21, Lean 4.35.0 and Python 3.13.
Run negative controls first.
Keep commands, results and counterexamples in .results/.
