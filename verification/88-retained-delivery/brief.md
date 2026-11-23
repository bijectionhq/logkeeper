# Study 88 · Bound and recover unfinished delivery evidence

2026-11-23

## Question

Can a chosen reply outlive its logical read and its original journal frame with bounded retained evidence and independently charged physical custody?

## Sources

Use the [ordered reissue decision](../87-ordered-reply-admission/report.md), [exact source outcome settlement](../47-source-outcomes/report.md), [joint checkpoint protection](../50-joint-checkpoint/report.md), and [regional physical custody](../61-regional-retirement/report.md).

## Model and comparisons

Add a finite delivery result book to the same reducer and journal order as logical read closure.
Bind each admitted slot to its exact scoped funding and non-reused serial.
Compare independent retained evidence against coupling it to the original read slot, trimming through a single visible checkpoint, relying permanently on the raw frame, accepting foreign terminal evidence, forgetting the issuance frontier, and overwriting a full book.
Model a single retained slot, a retained raw frame and two crash-selectable checkpoints in TLC.
Use arbitrary finite books and replay histories in Lean.

## Properties and programs

- A successful chosen authorization durably records its exact original result and physical use in the same transition.
- Read closure preserves that independent record.
- Both selectable recovery paths must cover the record and any required suffix before reclamation.
- Authenticated exact physical settlement clears only the named result and keeps its issuance floor.
- A held original use can complete from the named checkpoint through source loss.
- Bound record count, encoded bytes, and non-reuse through arbitrary replay.

## Reproduction

Use TLC 2.19 with Java 21, Lean 4.35.0, and Python 3.13.
Run negative controls first.
Keep proof output and counterexample traces under .results/.
