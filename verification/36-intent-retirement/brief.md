# Study 36 · Retire an activation intent

2026-11-23

## Question

When can a target reclaim the whole incoming activation row while old copies and installation replies can still arrive?

## Sources

Use the [requirements](../requirements.md), [move cancellation](../10-cancel-move/report.md), [custody channel lifecycle](../21-custody-channel-lifecycle/report.md), [pending activation](../34-pending-activation/report.md), and [attempt compaction](../35-attempt-compaction/report.md).

## Model and comparison

Model one reusable admission slot, exact source seal or abort, exact target installation, an independent copy plan, and an independent durable result record.
Let an old copy request or reply arrive after retirement and new admission.
Compare detaching those two obligations with requiring settlement of both before retirement.
Compare reserving result capacity at admission with acquiring it at installation.
Model voter replacement as restoring the durable image and onward movement as authorized adoption elsewhere.
Use authenticated source decisions, copy settlement, and onward adoption as premises for the abstract actions.

## Properties and acceptance

- Preserve exact admission and installation scope across retirement, reuse, and replacement.
- Refuse retirement of an irrevocably sealed move awaiting installation.
- Keep a chosen result retrievable until the source durably records that exact binding.
- Reuse the admission slot after an exact abort while old cleanup remains charged. Fence the empty copy slot, then refuse its delayed copy request.
- After installation, reuse the slot, move onward, and replace the old target's voters. Drop a result reply, then recover and acknowledge the original result.
- With one result credit, acknowledge the original result before admitting a new intent.
- Retire under fair target scheduling while either the provider or source receipt path remains inaccessible, given that the target has the required terminal evidence.
- Check fair installation from a ready sealed intent and fair settlement of retired aborted copies under their stated premises.

## Tools and evidence

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for arbitrary admission and result traces, the terminal guard, and exact copy plan preservation.
Run the negative controls before the baseline checks in each tool and record their failure sites.
