# Study 28 · Ordered application and fresh receipts

2026-11-22

## Question

What must happen between a group choice and a successful stream reply when a request races with a writer fence or retirement?

## Sources

Use the [requirements](../requirements.md), the [reference kernel](../07-reference/Kernel.lean), and the [fixed-group consensus proof](../27-prefix-consensus/report.md).
Use the [atomic snapshot reservation](../18-snapshot-admission/report.md) to distinguish the choice of a read cut from the storage required to serve its contents.
Read RTDB Multi's `AppendIsConditionalOnEpochAndPosition`, `ReadIndexUsesTheActiveLoglet`, `ResolveAndAppend` and `ApplyOnCommit` at RTDB commit `fc6da3a4a3`.
The incumbent uses replica promises and synced epochs for append admission.
The study models application of a general chosen command history to the reference kernel.

## Model

Separate proposal, group choice, ordered application, and reply delivery.
A valid group certificate contributes an exact command prefix.
The deterministic reducer has one outcome per command at its original group position.
An unauthorized or otherwise refused command leaves the stream state intact.
An applied append advances the stream's next LSN and binds its success to the exact request.
A read marker carries the invocation identity and the writer it observes.
Its ordered state supplies the cut.
Later choices can extend the transcript while responses are in flight.

The finite model has two writer grants, a retirement decision, append positions, and two fresh read identities.
It treats the chosen group sequence as the output of agreement and uses a separate functional replay as the safety oracle.
The general model lowers all existing logical kernel transitions and composes its replay with the chosen-prefix proof.
Abstract the authenticated transport, actual durable certificate formation, finite storage representation, and pinning of the checkpoint and tail used to serve a read.

## Checks and comparison

- A successfully applied command follows the reference step relation, and an existing reference step can be expressed by an ordered command.
- An append receipt binds the original chosen request and its successful result.
- A fresh barrier returns the cut from its own selected and applied marker, including all preexisting commits.
- Compare checking the writer and exact next LSN at application with prevalidating the writer alone or bypassing the LSN check.
- Compare the ordered marker with reading a lagging replica and replaying a completed marker for another invocation.
- Exhibit a chosen stale append refusing after a fence, an older successful response surviving retirement, and a read reply preserving its earlier cut during a concurrent append.

## Tool and report

Use TLC 2.19 with one worker and a 512 MiB heap, and Lean 4.35.0 with the pinned study toolchain.
Use the certified sequence abstraction in TLC.
Run each weakening before the intact candidate.
Record shortest bounded traces, the checked bounds, and the assumptions on sequencing and outcome delivery.
Describe the ordered marker as the reference for a read-index refinement.
