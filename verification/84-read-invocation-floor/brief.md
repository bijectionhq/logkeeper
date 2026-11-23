# Study 84 · Keep closed read invocations spent

2026-11-23

## Question

Can recovery enforce one-use protected read admission after complete reclamation of its row without an unbounded history of completed invocations?

## Sources

Use [S04, S68–S70, L05, B23, and P149–P158](../requirements.md), [ordered writer eligibility](../77-ordered-worker-eligibility/report.md), and the [combined read and journal reducer](../83-ordered-read-replay/report.md).

## Model and comparisons

Compare an exact-next floor, live-row deduplication, and a largest-seen watermark in one finite transition system.
Exercise reclaim, reopen from a checkpoint, delayed messages, missing next requests, writer replacement, and finite nonce exhaustion.
Use two writer grants, one paid result slot, and two usable nonces per grant in TLC.
Use the actual combined chosen reducer, arbitrary word size, and arbitrary finite replay in Lean.
Keep physical custody, receipt signing, the writer's external assignment of pending identities, and ranked certificate acquisition at their typed reference boundaries.

## Properties and programs

- Check one-time admission after closure, compaction, and crash recovery.
- Check that a later proposal cannot silently consume a pending earlier nonce.
- Check that a writer can explicitly abandon the exact next nonce without read capacity and that the next request can then run.
- Check that a newer grant opens a fresh namespace and preserves reissue of live old rows.
- Check that exhaustion refuses fresh admission and that restoring a named combined snapshot restores its own floor.

## Resources and evidence

Use TLC 2.19 with Java 21, Lean 4.35.0, and Python 3.13.
Run the negative controls first.
Report the finite histories, proved properties, relation to policy choices, and remaining provider and transport premises.
