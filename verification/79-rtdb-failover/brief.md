# Study 79 · RTDB failover on an installed Logkeeper group

2026-11-23

## Question

Can an eligible RTDB worker replace a failed writer and reconcile a hidden chosen append with one AZ down, while the directory, a separate regional decision plane, and fresh allocation are unavailable?

The [baseline architecture](../architecture-reopening/comparison.md) assigns the grant to the reachable installed journal.
[Study 64](../64-chosen-append-recovery/report.md) checks recovery of the exact chosen prefix.
[Study 76](../76-stable-writer-handoff/report.md) checks same-placement grants and funded append windows.
[Studies 77 and 78](../78-sealed-worker-roster/report.md) supply the ordered eligibility and checkpoint premises.
This study composes the same-placement program P142 and tests the delivery contract for its fresh read.

## Common history

The incumbent's append is chosen, its response is lost, and a different payload at that position has staged elsewhere.
Lose one of three AZs and leave the known installed group route usable.
Recover the chosen prefix, admit a verified currently eligible replacement, reconcile the original request, and refuse the rival binding.
Require the worker to reach the inherited cut before serving.
Open a fresh barrier invocation, deliver an earlier authentic marker from the same writer scope, and compare accepting by cut, by matching a recycled identity, or by a fresh non-reused invocation.
Commit the successor's new append with the exact inherited physical extent and advanced cursor.

Compare the same trace with missing exact coverage, an old grant that can still append, or a requirement for new allocation or directory contact.
Distinguish chosen state from a physically staged candidate and from a caller receiving the result.

## Method

Use TLC for the finite history under every single AZ loss and for the progress and refusal variants.
Use Lean to run the acceptance sequence through the actual ranked source, ordered grant, receipt lookup, marker and funded append reducers.
Name route authentication, accepted physical support, invocation issuance and verified RTDB materialization as boundaries.
Keep physical replica correctness, complete request codecs, network transport and SQL execution outside this study.

The [report](report.md) records which parts are checked under those premises.
