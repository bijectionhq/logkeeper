# Study 77 · Order worker eligibility at the journal

2026-11-23

## Question

What must a stable journal commit to reject a worker nomination delayed across withdrawal and re-enrollment, while keeping funded failover and administrative retirement available?

The study starts from [the selected architecture](../architecture-reopening/comparison.md), [Study 76](../76-stable-writer-handoff/report.md), and [the implementation gate](../implementation-gate.md).
Study 76 treats nomination authorization as a predicate.
This study makes the live enrollment binding part of the recovered source state.

## Model and acceptance

Model one installed journal with an ordered history, a current grant or a fenced vacancy, and a small roster.
The journal authenticates scoped worker edits and nominations and compares them to the state at their ordered positions.
An enrollment has a non-reused serial.
Withdrawal closes one exact enrollment and vacates the grant in the same decision when the removed worker holds it.
Re-enrollment of the same worker issues a new serial.
The issuance counter has a ceiling, while closure has no new issuance requirement.

Use the same state machine to compare presence-only eligibility, signatures without current membership, worker removal that leaves an active grant, and closure requiring a successor or new serial.
Race old and fresh nominations and admin edits.
Keep an unaffected candidate eligible while a different worker enrolls and withdraws.
Check retirement after the current writer is withdrawn, including at the last representable enrollment serial.

Use TLC for finite counterexamples and liveness and Lean for the actual chosen source reducer, kernel projection and exact replay.
Abstract signature verification, independent provider failures, real routing, exact wire encoding, and across-region control traffic.
Keep P142's full append, barrier and data-recovery behavior as a separate integrated obligation.

The [report](report.md) records the cases, bounds, commands and limitations.
