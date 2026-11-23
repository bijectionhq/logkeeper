# Study 14 · Physical custody for admitted reads

## Question

Can compaction, logical trim, or a stream move reclaim the exact bytes an admitted read is using?

## Sources and scope

Use S06 and P06 from the [requirements](../requirements.md) and the [snapshot handoff study](../08-replay-handoff/report.md).
RTDB's `ReleaseReplicaReplay` currently requires a drained replay or confirmed owner stop and addresses ambiguous registration.
The proposed fast release applies only to an operation that has independently reserved all its physical input bytes.

Model an original extent, a same-site compaction replacement, and a target extent with the same exact record.
An operation locates a candidate extent, acquires a physical borrow, and eventually finishes or is effectively stopped.
A move changes the site for new admissions.
Previously admitted source operations retain their own physical obligations.
The source link may become permanently unavailable.
A timeout is an observation and leaves physical operation state unchanged.

Compare waiting for all operations to drain before releasing the logical hold with releasing it once admission is effectively fenced.
Both candidates protect physical borrows.
Mutate lookup-to-borrow validation, the physical reclaim guard, admission closure, timeout handling, and result fencing.
Check safety up to two requests and conditional drainage under weak fairness for effective fencing at reachable sites.

The finite model treats closure of new admission as an already effective fence and move installation as an already certified cut.
It does not assume that an unreachable endpoint obeyed a new request.
A separate eventual-stable-reachability condition supports progress.
The Lean model treats an extent and the exact bytes it represents as part of the physical admission.

## Rules

Use pinned TLC and Lean 4.35.0, checking weakening controls and acceptance traces.
Record the exact model bounds, messages, and unresolved deployment premises in the [report](report.md).
