# Study 30 · Reads across voter reconfiguration

2026-11-22

## Question

When voter membership changes during a read, which quorum evidence can the caller keep and which snapshot resources must the system preserve?

## Sources

Use the [requirements](../requirements.md), [membership comparison](../12-quorum-membership/report.md), [exact replay reservations](../18-snapshot-admission/report.md), [fixed-group agreement](../27-prefix-consensus/report.md), and [fresh read index](../29-read-index/report.md).
Read RTDB Multi's `QuorumsCountDistinctJournals`, `NothingCommittedIsLost`, `ReadIndexUsesTheActiveLoglet` and `TrimFollowsPublication` at `fc6da3a4a3`.

## Model

Use one stream and one replica-group lineage with an old, joint or sealed, and successor configuration.
Model local durable voter scope separately from the authoritative phase.
An authorized transition installs the exact current history on a ready quorum and can leave other voters in their previous scope.
Read observations retain the scope at which their voter answered.
Writes in the joint phase require majorities of both constituencies.
The serving replica's certified applied position can lag the group's chosen position.

After a valid round, reserve the currently selected root and the suffix to a certified applied cut covering the sampled maximum.
The chosen cut and its physical requirements survive later publication and membership changes.
Treat the membership decision, exact copied contents, and checkpoint validation as premises from the earlier studies.
Use the logical batch semantics from the read-index study.
Treat an atomic reservation against the applied view as the custody boundary.

## Checks and comparison

- Compare dual-majority reads in joint membership with successor-side reads and reads from a majority of either constituent.
- Test which durable fences exclude every old read quorum after finalization.
- Compare carrying an immutable round as a floor against requiring a fresh current-scope round or waiting for the original selected cut.
- Test late samples, mixed voter scopes, speculative floors, lagged application, and disappearance of reserved roots or suffixes.
- Exhibit a read using an old round with a newer applied root, a live older reservation surviving adoption, and a retry after a discarded speculative floor.

## Tools and report

Use TLC 2.19 with one worker and a 512 MiB heap, and Lean 4.35.0.
Record negative controls, state counts, shortest traces, and the proof boundaries.
Keep a focused two-command schedule separate from the general single-command bounds.
