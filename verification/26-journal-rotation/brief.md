# Study 26 · Repeated journal rotations and recovery

2026-11-22

## Question

Can a replica recover service and keep compacting across repeated interruptions while every possible recovery generation and old read remains valid?

## Sources

Use the [requirements](../requirements.md), the [single-switch media study](../25-media-crash-consistency/report.md), and the [exact physical read custody study](../14-read-custody/report.md).
Use RTDB Multi's `ReplicaIdentityFollowsTheJournal`, `CommitIsAWriteQuorum`, and `TrimFollowsPublication` invariants at RTDB commit `fc6da3a4a3`.
Read the [journal opener and compaction](../../src/server/journal.rs) at `85a594e` for incumbent behavior.

## Model

Model an acknowledged prefix, durable staged bases, immutable shared suffix extents, a visible selector, and the last durably installed selector.
Represent every possible power-loss outcome explicitly.
A namespace sync collapses the choices to the visible selector.
In a warm process restart the namespace can still expose its volatile replacement.
A power loss resolves the namespace to one permitted durable result.
Model an exact physical borrow independently of selector reachability and allow it to survive local process recovery.
Assume scope is an intact replica under the media contract from study 25 with an exclusive holder whenever it serves.
The model starts at the durable-vote boundary and treats append as an atomic new exact record plus local vote.
Quorum decisions, actual flush calls, lease transport and shared segment layout are outside scope.

## Checks and comparison

- Safety for every power-loss outcome. Keep the exact base and the suffix each selectable generation needs.
- Exact read custody. Preserve live pins against their original bytes even across recovery and a later selector switch.
- Bound on unsettled recovery choices. Permit one unresolved selector switch per journal.
- Compare an exact predecessor-bound receipt with revalidating a forward prepared cut against the current closure.
- Compare serving after exact reopen with waiting for selector durability, and exact reclamation with draining all reads before another publication.
- Exhibit a write after warm reopening that survives fallback, a pinned old base alongside reclamation of an intermediate base, and recovery after distinct published generations survive successive power losses.
- Falsify by treating a warm name as durable, dropping a still-live physical borrow, publishing a stale candidate without revalidation, and stacking unbarriered publications while protecting only two endpoints.

## Tool and report

Run the negative controls before intact checks.
Use TLC 2.19 with one worker and a 512 MiB heap and Lean 4.35.0 with the study's toolchain file.
Record bounds, shortest traces, unconditional theorems within the model, and the assumptions needed by the media implementation.
Classify service and compaction witnesses as reachability results.
