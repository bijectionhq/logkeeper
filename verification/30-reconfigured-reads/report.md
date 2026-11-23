# Study 30 report · Reads across voter reconfiguration

2026-11-22

## Verdict

A read during joint membership can use a majority of either constituent while writes require both.
Each such read intersects every joint write quorum.
The cheaper read quorum changes finalization.
Persist fences on both constituencies before the successor opens, because either one could otherwise still supply a stale read quorum.
Dual-majority joint reads require a fence that blocks one side, and the successor majority suffices for that purpose.
Joint reads restricted to the successor side also close under that same successor-majority fence.
The membership decision and exact successor installation retain their own quorum rules.

An already valid round can carry its immutable coverage floor across voter changes in the same logical replica-group lineage.
Reserve an exact authorized applied snapshot that covers that floor.
This can use a newer root and cut than the observed position.
If the successor discarded the speculative tail that made the old floor too high, start a fresh round under the new scope.
An admitted reservation survives the change with its original root and suffix.

## Bounded results

Each configuration has three voters.
The two configurations share two voter identities.
The five safety laws cover scoped quorum evidence, prior promises and choices, the exact snapshot basis, and the returned cut.

| Candidate | Command bound | Distinct states | Result |
| --- | ---: | ---: | --- |
| Joint change with dual reads | 1 | 472,684 | Safety holds over the general schedule. |
| Joint change with one-side reads | 1 | 532,502 | Safety holds over the general schedule with both fences. |
| Joint change with successor-side reads | 1 | 598,916 | Safety holds over the general schedule with the successor-side fence. |
| Sealed change | 1 | 131,088 | Safety holds over the general schedule. |
| Joint change with dual reads | 2 | 2,120,241 | Safety holds over the focused schedule. |
| Require a current-scope round at reservation | 1 | 323,998 | Safety holds. The earlier-round witness is excluded. |
| Reserve exactly the observed position | 1 | 419,884 | Safety holds. The overtaken-floor witness is excluded. |

The unrestricted two-command run exceeded the 60-second checker limit.
The focused depth-two schedule fixes the participant sets for the changes and writes.
Replica catch-up, sampling, checkpoint changes and reservation interleavings remain in that search.

| Amendment | Weakening | Shortest bounded failure |
| --- | --- | --- |
| A106 | `mix_scopes` | Combine replies from different scoped voter states. The resulting receipt fails the exact quorum rule in six transitions. |
| A107 | `fence_new_only` | Enable one-side joint reads, then finalize by fencing only a new majority. A stale joint round certifies after finalization in seven transitions. Its floor misses a preexisting choice in eight, and an outdated snapshot is actually returned in ten. |
| A108 | `ignore_observed_floor` | Start a valid read after a remote choice and answer from a serving replica with an earlier applied cut. Eight transitions. |
| A109 | `forget_hold` | Reserve a basis and lose its protection at successor adoption. Eight transitions. |
| A109 | `collect_pinned_root` | Reserve a root, publish a successor root, and collect the older root while the reservation still needs it. Ten transitions. |

The general carry witness begins in the old configuration, assembles replies from that scope after finalization, and reserves at a root newer than the observed floor in twelve transitions.
Focused witnesses finish the round before the transition and carry it across joint or sealed replacement, also in twelve transitions.
It also serves an earlier nonempty pinned view after adoption and publication of a newer root in twelve.
It can abandon a speculative floor and retry to return the successor's actual empty cut in fifteen.
One-side joint reads can complete without a dual read quorum in eight transitions.
The successor-only policy also serves in eight transitions with a majority of the successor that lacks a predecessor majority.
These are reachability results.

## General proofs

Lean checked eleven theorems with standard axioms only. [Proofs](ReconfiguredReads.lean)
One constituent majority intersects the exact opening coverage held by a joint quorum.
This gives a verified opening floor under the same-scope observation and monotonicity premises of the read-index proof.
The proof also constructs a new-side durable fence and an old-side reader with disjoint voters.
Fencing both constituents blocks every either-side joint read.
A successor-side fence blocks dual reads and reads restricted to the successor.

Both a stable round and a joint round produce the same kind of verified floor, bound to its original invocation.
An exact applied snapshot covering that floor has a logical cut inside the invocation interval, no later than reservation.
The proof uses the stream reducer to map that group's command position to the exact stream cut and checks the authorized writer at the chosen snapshot.
The existing atomic reservation step then acquires that root and any needed suffix at that cut.
Once reserved, the original basis remains protected through later changes until its own effective release.

Three Lean controls weaken the required fence, the applied coverage check, or the invocation binding.
Each fails its designated proof obligation.

## Remaining obligations

The model assumes an authorized membership transition and exact installation of the current chosen history.
It does not prove the full dynamic consensus protocol that supplies that decision.
The floor carry proof stays within one group, stream incarnation and placement and uses a common exact chosen history.
A cross-placement carry needs the corresponding handoff certificate and proof.

The reservation proof combines an admitted root and replay range under the preceding custody model.
Deploying that step requires a concrete atomic protection path and correct transfer of its holds.
If reservation is itself chosen as a command at the current group head, that command can supply its own ordered read cut.
A path without an ordered command per read must instead establish independent custody against the certified applied basis.
The proof explains the binding needed at that interface.
It leaves physical placement, durable capacity, read batching, protection under crashes, and progress under repeated reconfiguration for their own proofs.
The reservation model serves an open stream.
Terminal retirement retains its separate fence on new admissions and effective release for admitted operations.
The next study models standing physical custody for the no-command path and compares retirement deadlines. [Standing snapshot custody](../31-standing-custody/report.md)

Apply [A106–A109](../amendments.md#study-30--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner keeps exact configurations, commands and counterexamples under the ignored `.results` directory.
Set `LOGKEEPER_TLC_SCRATCH` to an existing directory with room for the verifier's queues.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/30-reconfigured-reads/run.py
```
