# Study 28 report · Ordered application and fresh receipts

2026-11-22

## Verdict

A quorum chooses the order of commands.
The stream reducer decides the result at each chosen group position.
Check the current writer grant, expected stream LSN, and recovery and retention budgets at that application point.
A refused command has one recorded outcome and leaves the stream state unchanged.
It consumes a group command position.
A successful append advances the stream LSN.

A successful reply carries the exact request and its deterministic result from the chosen position.
A later fence or retirement leaves that earlier result valid.
The reference read path chooses and applies a marker for the exact invocation.
The cut at that marker stays defined as the group history advances.
Producing the result can replay a certified prefix or use its equivalent materialized state.
The requirement is the exact ordered decision.

## Bounded results

The six safety laws hold in 6,665 distinct states with two proposed commands and 158,216 with three.
Both bounds permit two writer grants, retirement, two candidate append positions and two read invocation identities.
Proposal, choice, application and reply delivery interleave independently within their guards.
The bounded model treats group agreement as an input.

| Amendment | Weakening | Shortest bounded failure |
| --- | --- | --- |
| A98 | `reply_on_choice` | Propose an append, choose it, then reply without an applied result. Three transitions. A further three-transition trace acknowledges a command that the reducer would refuse. |
| A99 | `check_on_submit` | Submit retirement and then an append while its writer is still installed. Apply retirement and let the cached grant authorize the later stale command. Six transitions. Replacing retirement with a higher writer grant also fails in six transitions. |
| A99 | `ignore_lsn` | At stream LSN 0, choose a command expecting LSN 1 and append it to the next position anyway. Three transitions. |
| A100 | `replay_old_marker` | Invoke a read, choose and apply its marker, then invoke a different read and answer it using the earlier marker. Six transitions. |
| A101 | `replay_old_marker` | Add a chosen append after the old marker and before the fresh invocation. The earlier marker misses that commit. Eight transitions. |
| A101 | `read_lagging_replica` | Apply and acknowledge a write, then invoke a fresh read and return the empty cut from a lagging replica. Six transitions. |

In six transitions the intact candidate chooses and refuses a stale append after a higher writer grant.
In seven it delivers a successful append receipt after retirement for the earlier applied command.
In eight it captures an empty cut on its own marker, applies a concurrent append, and then delivers the original cut.
The last two witnesses record the state at reply delivery so a later change alone cannot satisfy them.
These are reachability results within the stated bounds.

## General proofs

Lean checked fifteen theorems with standard axioms only. [Proofs](OrderedApplication.lean)
The deterministic reducer either stutters or takes a step in the imported logical kernel.
Every step of that kernel has a successful command expression.
The projection covers arbitrary chosen traces and carries the kernel's bounds on retained and recoverable stream records.
Each input command has exactly one result at its original group position.
Replaying an extension preserves already computed outcomes.
Composing that result with fixed-group prefix agreement makes replicas agree on both the exact command and its result at any shared certified position.

An applied append produces the exact stream position, epoch and payload of its request under the installed grant.
An append from a superseded writer leaves the state untouched.
An applied read marker returns the cut and nonce of that decision.
If a marker is chosen inside its invocation interval and the reply observes a certified prefix through that marker, its read result survives arbitrary later prefix extensions.
The invocation and reply positions are premises of the general theorem.
The finite model checks those premises against its live trace.

Removing the current writer check, removing the expected LSN check, or changing the read nonce fails the corresponding Lean proof.

## Remaining obligations

The reducer is a reference specification for the existing kernel steps.
It assumes the same starting image and limits on every replay.
Checkpoint receipts, handoff, and extent custody retain their separate validation obligations.
The pure projection establishes stream bounds.
Group command history, including refusals and markers, needs its own admission and compaction budget.
Receipt delivery remains subject to the authorized invocation and any retained outcome witness allowed by the retirement and erasure contract.

The ordered marker defines freshness with one extra group command.
A read-index path needs independent evidence that its quorum round is fresh for the invocation, it knows the current chosen cut, and the serving replica applies through that cut.
The fixed-group refinement establishes this relation under explicit activation, scope and cut assumptions. [Read-index refinement](../29-read-index/report.md)
The finite oracle counts an effective command once the group chooses it.
Cut coverage therefore includes choices the serving replica has yet to learn or apply.
Serving the actual snapshot also needs the atomic root and replay reservation.
Authentication, outcome retention for retries, live voter reconfiguration and progress under eventual leadership remain separate obligations.

Apply [A98–A101](../amendments.md#study-28--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner retains exact configurations, commands and counterexamples under the ignored `.results` directory.
Set `LOGKEEPER_TLC_SCRATCH` to move the state queue to an existing directory on a volume with more room.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/28-ordered-application/run.py
```
