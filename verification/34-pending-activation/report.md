# Study 34 report · Pending activation across target reconfiguration

2026-11-22

## Verdict

Use the existing target group's ordered journal to decide inward activation when that group already has a serving authority.
Voter replacement recovers the ranked command prefix, including an accepted activation the learner has not applied or reported.
Carrying a separate pending slot also works within the check when it transfers the exact accepted binding and its physical coverage.
That alternative needs a separate recovery and publication step in the new scope.

Decide a replayed command using the revision and exact live grant at its original ordered position.
Receiving voters can be in a later physical family while replaying that earlier decision.
A packet first ordered after the revision change must meet the current revision and grant checks.
The new family verifies the exact physical coverage of the recovered view before it serves.

Target group repair can proceed while an incoming reservation awaits data, provided the recovered journal has no command depending on that data.
Requiring all such reservations to resolve first can prevent target repair indefinitely.
A bootstrap slot that already has a certified target family can still use the fixed-family protocol.
The wait comparison checks the case with a ready seed and a reachable quorum.

## Bounded comparison

The transfer model uses one authorized intent, up to one old and one new proposal, four durable identities, one voter replacement, and at most one AZ loss.
The general cases interleave proposals, old votes, fences, copying, membership installation and publication.
Each hidden-choice case starts with an unreported old quorum and an unavailable external source.
The unready cases start with the exact reservation live and no proposal dependent on the missing source data.

| Candidate or schedule | Distinct states | Checked result |
| --- | ---: | --- |
| Existing ordered journal, general | 41,648 | Six safety laws hold. |
| Separate pending slot carried exactly, general | 58,704 | Six safety laws hold. |
| Existing journal, old hidden choice with AZ 1, 2, or 3 absent | 24 / 24 / 12 | Safety and eventual publication in the new scope hold. |
| Separate slot, old hidden choice with AZ 1, 2, or 3 absent | 36 / 36 / 18 | Safety and eventual publication in the new scope hold. |
| Either transfer, no proposal and source unavailable | 7 each | Eventual target voter replacement holds. |
| Wait for installation, hidden but ready choice with one AZ absent | 32 | Safety and eventual publication in the new scope hold. |
| Historical replay, up to three chosen commands | 1,823 | Learner state and outcomes match the ordered oracle. |
| Historical replay, up to four chosen commands | 19,311 | Learner state and outcomes match the ordered oracle. |

The publication progress checks assume a reachable predecessor and successor majority, preserved exact copies for the dependent cut, and weak fairness for fencing, copy, installation and publication.
The unready-case property requires voter replacement.
The incoming installation remains pending on its own data.

| Amendment | Weakening | Checked failure |
| --- | --- | --- |
| A126 | `learned_only` | Recover an empty learned view over a real old choice in six transitions. The new scope chooses a conflicting image in twelve. |
| A126 | `forget_slot` | Install successor membership with the pending binding erased in eight transitions. A conflicting activation is chosen in fourteen. |
| A127 | `skip_install_copy` | Change membership without any current recoverable copy of the inherited image in six transitions. |
| A127 | `stale_ready` | Use an older scope's readiness to vote for a seed without its target copies in nine transitions. |
| A127 | `publish_stale` | Enable serving from an old choice before the carried slot has a current decision in ten transitions. |
| A128 | `replay_current_revision` | An older preparation replays differently in three transitions. A separate outcome check changes an earlier activation result in five. |
| A128 | `ignore_stage_revision` | Treat a delayed old envelope as a currently valid one in six transitions. |
| A129 | `reuse_dead_ready` | Use a readiness receipt after discarding its exact grant in six transitions. |
| A130 | Wait with the incoming image unavailable | A fair execution keeps a reachable target family from switching forever. |

The existing journal moves a merely accepted command and serves its result in nine transitions.
The carried-slot candidate does so in eleven.
They recover and serve the previously unreported choice after old target storage settles in eight and ten transitions respectively, with the external source unavailable.
The existing journal replaces a voter before incoming materialization in four transitions.
The historical model replays an older successful activation after the physical switch in five transitions and refuses a delayed older packet ordered after the switch in six.
These are reachability results and supply no latency comparison.

## General proofs

Lean checked eleven theorems with standard axioms only. [Proofs](PendingActivation.lean)
Every successful activation uses the exact intent, historical ordered revision, and live grant in the reducer's state.
The reducer projects to a single-assignment slot and expresses an eligible installation with one command.
Replay over arbitrary extensions preserves every earlier outcome and any already installed ticket.
A discarded attempt stays spent through later commands and revision changes.

The composition theorem applies ranked closure to the target journal's old voters.
Every target recovery majority intersects an exact installed quorum at a replica with the recovered command image.
Replaying that image preserves earlier outcomes and the installed ticket, even if the result had not reached its caller before the change.
Exact physical coverage of that image is a premise of the theorem.

Four Lean controls fail when activation ignores its ordered revision or live grant, or when replacement forgets an installed ticket or spent fence.

## Developer cost

For an existing target, durably register exact readiness and submit the activation through its replica group's existing command order.
Reconcile a lost result at the chosen command position or with its retained outcome.
On voter replacement, recover and materialize the journal prefix and the dependencies needed to serve it.

A separate slot needs equivalent accepted-state recovery and an exact current physical handoff, even if a caller has never seen an outcome.
The fixed-family bootstrap case retains that interface when the replacement family has no already serving control journal.

## Remaining obligations

The finite model uses one old accepted proposal and one membership change.
The proof covers arbitrary reducer histories with ranked closure and exact target quorum installation as premises.
The replay reducer uses recorded authenticated evidence for historical admission.
The implementation must ensure that this evidence was validated and that the resulting live physical dependencies have transferred.
The [compaction study](../35-attempt-compaction/report.md) checks bounded spent markers and separate physical obligations.
Byte quotas for abandoned staging and repeated target reconfiguration need composition with the existing custody protocols.
The bootstrap wait result requires a reachable quorum through activation.

Apply [A126–A130](../amendments.md#study-34--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, traces and mutation diagnostics in the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/34-pending-activation/run.py
```
