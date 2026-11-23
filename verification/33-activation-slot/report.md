# Study 33 report · Recover the successor activation slot

2026-11-22

## Verdict

Choose the successor's exact seed in one target-scoped consensus slot.
Its recovery rule is the ordinary durable prepare rule specialized to a single value.
Every higher ballot inherits the highest accepted report, including a vote whose coordinator never learned its result.
A stage receipt conveys readiness to propose.
Publication requires exact quorum evidence for the chosen seed and access to its image.

The data-bearing candidate binds each accept to exact durable local bytes.
That local binding makes any reported accepted seed recoverable from a surviving owner.
A reference-bearing candidate can instead protect the exact image independently before recording any reference vote.
An unbacked vote can choose a value that the recovery path is bound to inherit after the image is lost.
A higher promise leaves the prior accepted metadata and its physical binding live.

An accepted donor can fail between prepare and materialization.
A new ballot and a fresh quorum can safely recapture the slot.
Any hidden prior choice remains in its evidence.
A lost singleton that never reached quorum can be omitted if the fresh quorum has no accepted reports.

After one AZ loss, both surviving voters can retain distinct unchosen images.
Reserve room to stage the higher-ranked image at the lower-ranked voter while its accepted binding stays protected.
Only the valid durable replacement switches that binding.

## Bounded comparison

Use one authorized intent, one fixed target slot, two exact seeds, and three target voters in distinct AZs.
General schedules have two ballots and allow one zone to fail at any point.
The focused schedules bound which earlier votes are in flight and provide a final stable term after the fault.
The three-ballot cases use the extra term to exercise loss after prepare or reconcile divergent surviving holders.

| Candidate or schedule | Distinct states | Checked result |
| --- | ---: | --- |
| Data-bearing votes, general | 185,448 | All five safety laws hold. |
| Independently protected reference, general | 713,928 | All five safety laws hold. |
| Data-bearing votes, hidden choice before loss | 366 | Safety and conditional publication progress hold. |
| Protected references, hidden choice before loss | 1,118 | Safety and conditional publication progress hold. |
| Data-bearing votes, lost singleton | 158 | Safety and conditional publication progress hold. |
| Data-bearing votes, donor loss after prepare | 1,562 | Safety and conditional publication progress hold with a fresh ballot. |
| Data-bearing votes, two surviving distinct bindings | 378 | Safety and conditional publication progress hold with replacement room. |

The safety laws cover agreement, publication, exact accepted backing, recovery from a current majority, and the configured staging limit.
The data-bearing recovery check looks for an exact local copy in every current majority.
The reference check looks for a reachable protected copy in the backing domain.
The temporal property begins when the modeled fault occurs.
The focused cases give weak fairness to control work, staging and publication, reserve space for the needed copies in the passing cases, and let the last term complete with one permanent AZ loss.
The general schedules check safety without a fair-leader assumption.

The general reference run initially explored historical readiness and recovery observations unused by its laws.
That version completed once, then exceeded the 60-second limit on a concurrent rerun.
The final model records those observations only in schedules that inspect them.
The general vote, stage, collection, and outage choices remain the same.

| Amendment | Weakening | Checked failure |
| --- | --- | --- |
| A121 | `ignore_accepted` | A later target ballot ignores the already chosen seed and chooses another in sixteen transitions. |
| A121 | `publish_readiness` | Publish a staged image with no authoritative choice in eight transitions. |
| A122 | `metadata` | Choose a seed with no protected target copy in six transitions. A separate fair run loses the only readable image, adopts its surviving metadata, and never publishes. |
| A122 | `cached_ready` | Stage, collect, and vote using the old receipt in seven transitions. |
| A123 | `promise_releases_vote` | Promise a higher ballot and collect a still-reported accepted image in nine transitions. |
| A124 | `no_new_ballot_after_loss` | Keep the prepared term after its speculative donor fails. Recovery stays blocked under the stated fairness. |
| A125 | One image per recovering voter | With two distinct accepted bindings and the third AZ down, the lower-ranked voter cannot stage the chosen candidate in the new term. The reachable quorum cannot finish. |

The bounded programs recover a previously unreported target choice after AZ loss in eighteen transitions and safely omit an absent earlier singleton in seventeen.
They replace a prepared but unreadable candidate through a fresh ballot in twenty-one transitions.
They replace the lower-ranked live binding, publish the higher image, and reclaim the unused copy in twenty-three.
These witnesses exhibit possible executions within the stated bounds.

## General proofs

Lean checked ten theorems with standard axioms only. [Proofs](ActivationSlot.lean)
Two exact certificates for the single slot have the same seed.
An empty prepare quorum excludes every earlier choice.
After a seed is chosen, every acceptance at that ballot or any later ballot uses the same value.
These claims derive from the earlier prefix agreement proof with an exact single-entry history.

The data-bearing acceptor proof composes durable rank history with the exact local media binding.
Staging, preparing, accepting, collecting, and restarting preserve the latest accepted image on any intact device.
A higher promise leaves that image resident.
Every current recovery majority intersects a previously chosen write quorum at a reachable voter whose latest exact binding still supplies the chosen seed.
The result applies to arbitrary finite acceptor histories and fixed voter lists under the stated projection and consensus premises.
For publication, a recovered reply has the same exact chosen value as the earlier reply, even if the learner lost its local result.
The composition theorem binds the target image to the ranked predecessor cut.
Every target recovery majority can obtain the published image, whose decoded history contains every predecessor choice, including choices learned after closure.

Four Lean controls fail when a vote accepts absent bytes, collection ignores the latest binding, publication skips the choice certificate, or the installed image matches only the length of the recovered history.

## Developer cost

Keep the successor intent and slot identity fixed across every retry.
Stage any eligible exact proposal, then use the highest accepted prepare report if one exists.
For local backing, copy the required image to a voter before accepting it there.
For independent backing, register and protect the exact dependency set before any metadata accept and reconcile that registration by its physical authority.
Read the exact installed outcome from the slot after reply loss.

## Remaining obligations

The test starts with an authorized intent, exact eligible seed descriptors, and a fixed certified target quorum family.
The finite runs model the target, while the preceding study models the predecessor fence and ranked cut.
The composition proof assumes the exact decoding of the installed image.
Authentication, durable slot allocation, competing valid intent proposals, and local application of the exact installed state remain to be refined.
Membership changes during a pending target slot need an explicit transfer of its promises, accepted bindings, and installation result.
The [pending activation study](../34-pending-activation/report.md) compares that transfer with ordering inward activation in an existing target journal.

The general backing proof covers the local data-bearing path.
The independently held referent is checked in TLC, with its registered quorum protection held for the life of this model.
Its registration, release, and exact physical provider adapter still use the separate custody contracts.
The staging bound counts images of equal modeled size.
Real budgets must charge bytes and dependency graphs, account for shared extents where safe, and track other live borrows outside this slot.

Apply [A121–A125](../amendments.md#study-33--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner saves exact commands, checker traces, and mutation failures under the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/33-activation-slot/run.py
```
