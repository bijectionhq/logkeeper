# Study 32 report · Configuration closure and successor installation

2026-11-22

## Verdict

Recover from the exact accepted state captured by a durable, scope-specific fence.
Rank each report by accepted ballot and logical position.
The coordinator's learned history can lag behind actual choices.
Every old quorum that can still assemble intersects at least one frozen report.
A vote recorded before that voter fenced can still combine with a delayed vote at an unfenced voter.
Such a completion can only confirm a prefix already covered by the recovered image.
Fencing every old voter excludes even late quorum completion, but can prevent reconfiguration during one-AZ loss.

Select one successor intent independently of the fence.
Two joint fence quorums can each block every write quorum and still be disjoint from each other.
Restricting intent votes to one constituency gives intersection, but irrevocably splitting them across three contenders can prevent every contender from proceeding.

Keep the authorized successor fixed while allowing recovery to reselect its proposed cut before activation.
A speculative tail can be the highest report and still have one accessible copy.
Losing that copy can strand a protocol that binds the first candidate irrevocably.
Choose one exact successor seed under its own authority after durable installation.
An abandoned candidate's staged copies need separate settlement.

## Bounded comparison

The closure model has four or five replica identities, three AZs, and up to three successive scopes.
It models one immutable proposal chain per scope and separates physical votes from receipt delivery.
The general cases use up to one record.
The unrestricted joint state space exceeded 60 seconds.
The focused joint comparison fixes the fence and install cohort, suppresses receipt learning, and retains concurrent old and joint vote, seal, copy, and activate interleavings.
The outage cases begin with a hidden choice and one named AZ unavailable.

| Candidate | Distinct states | Result |
| --- | ---: | --- |
| Sealed change | 8,186 | Six safety laws hold. |
| Joint change with focused cohort | 3,237 | Six safety laws hold. |
| Fence every voter | 1,769 | Six safety laws and no late quorum completion hold. |
| Carry a hidden prefix across two sealed changes | 132,512 | Six safety laws hold. |
| Joint change with AZ 1, 2, or 3 unavailable | 196 / 376 / 188 | Six safety laws and eventual activation hold in each case. |
| Ordered successor intent with either fence constituency | 109 | At most one successor activates. |
| Sticky intent on the successor constituency | 496 | At most one successor activates. |
| Ordered successor intent with one AZ unavailable | 19 | Eventual activation holds under weak fairness. |
| Recapture candidate with one prior chosen record | 1,668 | Agreement, unique recoverable installation, and eventual activation hold. |
| Recapture candidate with two prior chosen records | 68 | The same properties hold, including preservation of the longer chosen cut. |

The recapture model starts after an authorized source fence.
One AZ can fail before or after capture or staging.
Two old voters can still return their exact captured prefix.
The target stages and chooses one exact seed under its own quorum.
The temporal checks give weak fairness to gathering the available reports, staging, and installation in their respective models.

| Amendment | Weakening | Shortest bounded failure |
| --- | --- | --- |
| A115 | `learned_only` | Lose a chosen command from the seal in six transitions. A successor chooses a conflicting command in twelve. |
| A116 | `sample_only` | Collect a quorum of reports without fencing its voters. A later old quorum extends beyond that image in six transitions. |
| A116 | `volatile_fence` | Restart a durably reported voter with its fence forgotten, then finish a quorum beyond the seal in seven transitions. |
| A116 | `wrong_membership` | Close using the successor's membership. Its reports can omit a choice supported by a disjoint predecessor majority in six transitions. |
| A117 | `install_by_length` | Stage a same-length wrong payload and activate without any exact installed majority in eight transitions. |
| A117 | `drop_inherited_base` | Forget the installed basis when an intermediate scope has no longer vote, then activate the next scope in fourteen transitions. |
| A118 | `sticky` with either constituency | Two disjoint joint fences activate different successors in eight transitions. |
| A118 | `sticky` with successor-only fences | Three irrevocable per-voter intent choices split the target constituency. A fair execution cannot activate any successor. |
| A119 | `first_cut` | Bind the longer speculative cut, then permanently lose its only accessible copy. A fair execution leaves the transition unfinished. |
| A120 | `multiple_seeds` | Stage two valid candidates under one intent, install both, then choose an extension of the shorter one that diverges from the longer seed. Nine transitions. |

The all-voter fence also has a fair execution that cannot activate after one AZ loss.
An intersecting fence can close under the same loss.
The bounded acceptance cases recover an already chosen unlearned write and deliver its receipt after activation in seven transitions.
A distinct nine-transition witness chooses the seed in the successor before a delayed old vote completes the old quorum.
The first successor preserves the same command, which survives a second change in twelve transitions.
Joint and final scopes both choose new writes with one AZ unavailable in eighteen transitions.
After loss of an unchosen longer cut's only copy, a reachable quorum recaptures and installs the shorter choice in six transitions.

## General proofs

Lean checked twelve theorems with standard axioms only. [Proofs](ConfigurationClosure.lean)
Local scoped traces compose the existing accepted-rank proof with an immutable scope fence.
A fenced voter's scoped accepted state and reports survive restart and delayed assembly.
A fenced majority excludes any old majority consisting entirely of new votes.
For any earlier quorum, its intersection report dominates its vote.
An equal-ballot winner lies farther along the same chain.
A higher-ballot winner inherits the earlier quorum prefix by the fixed-group agreement theorem.
The proof covers any qualifying old quorum, including one learned after the fence.

A handoff inherits the already installed basis and every old choice.
Any finite sequence of consecutive handoffs preserves this evidence.
Every later recovery majority has an exact replica of the installed basis containing an earlier chosen prefix.
Later decisions agree with all earlier decisions.
For a joint scope, the proof applies to a constituency covered by every ordinary prepare and write quorum in that scope.

One fixed constituency together with immutable per-voter intent binding yields at most one successor.
A separate theorem exhibits two disjoint sets that each block every dual-majority joint write.
Three proof controls fail when a frozen scope is allowed to operate, an empty report set forgets the installed basis, or the target installation counts unrelated bytes.

## Remaining obligations

The proof models a chain of authorized handoffs.
It derives what any valid ranked certificate must preserve and how to carry that result through successive installations.
Authentication, a real distributed choice for the intent and the seed, pending attempt recovery after lost replies, and the composition of ordinary prepares with membership commands still need refinement.
The reselecting model uses a fixed old ballot for its data and one fault over one transfer.
It leaves repeated outages, competing scopes, durable staging quotas, compaction of exact closure reports, and eventual repair for further verification.
The history list is logical. Production can use a certified checkpoint and retained suffix to establish equivalent recovery coverage under the trim contract.
The brief's physical stop deadline is stronger than agreement of old evidence with a sealed prefix.
Receipt handling at a real endpoint must retain the difference between previously chosen evidence and a new extension.
The [activation slot study](../33-activation-slot/report.md) models choosing and recovering the target seed under a fixed certified target family.

RTDB Multi's Allium contract uses ranked recovery and binds durable journal identity independently of its serving process.
The incumbent Allium prose says closure prevents a quorum from forming for earlier writes in flight.
The modeled timing trace shows the limitation of that statement if the quorum may include a previously durable vote.
The design retains the exact history guarantee, with the stricter physical timing policy left for product review.
[RTDB Multi seal contract](https://github.com/bijectionhq/rtdb/blob/fc6da3a4a3/allium/rtdb-multi.allium#L465-L474)

Apply [A115–A120](../amendments.md#study-32--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, counterexamples, and proof mutation diagnostics under the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/32-configuration-closure/run.py
```
