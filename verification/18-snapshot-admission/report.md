# Study 18 report · Snapshot admission under checkpoint publication

2026-11-22

## Verdict

Capture the head for an ordinary latest read in the same ordered decision that reserves the current certified root and its nonempty WAL suffix.
The decision can share a registered root custody reference.
The asynchronous read can then proceed at the reserved cut across publication and handoff.
An explicit historical cut still requires a basis that covers it.
The two sides of disposal authorization are ordered on the custody identity, so a delayed publication can only use a still-live registration.

## TLC safety and temporal comparison

The six baseline safety laws and conditional completion property hold across 3,188 distinct states with maximum head 2 and retention capacity 1, and 47,238 states with maximum head 3 and capacity 2.
Each run allows one request, a move, separate authorization and arrival of root disposal, and changes to reader connectivity.
The liveness property uses weak fairness for the install, reserve and fetch actions, and assumes eventually stable reader connectivity.

| Amendment | Variant | Counterexample |
| --- | --- | --- |
| A53 | `fixed_then_reserve` | Request at genesis → commit → register at the new cut → publish. Four transitions reach a pending cut the latest-root gate can no longer serve. TLC also finds a fair stuttering execution with the link up and the pending request unanswered. |
| A53 | `read_live_head` | Request → reserve → commit → answer at the new head. Four transitions. |
| A54 | `before_custody` | Commit and publish with no custody registration. Two transitions. |
| A54 | `accept_old_receipt` | Commit → register → authorize disposal of the staged root → publish using the old registration. Four transitions. |
| A55 | `split_root_hold` | Commit and reserve, then register and publish a newer root. Authorize disposal of the old reserved root. Six transitions. |
| A55 | `split_wal_hold` | Commit and reserve, then register and publish a newer root. Trim past the reservation's nonempty suffix start. Six transitions. |
| A56 | `unfair_fetch` | Reserve the read and leave a continuously enabled fetch unscheduled despite the healthy link. The progress property fails. |
| A56 | Permanent link loss | Remove the stable-connectivity premise. The target installs and can admit, but its protected read never receives the unavailable inputs. |

A nine-transition witness reserves a nonempty suffix at the source and serves at the target after a newer checkpoint and an additional commit.
A seven-transition witness serves an empty suffix after trim has passed its checkpoint.
A twelve-transition witness runs the same handoff program and then reclaims both components of its old basis.
In six transitions a live hold reaches retention capacity before the global head limit, despite a newer published checkpoint.

## General model proofs

Twelve [Lean theorems](SnapshotAdmission.lean) use only standard axioms.
For arbitrary finite traces, the logical registry preserves current and reserved roots, the bounds of every active suffix, and the exact basis of each read until its own effective release.
The model applies to repeated logical installs and multiple concurrent reads.
A latest reservation under an available slot is always constructible without waiting for a checkpoint generation to stop changing.
A latest-only selection at a previously fixed cut stays unavailable once a published start overtakes it, as the published start never decreases.

The nonempty admission program projects to the existing kernel's prepare-and-admit replay program.
Those internal steps have to lower within the same externally ordered reservation.
The root-only theorem reconstructs the certified cut with an empty journal input, independently of the current journal floor.
A held nonempty suffix and bounded retained debt imply a finite upper bound on further commits, even with later checkpoints.
Weakening publication custody, disposal of a held root, or the trim guard fails the matching Lean preservation proof.

## Residue

RTDB's current directory admission for receipted startup already registers checkpoint metadata and replay protection together.
This study generalizes that shape to a Logkeeper recovery cut and its exact custody interest.
The checked models treat registration as trustworthy evidence for the complete immutable graph and assume the actual manifest codec from the checkpoint study's interface.
They do not establish atomic capture across two independently writable authorities.
If a distributed refinement splits the order, it must show an equivalent reservation or fence across the split.
Disposing identity and aliasing are at the level of a root's custody registration.
[Study 19](../19-shared-object-custody/report.md) composes that registration with an exact-version graph model for manifests, forks, and active borrows.

The liveness claim is conditional and bounded in TLC, and the Lean arguments prove availability of the admission step and preservation of its inputs rather than a scheduler theorem.
An admission slot, a capable endpoint, fair scheduling, and eventual access remain premises.
Finite slot and byte accounting, loss or uncertainty of reservation acknowledgments, authenticated provider dispositions, and deadlines that trigger effective cancellation remain refinement work.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/18-snapshot-admission/run.py
```
