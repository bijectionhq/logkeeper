# Study 76 · Replace the writer inside its existing journal placement

2026-11-23

## Verdict

A worker replacement changes the ordered holder grant within the installed journal.
It preserves the placement, paid window and cursor, committed prefix, checkpoint and replay reservations, and pending move bookkeeping.
A worker inherits the exact cut and reaches it before serving transactions.
An eligible replacement can make progress while the incumbent worker, directory, and fresh allocation service are unavailable.

An authenticated nomination names the lineage, exact expected old holder, and the new holder.
The group's ordered state checks the current holder, same placement, and strictly higher epoch.
A generic stream fence cannot bypass nomination.
The installed source also requires authenticated evidence for the dedicated checkpoint publication command.

Routing publication can follow these choices.
An enrolled deployment still needs a usable route to its group, a functioning current quorum, an eligible candidate, and verified recovery inputs.
Local replacement uses existing stage and append headroom.
Cross-group migration retains its separate funded seal and installed-cut contract.

## Bounded comparison

[WorkerHandoff.tla](WorkerHandoff.tla) uses one installed journal, one candidate, the old writer's last append, and one existing paid window.
TLC checked eight distinct states for the safety baseline and eight for the temporal comparison.
The temporal baseline gives weak fairness to an eligible grant, exact catch-up, and the next append.
The four-transition witness commits the old worker's last record, selects the successor, catches up to the extended cut, and commits through the original window.

| Weakening or alternate dependency | Result |
| --- | --- |
| Accept the old epoch after installing the replacement | Replace the holder and accept a delayed old append in two transitions. |
| Let the successor serve early | Replace the holder, then start serving while the certified cut has not been applied. Two transitions. |
| Omit nomination eligibility | Install an ineligible worker in one transition. |
| Require directory publication | With its directory unavailable, the eligible successor cannot progress despite the original recoverable journal. |
| Require the incumbent worker to release authority | The authorized path stalls while the old worker is unavailable. |
| Require a fresh physical migration | The inherited window has usable room, but the eligible successor stalls while the new allocator is unavailable. |

## General proofs

[StableGrant.lean](StableGrant.lean) checks eleven theorems over the augmented source reducer from Study 75.
A verified same-placement replacement applies the real ordered fence, records the higher epoch, and returns the exact committed cut.
It preserves the window and source books, all physical window bindings, pending plan and seal slots, and all read reservations.
An unverified nomination and a generic fence are refused.
Another nomination based on the superseded writer cannot displace the first successor.
An old writer fails even with the still-paid physical window and exact original cursor.
The nominated successor's eligible append uses that same window and advances only its next LSN and spent bytes under the existing funded append rule.
Exact retained append receipt lookup is unchanged by worker replacement.
The current writer can order a certified checkpoint through the installed group without moving its window.
An unverified or generic checkpoint command cannot apply the publication effect.

## Design changes beyond the local proof

The [baseline decisions](../design.md#baseline-decisions) specify how the earlier tradeoffs resolve together.
The group orders effective eligibility, grants, and checkpoint publication.
The directory locates enrolled groups and publishes discovery hints.
State watches restart from a certified snapshot after their cursor falls behind retention.
Exact event history is a separately specified service contract.
Retirement closes fresh invocations, while exact disposition governs physical erasure.
Fresh degraded work spends the current one-AZ allowance until full repair.
Separate control and repair reserves protect foreground work from finite unsettled debt.
The default shared tier provides content and authority isolation and exposes shared contention.
A qualified effect protocol at the original custodian gates physical creation and reclamation.
These choices use the constraints previously established in Studies 02, 03, 04, 09, 17, 31, 43, 58, and 67.

## Amendments

[A299–A302](../amendments.md#study-76--2026-11-23) separate writer and placement authority, constrain the ordered nomination, and put authoritative state and proof-bearing checkpoint publication in the journal.

## Acceptance coverage

- P137–P139. Replace an authenticated worker in the same placement during the modeled outages, return the exact cut, keep existing paid window and cursor, refuse a stale writer, and allow the caught-up successor to append.
- P140–P141. The augmented reducer can replay the ordered grant using its attached nomination.
  Discovery of the original group, portable grant reconciliation in RTDB Multi, and exact certified checkpoint publication across a directory outage still need integration-level refinement.

## Residue

The finite outage model holds the installed journal quorum, candidate eligibility, and recovery inputs available.
It abstracts old-holder disconnection from an already-delivered stale append.
The general reducer assumes authenticated ordered nomination, installed group authority, and exact historical evidence.
RTDB Multi's current target spec uses a directory CAS in `Claim` and adds a loglet for that epoch.
A production integration must transfer effective eligibility, same-placement grant, and checkpoint authority to the installed journal and prove RTDB catch-up and history compatibility.
The authorized checkpoint wrapper checks the evidence predicate and original ordered decision.
Concrete certificate construction and atomic binding of the exact checkpoint dependencies remain separate evidence.
Actual scheduling, capacity forecasts, and failover latency need qualification.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records exact commands, configurations, theorem checks, and counterexample traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/76-stable-writer-handoff/run.py
```
