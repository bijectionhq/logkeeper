# Logkeeper architecture decision

2026-11-23

Use stable logical journal groups for the ordinary path.
A worker replacement changes the ordered writer grant.
A voter replacement changes membership while preserving the group's exact recoverable state.
A true transfer to another independently ordering group remains supported through a funded source seal and certified destination installation.
Directory discovery, capacity planning, checkpoint production, and storage reclamation remain separate responsibilities.
A funded group with a current quorum, the required recovery inputs and a usable route can serve existing deployments through the failure of a separate regional decision service.
The product owner delegated that choice.
L01 and L27 make the boundary of installed-authority service explicit.

A regional capacity authority remains a structural alternative for funding physical moves.
Its outage may block fresh reservations.
It cannot be required to validate an already installed continuation during ordinary operation.
A separate regional append witness fails the chosen foreground contract when it can become unreachable independently of the installed data placement.

## Comparison under the shared histories

The eight [independent seeds](seeds.md) and the Study 76 incumbent are compared under the same [H1–H5 schedules](brief.md).
The rows describe expected behavior under each candidate's named premises.
The executable comparisons check selected boundaries of those histories.
Exact group reconfiguration, complete provider inventory, and end-to-end QoS remain joint qualification obligations.

| Candidate | H1 · Healthy sequence | H2 · Lost reply, AZ, worker, and directory | H3 · Opposite moves and pinned source | H4 · Delayed storage effect | H5 · Exhausted evidence or debt |
| --- | --- | --- | --- | --- | --- |
| Incumbent at Study 76 | Payload and result are chosen in one group. Certified checkpoint guards trim. | Reachable quorum and paid window suffice for a writer change. Voter repair uses a certified membership cut. | Ordered independent holds, exact source seal, target install, separate physical settlement. Missing exact install evidence prevents activation. | Journal closes fresh invocations. Exact ticket fence or exact drain and disposition govern erasure. | Local prepaid bounds and recovery dependencies guard admission. A stale watch can reopen a certified checkpoint. |
| A1 · Stable group | One group orders the sequence. | Surviving group returns the exact receipt, fences old work and repairs its voters. | Independent permits with funded peak and retained certificate. Missing source evidence can stall the move before install. | Original custodian fences and disposes its scope. | Bounded receipt state and checkpoint-backed trim. |
| A2 · Sharded ledger | Durable payload receipt precedes ledger choice and barrier. | Exact result when both the ledger quorum and protected data remain reachable. | Atomic vector can coordinate charged scratch. The target retains install evidence, but a new reservation can stall. | Ledger closes admission. Each scope still fences and disposes physically. | Bound exact results and extent proofs across the ledger and pools. |
| A3 · Storage-native | One storage transaction binds head, bytes and result. | Storage authority must expose exact conditional recovery through the AZ loss. | Cross-namespace seal and funded copy or enforceable protected borrow. | Actual store must reject delayed materialization, including staging and restore. | Storage must track bounded pins, exact receipts and reconstructable roots. |
| B1 · Stable group | One group chooses append and orders barriers and trim. | Existing authority and funded slot suffice. Membership change preserves the hidden choice. | Independent pool debits and exact certificates. Pins keep their original charges. | Registered custodians fence effects and attest disposition. | Finite reconciliation window and protected suffixes. |
| B2 · Fixed witness | Protected payload receipts precede choice at the witness. | Fresh service requires the witness, even when protected data survives. | Atomic funding covers stage and retained copies. Local activation can finish, with witness contact still needed for fresh decisions. | Storage scopes and any data-bearing witness scopes settle. | Bound witness receipt and custody debt as well as data queues. |
| C1 · Stable group | One quorum orders the normal operations. | Existing route and local capacity suffice before voter redundancy is restored. | Local exact holds and verified transfer. Failed preparation needs exact terminal evidence. | Each scope enforces closure and attests disposition. | Bound unresolved work and reopen from certified state. |
| C2 · Sharded ledger | Protected payload placement precedes ledger choice. | Both the ledger quorum and exact inputs must survive. | A joint move can use a paid bridge. New joint admission depends on the capacity authority. | Ledger retirement and original storage effect fences. | Ledger and pool quotas remain independent of placement liveness. |
| C3 · Authority cohorts | The current cohort orders append, read cuts and trim. | A surviving cohort replaces the worker. After a cohort change, service follows the installed successor and route. | One seal binds one successor. A relay needs two funded handoffs and additional runway. | Each generation's registered scopes remain accountable until disposition. | Exact records and charges follow the sealed cut. A relay adds custody and replay debt. |

## Executable comparisons

[CapacityOwnership.tla](CapacityOwnership.tla) compares strictly ordered local holds with a single authoritative vector reservation.
Two moves request respectively (2, 1) and (1, 2) units in two pools of capacity four.
Each pool starts with one unit of ordinary use.
A live old reader consumes another unit in the left pool.
Funding remains charged after activation.
The vector authority is assumed to have exclusive reservation rights for each admitted pool.
The local variant uses one strict pool order.
Each continuously enabled operation is weakly fair.
The outage cases start from an already funded or installed prefix with one source route and the coordinator absent, or from empty preparation with only the coordinator absent.

| H3 case | Ordered local pools | Authoritative vector |
| --- | --- | --- |
| Original pin reaches verified disposition | Both moves eventually activate in 34 states. | Same in 23 states. |
| Original pin stays indefinitely | At least one move activates. Activating both would overflow the left pool. Nine states. | Same in seven states. |
| Loss before exact install certificate | Funded move stays inactive. One state. | Same in one state. |
| Loss after exact install certificate | Move activates using retained evidence. Two states. | Same in two states. |
| Separate coordinator down before preparation | At least one move activates with local owners and source authorities available. Nine states. | Fresh reservation stalls. TLC found a temporal counterexample. |

Three deliberate weakenings failed under each owner.
Ignoring the pin overflowed the left pool in two transitions.
Activating from complete funding alone violated exact installation in one transition.
Requiring coordinator and source contact after installation violated progress.
[Study 43](../43-concurrent-capacity/report.md) retains the two-intent wait-cycle counterexample for arbitrary partial acquisition order and the general acyclic-order result.
The new model compares persistent charges and route dependencies.
It abstracts abort recovery, bridge schedules, and distributed implementation of an enforcing vector authority.

[WriterOwnership.tla](WriterOwnership.tla) compares group-local decisions with a required separate witness.
It starts after a hidden durable choice, a rival stage, one AZ loss, and loss of the old worker, directory and fresh allocation.
An eligible replacement has a usable route, exact protected data and a paid slot.
The witness variant locates both the writer grant and fresh barrier decision at the witness.
When that authority was reachable, both designs applied and returned the exact cut in four states each.
With the witness isolated, the group-local variant still completed in four states.
The witness variant stuttered before grant.
Selecting the staged rival as the result violated the exact result property in two transitions for both variants.
The model isolates the extra availability dependency.
[Study 76](../76-stable-writer-handoff/report.md) separately checks the augmented source reducer's old-epoch refusal and funded window reuse.
[Study 77](../77-ordered-worker-eligibility/report.md) now checks the installed source's ordered roster, stale nominations, and the fence on withdrawal.
The RTDB refinement still needs exact authenticated bindings, routing, codec, and durability.
[Study 32](../32-configuration-closure/report.md) checks the old and new voter boundary.

### Storage alternatives under H4

[Study 40](../40-provider-io-closure/report.md) compares two valid mechanisms under the same delayed ticket history.
A provider fence excludes old requests at the durable materialization boundary.
An exact drain closes issuance, verifies every issued operation's terminal state with permanent duplicate suppression, then verifies physical absence.
Both held with fair delivery of queued work.
Only the effect fence completed erasure in the checked schedule where an issued request never arrives and the effect boundary is otherwise reachable.
Logical retirement can complete while physical erasure is pending under either mechanism.
A physically unreachable original scope with missing terminal evidence blocks the erasure receipt.
[Study 58](../58-storage-effect-boundary/report.md) retains the failures of precheck-then-write, key absence as permission, reused revisions, recovery that loses the fence, and missing staging or retained versions.
The native candidate needs an actual primitive and an inventory of its materialization and restore paths.
The selected baseline requires stable closure and exact disposition, with an effect fence for progress when a delivery can remain stalled.

## Acceptance operations at each boundary

For P142, a gateway with an enrolled route asks the installed group for the chosen writer binding.
An eligible replacement submits an authenticated nomination bound to the existing eligibility evidence and expected old holder.
It replays through the returned cut, reconciles the retained request with its original digest and result, then obtains a fresh barrier and appends with its new epoch.
The directory can learn the new binding later.
In the split witness candidate, the worker opens the same protected data and reconciles against the witness's decision.
The same witness must order the writer grant and supply freshness evidence for the barrier.
The loaded data and an old receipt cannot supply those decisions during witness isolation.

For the move program, reserve the full pointwise peak, seal the exact source cut, install that cut and its funding and custody evidence at the target, then activate.
With independent capacity owners the first step collects exact holds in pool order.
With a single enforcing vector owner that step is one vector reservation.
In both cases the installed target completes with its retained evidence and the old custodian independently settles the original pin.
Before the certificate is present, funding alone leaves the receiving target inactive.

For retirement, order closure at the installed group, then track physical erasure to an independently verified receipt.
A terminal provider fence excludes delayed old work before the final absence check.
An exact drain waits for terminal outcomes under closed issuance before making the same absence check.
In either case, the original scope retains its charge until its disposition can be verified.

## Limits and choices

### Limits across candidates

- **Authority transfer.** Without recoverable evidence that an old authority cannot extend, the target cannot distinguish a temporarily unreachable writer from a fenced one. Evidence from the old quorum can confirm only an inherited cut after installation. [Handoff](../02-handoff/report.md) · [Voter closure](../32-configuration-closure/report.md)
- **Peak capacity.** Each pool accounts for its distinct physical ordinary bytes, still-live old copies, destination residency, and concurrent staging and repair. A scheduler can find a feasible schedule or reconcile an exact unfinished hold. It cannot spend the bytes still occupied by a continuing borrow.
- **Finite debt.** Unbounded growth of the unreconstructable tail or required exact history conflicts with bounded bytes and replay time if the releaser can stop. Use backpressure and checkpoint restart. Longer exact event history requires separately funded durable coverage. [Bounded retention](../03-retention/report.md) · [Exact feed](../17-exact-feed/report.md)
- **Physical completion.** A producer-side tombstone cannot stop a packet already authorized to create bytes. Exact physical erasure needs trustworthy stable disposition across the original scopes. [Provider I/O closure](../40-provider-io-closure/report.md)
- **Degraded service and shared admission.** Renew the one-AZ fault allowance after verified repair. A tier that conceals shared contention needs explicit reserves and a separate scheduling contract. [Degraded admission](../67-full-admission/report.md) · [Isolation](../09-isolation/report.md)

### Architecture-specific costs and reopening tests

| Boundary | Decision now | Evidence that changes the choice |
| --- | --- | --- |
| Stable pooled group and replaceable replicas | Default. Keep worker moves, append and membership change inside one authority. An incarnation's ordered commit path has a finite service rate. Scale regional throughput across groups. | Find a Q01 limit caused by logical ownership under the same hot-stream and one-AZ workload. Separate ordering limits from recovery media, repair bandwidth and placement skew. |
| One authoritative capacity vector | Structural alternative. Use local atomicity where one owner actually enforces the whole vector. Keep cross-owner preparation out of foreground operations. | Under identical workloads and outages, show that enforceable vector reservations with the same real bridge budget admit more eligible moves or meet a move deadline that ordered local prepares miss. Account for per-pool peaks, outages and reclaim time. |
| Required regional append witness | Exclude under the installed-group availability contract. The studied design also adds a dependent durability decision. | Find an authority placement where isolation of a separate witness cannot block a reachable group and verify it against H2. Adopting a weaker availability contract would need a product decision. |
| Storage-native and relay seeds | Preserve as alternatives. A relay is a sequence of funded moves. Native storage requires a qualified effect primitive. | Test delayed delivery, staging, version creation, restart and administrative restore. Test a relay when measured headroom exposes a feasible schedule unavailable to direct placement. |

The next discriminating experiment pairs the stable-group reference with the coordinated funding alternative under the same skew, one-AZ loss, old pins, source-link loss, and zero or positive bridge headroom.
Compare per-pool peak bytes, eligible move completion and pause, and recovery and reclaim times.
Set the numerical workload and thresholds under Q01 before claiming either design is faster or more elastic.
The backend effect test can run independently once the adapter and recovery paths are specified.

### Product boundaries

This round retains exact bounded reconciliation, checkpoint-based watch reopening, retirement for fresh invocations, separately evidenced erasure, and one AZ loss until verified repair.
Funded live stream transfer remains an acceptance program.
A guarantee to migrate with no feasible physical schedule, retain indefinite exact event history, stop overlapping reads at retirement, equate key destruction with physical disposal, or survive a further AZ loss before repair would each change the product contract.

The [architecture tensions review](tensions.md) revisits proved tradeoffs across the whole design.
It compares the next-nonce floor with bounded selective admission and gives the next evidence for choosing the read architecture.

## Reproduction and strength

The model results are bounded under their stated schedules and fairness.
The cited Lean proofs are general over their respective models and premises.
The full candidate matrix also contains architectural arguments where the models abstract storage or transport.
Running RTDB, provider guarantees and latency remain unqualified.

Run with Python 3.13, TLC 2.19 and Java 21.
The shared runner verifies the TLC jar hash and stores each configuration and raw counterexample under .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
python3 -u verification/architecture-reopening/run.py
```
