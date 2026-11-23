# Logkeeper protocol tradeoffs worth reopening

2026-11-23

## Changes with the most leverage

1. Keep the ordering authority local to the installed journal group.
   Directory lookup, compute worker placement and physical capacity acquisition are three different jobs.
   Put directory discovery, planned moves and new funding outside the path of an installed funded group.
   A true change of ordering authority still needs a verified source fence and an installed exact successor.
   RTDB Multi's current target Allium assigns writer epochs and checkpoint publication to the directory and describes finite independently managed cells.
   The Logkeeper reference instead puts same-placement writer grants and checkpoint publication in the journal and scales the regional service across bounded journal groups.
   This is a change to the RTDB target design and its integration boundary.
   It does not require one regional consensus log or manual placement for each group.
   [Shared architecture comparison](comparison.md) · [Writer handoff](../76-stable-writer-handoff/report.md)
2. Keep exact replay on the operations that promise it.
   An ordinary latest observation can retry in a new freshness interval, while an accepted transaction or protected named invocation needs its original outcome.
   Flight SQL owned-read open and placed transaction reconciliation already use distinct identities at the inspected RTDB revision.
   Confirm the ambiguous-read behavior of each Bijection caller before changing its guarantee.
   The separation can remove an entire foreground journal operation and its recovery debt for ordinary reads.
   [RTDB and Bijection caller inventory](../92-read-contracts/report.md)
3. Decide explicitly what a degraded admission asserts.
   A stable-outage proof verifies admission given a trustworthy failure identity.
   A timeout and two surviving replies can be identical whether the third AZ is down or slow.
   Avoid making a separate global diagnosis mandatory for funded installed service.
   An alternative worth checking is a durably ordered degraded scope with explicit authorization and verified surviving quorum, current window, and complete exact recovery inputs.
   A deliberate exclusion must preserve existing acknowledged protection and must consume the fault allowance visibly if it permits fresh work under narrower coverage.
   Healthy status returns only after the protection is actually restored.
   [Existing proof](../67-full-admission/report.md) · [Diagnosis comparison](../99-degraded-evidence/report.md)

## Fundamental constraints

| Guarantees in tension | What the evidence forces |
| --- | --- |
| Serve both sides of an authority partition and keep one ordered history | A successor needs an intersecting decision or exact evidence that the predecessor has fenced its order. Reachable funded service belongs to the installed side. An arbitrary isolated side cannot be promoted safely. [Handoff](../02-handoff/report.md) · [Quorum closure](../32-configuration-closure/report.md) |
| Bound bytes and replay while preserving an indefinite exact feed through stalled maintenance or consumers | An advancing history creates debt while its required release point remains fixed. Use bounded recovery and checkpoint restart, or independently fund a defined exact history contract. A stalled required consumer or checkpoint eventually forces a refusal. [Bounded retention](../03-retention/report.md) · [Exact feed](../17-exact-feed/report.md) |
| Complete retirement at a reachable quorum and prohibit every later effect at an isolated provider | Quorum closure can exclude new invocations. A previously authorized overlapping operation can still have a live borrow, and a delayed storage request can still reach its effect boundary. Logical retirement, effective stop and verified physical erasure have different authorities and availability. A strict stop deadline must wait for enforcement or require every effect to intersect the stop decision. [Standing read custody](../31-standing-custody/report.md) · [Provider effect closure](../40-provider-io-closure/report.md) |
| Move immediately while retaining old physical interests at full capacity | Until the old interests settle, both footprints can be necessary. Exact capacity is pointwise by physical pool and AZ. A scheduler can improve placement and timing when there is a feasible path. It cannot manufacture capacity in the needed domain. [Concurrent move capacity](../43-concurrent-capacity/report.md) · [Evacuation](../53-pool-evacuation/report.md) |
| Always use idle capacity and promise unconditional immediate isolated admission | Another tenant can consume the promised bytes as irrevocable writes. The existing proof protects data and authorization and explicitly allows shared admission to reveal contention. Isolated guarantees need hard reserves, independently enforceable scheduling, or a loan that can be reclaimed before the guarantee applies. [Shared-budget counterexample](../09-isolation/report.md) |

## Proved tradeoffs that remain choices

- **FIFO read identities.** The one-word floor is sound and compact under strict next-nonce admission.
  It also makes request 2 wait for a lost request 1 even if their read work is independent.
  Keep it if exact opens are serialized in the caller.
  If they arrive independently, compare a bounded selective window in which one missing nonce blocks only after the window fills.
  The bitmap must survive checkpoint selection and failover.
  [Nonce floor](../84-read-invocation-floor/report.md) · [Selective admission comparison](tensions.md#a-next-nonce-floor-imposes-head-of-line-blocking)
- **Fusion of exact capture and delivery.** One ordered decision can save a round, given prepaid coverage of the view the journal actually chooses.
  A fixed preauthorization can be overtaken indefinitely by checkpoint churn.
  Standing coverage avoids that race by delegating paid range ownership, durable scope state and settlement to the original provider.
  Keep the split reference until fusion shows a foreground benefit under the same failure and peak byte budget.
  [Atomic capture](../93-atomic-read-capture/report.md) · [Provider settlement](../96-standing-provider-settlement/report.md)
- **Cross-pool acquisition order.** Strict order prevents cyclic waits.
  It does not establish useful admission throughput or rule out stranded partial holds.
  Compare an enforcing vector owner, coordinated scheduling of independently enforced holds, and ordered local acquisition under the same funded bridge and placement skew.
  A separately failing allocator belongs only on fresh preparation paths.
  [Concurrent capacity](../43-concurrent-capacity/report.md) · [Capacity comparison](comparison.md#executable-comparisons)
- **Early reuse of refunded capacity.** Durably located redo can preserve the refund before a selector switch.
  That shortcut requires enough overlap to write the replacement while retaining redo for the predecessor.
  The stable-image alternative has a smaller reserve in the model and adds selector completion to the reporting path.
  Study 100 ties the ranked handoff to the exact local pool media.
  It checks a hidden chosen refund and dependent reuse in the same recovery history.
  Recovering only the refund or spending a historical receipt can duplicate a credit.
  [Local settlement redo](../98-settlement-redo/report.md) · [Ranked pool refund](../100-ranked-pool-refund/report.md)

## What the proofs leave open for scale

Service scales across independent journal groups while each deployment keeps its own order.
A regional management boundary can contain many groups and shared worker pools.
More workers alone do not increase one hot deployment's ordered service rate or create eligible capacity during repair.
A bounded queue or a bounded number of scheduler turns also does not establish wall-clock latency.
Q01 currently names latency, recovery time and repair progress without numerical thresholds.
Before choosing how densely to pool groups, compare healthy and one-AZ-down admission with a hot deployment, cold-start replay, checkpoint churn, and concurrent repair.
Measure per-group and per-pool occupancy, recovery debt, wait times and surviving throughput.
[Qualification gate](../implementation-gate.md) · [Ready-work scheduling](../97-settlement-workspace/report.md)

The candidate changes to caller retry semantics, exclusion policy and strict retirement promises are product decisions.
The report describes the verification worktree and the inspected RTDB target at `f3be4137350e`.
The named model results are scoped to their stated proofs and bounds.
