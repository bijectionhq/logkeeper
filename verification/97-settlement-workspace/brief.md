# Study 97 · Keep settlement workspace free of remote waits

2026-11-23

## Question

Can independent ready settlements reclaim their original charges at full ordinary occupancy while an older settlement waits indefinitely for another authority?

## Sources

Compare [reserved progress space](../03-retention/report.md), [settlement and physical accounting](../48-settlement-composition/report.md), [sparse compaction](../47-source-outcomes/report.md), [pool-local custody](../72-pool-local-issuance/report.md), and [provider settlement](../96-standing-provider-settlement/report.md).
Use B01, B14, B17, L04 and L22 as the existing capacity and progress boundary.

## Model and comparisons

Put charged obligations at the same original pool and give that pool a fixed reserved workspace outside ordinary admission.
Compare ready-only local use, one shared workspace held while waiting on a remote authority, and workspace reserved per live obligation.
Also compare no reserved space, accepting evidence for a different charge, using uncommitted local work as the refund, and requiring fresh ordinary space for refund.
Check a bounded local restart that interrupts staged work.
Use the existing pool refund in the Lean reference and project local execution to that ledger.
Compare uncoordinated dispatch, a scan of growing allocation serials, and round-robin turns under continuing arrival of ready work.
Use stable bounded local scheduling slots in the round-robin reference.

## Laws and programs

- Every live obligation retains its exact charge until its own stable physical disposition and durable refund.
- A pending remote request keeps its funded obligation and consumes no shared local publication workspace.
- At full ordinary occupancy, an independently ready charge can return during a permanently stalled peer, including after a local restart.
- Reserve for the physical peak of local publication and keep ordinary use within its own limit.
- Under fair local service, ready work completes once its exact disposition is available and the local authority remains stable.
- A continuously ready slot gets a turn even as other slots refill, assuming local dispatch and publication continue.

## Bounds and tools

Use Python 3.13, TLC 2.19 with Java 21, and Lean 4.35.0.
TLC models two or three funded obligations, unit slots, and a single possible crash.
The recurring-work model uses one parked slot, one continuously ready slot, and one slot with an unlimited succession of ready jobs.
Lean uses the exact list of physical rows and arbitrary byte costs and finite histories.
The round-robin proof covers any fixed finite number of scheduling slots.
Use negative controls before baseline checks and preserve commands and raw traces under .results/.
