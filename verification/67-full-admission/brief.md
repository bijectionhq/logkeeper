# Study 67 · Admit from one complete current recovery scope

2026-11-23

## Question

Can a recovered group refuse fresh work when any current recovery dependency is missing while still making progress during the one-AZ outage it is designed to tolerate?

## Sources

Use [complete recovery cut protection](../54-joint-recovery-protection/report.md), [exact pool eligibility](../55-pool-incarnations/report.md), and [scoped recovery and fresh window admission](../66-move-recovery/report.md).
Apply the one-AZ availability and recovery targets in L01, L02, S45, and Q01.

## Model and comparisons

Combine the exact current append window with the installed voter scope and all typed input requirements of every selectable checkpoint and suffix.
Use the same fault case for quorum availability and object coverage.
Compare complete admission with window-only admission, visible-selector-only admission, omitted tail attachments, reuse of an earlier scoped proof, and resetting the fault allowance during a known outage.
Check renewal of healthy certification after exact revalidation.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- A fresh admission binds the current ordered recovery scope, eligible window, voter family, and every exact selectable input.
- A degraded scope uses the remaining quorum and exact dependencies under the same identified AZ fault.
- Healthy scope certification requires restored protection for any one AZ loss.
- A stale proof cannot authorize a different installed scope.
