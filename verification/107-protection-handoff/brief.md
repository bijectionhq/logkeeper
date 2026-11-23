# Study 107 · Carry protection through a move and its storage effects

2026-11-23

## Question

Can an installed target inherit a spent protection interval without a source dependency, and can original media subsequently be withdrawn without invalidating an acknowledged recovery obligation?

## Sources

Use S02, S06, S57 and S89–S90, and L01–L02 in the [requirements](../requirements.md).
Use the [fenced placement model](../11-authority-refinement/report.md), [target durability proof](../13-install-durability/report.md), [named seal attachment](../89-sealed-delivery-handoff/report.md), and [ordered fault interval](../106-ordered-fault-interval/report.md).

## Model and comparisons

Compare carrying the existing protection summary, resetting at activation, and requiring renewal before installing the target.
Hold the original interval, acknowledged recovery requirements, exact seal identity and target readiness constant.
Check safety of the transferred summary and of physical withdrawal, and check conditional continuation when the source is unavailable.
Include a newly confirmed loss between source seal and target activation.
Compare withdrawal based on physical copies at check time, registered survivor witnesses that already exclude pending withdrawals, and deletion targeting an address that has since been reused.
Preserve older one-AZ promises while the withdrawal effects happen independently.

Use the existing named logical activation and its current-membership guard in Lean.
Represent exact mounted control and physically retained copies as explicit premises.
Use one source, one destination, one protected input and one neighboring deployment in the move comparison.
Use three AZs and at most two original competing authorizations in the concurrent effect comparison.
Use TLC 2.19 and Lean 4.35.0 with the shared runner's 60-second per-command limit.

## Boundaries

The deployment keeps its logical incarnation and the monotone ordered position across a placement move inside one regional failure domain.
Target selection and failure evidence already authenticate the original authority and interval.
An acknowledged dependency is an exact object or fragment needed for reconstruction.
The effect model uses exact interchangeable copies of each such input.
It assumes complete dependency enumeration, independent AZs and authentication at the provider.
