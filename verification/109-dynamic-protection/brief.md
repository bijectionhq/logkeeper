# Study 109 · Change the protected dependency set during withdrawal

2026-11-23

## Question

Can a checkpoint publish a changing set of exact dependencies across independent custodians while other versions may be withdrawing and the allowed fault cases may change?

## Sources

Use S02, S06 and S91–S93 and the prepared-root, custody and checkpoint contracts in the [requirements](../requirements.md).
Compose [shared object custody](../19-shared-object-custody/report.md), [interrupted registration](../20-registration-recovery/report.md), [residence transfer](../22-residence-transfer/report.md), [joint recovery protection](../54-joint-recovery-protection/report.md), and [withdrawal recovery](../108-withdrawal-recovery/report.md).

## Model and comparisons

Compare publication from durable version-specific grants, publication from a physical scan, and publication requiring a fresh round trip to the custody control plane.
Model a protection renewal between preparation and publication.
Compare verifying current coverage, trusting the old qualification and rejecting every such change.
Compare cancellation based on the original chosen outcome with timeout inference and with requiring acquisition replies before release.
Allow publication while an older checkpoint remains selectable, with its original references independently charged.

Use safety invariants for root and witness coverage, exact registration fences, irreversible logical outcome and prior selector retention.
Use temporal checks for publication with durable holds and a disconnected control plane, and cancellation with lost acquisition replies.
In Lean, compose the existing shared custody transitions, exact withdrawal gate, and durable-registration receipt contract across arbitrary finite model traces.

## Boundaries

The candidate manifest's exact logical dependencies and planned physical versions are immutable.
The finite model uses three AZs, an older root and one prepared root, one change to the protection allowance and at most one control-plane outage.
It abstracts a grant as a durably backed, charged registration tied to its original version.
Storage bytes can remain independently readable during a custody control-plane outage.
Use Lean 4.35.0, TLC 2.19 and the study runner's 60-second per-command limit.
