# Study 23 · Custody issuer authority handoff

## Question

What must move with a custody issuer so the successor can recover late physical grants and keep serving while the old issuer and an old custodian have different availability?

## Sources

Use the [portable authority seal](../11-authority-refinement/report.md), [checkpoint recovery model](../16-checkpoint-reconstruction/report.md), [registration recovery](../20-registration-recovery/report.md), [channel lifecycle](../21-custody-channel-lifecycle/report.md), and [physical residence transfer](../22-residence-transfer/report.md).
RTDB Multi at `fc6da3a4a3` distinguishes durable journal identity from process identity and keeps independently retained repair archives in their original custody during a cell transfer.
Moving the custody issuer's state is a proposed composition of those rules.

## Model and properties

TLC models one issuer handoff, one or two outstanding old plans, a fresh destination plan, queued acquire and release messages, and independent access to the former issuer and old physical custodian.
Check that moving the issuer preserves exact possible interests, committed terminal decisions and source authority fencing.
Check that old messages continue to name their original physical keys.
Check weakly fair install after staging the seal, and weakly fair exact release when the moved issuer and old custodian remain accessible.
Lean checks recovery of the issuer book from the certified cut, preservation of cancellation and unresolved plans through any finite ordered trace, and grant reconciliation or release at the original custodian.

## Comparison

Compare the final sealed intent ledger with a pre-copy and a snapshot of currently observed grants.
Exercise premature settlement on absence, omitted terminal decisions, late source decisions, old registrations rebound to the successor, target install dependent on the old issuer, and permanently unreachable old physical custody.
Observe delayed pre-seal work, an inherited cancellation, and a new destination grant while the old pin remains inaccessible.

The models assume the established handoff reservation and exact authenticated seals, and the existing registration and channel contracts for stable physical fences.
They abstract actual cryptography, metadata I/O and quota arbitration, and physical replacement of a custodian's provider.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/23-custody-authority-handoff/run.py` from the checkout with paths as in the [verification index](../README.md).
The study-local ignored results directory contains the commands, model traces and proof diagnostics.
See the [report](report.md) for outcomes and scope.
