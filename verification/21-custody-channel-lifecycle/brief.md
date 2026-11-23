# Study 21 · Custody channel rollover and retirement

## Question

Can a custodian reclaim an entire channel's admission metadata while preserving its live grants and refusing delayed operations under the retired handle?

## Sources

Use [one-use handoff reservations](../06-generations/report.md), [physical graph custody](../19-shared-object-custody/report.md), and [registration recovery and per-channel floors](../20-registration-recovery/report.md).
RTDB Multi at `fc6da3a4a3` binds exact hosted version disposition to its residence, namespace, physical key and validated owner revision.
The custody-channel lifecycle is a proposed design refinement.

## Model and properties

TLC models one reusable route, two or three receiver-issued handles, two serials per handle, up to two physical grants, delayed acquire and control messages, release, and a toggling receiver link.
Compare drain-before-close with closing the admission channel while retaining exact installed grants.
Check reuse, exact scoping, publication custody, retired admissions, control footprint, and conditional release progress.
Lean models arbitrarily many renewals across a configurable finite set of active slots with separately stored grants.
It checks retirement, delayed refusal, prior registration decision composition and exact release.

## Comparison

Exercise delayed acquire, close, floor and release messages crossing channel renewal.
Check both that an already published old pin can replay and release after renewal and that a delayed old acquire cannot create a new pin there.
Compare progress with a release rule that requires the issuing channel to remain open, even when an authorized release has reached the custodian.

The models assume authentic scoped authority and durable receiver issuance state.
They abstract actual wire authentication, recovery of lost open responses, provider replication, and grants transferred to another physical custodian.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/21-custody-channel-lifecycle/run.py` from the checkout with tool paths as in the [verification index](../README.md).
The study-local ignored results directory retains exact commands and traces.
See the [report](report.md) for results and scope.
