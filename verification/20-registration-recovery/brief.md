# Study 20 · Interrupted custody registration and bounded retry state

## Question

Can a recovered issuer settle a partially registered manifest and let the custodian compact its closed-reference markers without losing old live roots or accepting delayed acquisitions?

## Sources

Use the [shared custody product](../19-shared-object-custody/report.md), the [non-reused handoff reservation study](../06-generations/report.md), and the [capacity and isolation study](../09-isolation/report.md).
RTDB Multi at `fc6da3a4a3` fences outstanding fork and sweep preparation through the lineage generation and fences an ambiguous replica replay registration even if the hold is absent.

## Model and properties

TLC models one issuer-to-custodian channel with one immutable local dependency batch per serial, pending acquire messages, durable preparation and close, crash and restart, observed live grants, and a delayed cutoff proposal and acknowledgment.
Compare seven safety laws covering durable intent, terminal source closure, published coverage, terminal release, cutoff admission, issuer credit and physical pin capacity.
Check release progress under weakly fair delivery of exact release actions and eventual stable issuer and custodian connectivity.
Lean models exact bindings, arbitrary natural serials, receipt-backed cutoff certificates, custody transitions and whole-channel slot bounds.
It checks that a canceled immutable plan can settle its prepared interests independently across custodians.

## Comparison

Compare a cutoff that can pass only terminal entries to a cutoff that can also pass a still-live grant already durably held by the custodian.
Exercise incomplete recovery, an unsafe cutoff, a lost and replayed acquisition, release before delayed acquisition, early credit, unbounded issuance, unmetered physical pins, and cleanup blocked by a full pin budget.
Check that a still-live grant remains usable below an advanced floor.
Observe cancellation after a crash that loses a grant reply, and verify that the compacted marker still rejects a late request.

The study assumes authentic messages, exact immutable bindings, and an already established channel identity.
It abstracts real object bytes, bytes reserved per batch, provider replication, channel creation and retirement, and source authority transfer.

## Reproduction

Use Python 3.13, TLC 2.19 with Java 21.0.13+9, and Lean 4.35.0.
Run `python3 verification/20-registration-recovery/run.py` with tool paths as in the [verification index](../README.md).
The study-local ignored results directory contains exact commands and traces.
See the [report](report.md) for results and limits.
