# Study 39 · Recover activation decisions from certified evidence

2026-11-23

## Question

Can a successor recover a chosen activation acknowledgment or cleanup decision without contacting the source or original custodian again, while preventing an old refusal from turning into success?

## Sources

Use the [requirements](../requirements.md), [custodian recovery](../24-custodian-recovery/report.md), [ranked configuration closure](../32-configuration-closure/report.md), [historical activation replay](../34-pending-activation/report.md), and [activation composition](../38-activation-composition/report.md).

## Model and comparison

Order the request together with its exact validated evidence, or order a request without eligible evidence.
Compare deterministic replay of that ordered input with replay against current counterpart state or a synchronous remote lookup.
Compare ranked recovery of an unapplied choice with copying only the learned position.
Ground release evidence in absence plus a durable exact refusal fence at the original custodian.
Model quorum choice, immutable media identity, and authentication at their explicit proof boundaries.

## Properties and acceptance

- Recover earlier chosen responses and effect state from an exact installed quorum.
- Preserve a historical refusal even when settlement evidence becomes available during transfer.
- Recover a hidden chosen cleanup during counterpart outage.
- Refuse foreign evidence and a momentarily absent grant with a copy still queued.
- Show that validated evidence can drive the activation reducer at its original ordered position.
- Keep physical deletion evidence distinct from closure of a registration.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 to check exact intake, historical replay, and quorum recovery under stated premises.
