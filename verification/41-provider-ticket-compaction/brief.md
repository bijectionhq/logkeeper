# Study 41 · Bound provider write-ticket state

2026-11-23

## Question

Can the provider reclaim terminal write tickets and reuse a physical address while preserving stable refusal of every delayed exact request?

## Sources

Use the [requirements](../requirements.md), [non-reused generations](../06-generations/report.md), [attempt compaction](../35-attempt-compaction/report.md), [certified activation replay](../39-certified-activation-replay/report.md), and [provider I/O closure](../40-provider-io-closure/report.md).

## Model and comparison

Compare requiring an exact live ticket at the physical effect boundary with trusting a capability whose completion marker is absent.
Separate the provider's durable issuance and live set from historical success and network envelopes.
Compare atomic allocation of an issued live ticket with issuance that can precede its durable registration.
Check reuse of an address only after certified retirement of its exact old namespace.
Treat authenticated scope, the atomic physical effect, and exact stable erasure as explicit boundaries.

## Properties and acceptance

- Reuse live-ticket capacity for arbitrarily long histories with a bounded number of live tickets.
- Forget a completed ticket, erase its bytes, and reject delayed delivery even after recovery.
- Certify a closed exact ticket from current durable issuance and absence of its live record.
- Refuse to make a stable claim about future issuance or an allocation that can still register.
- Recover closure after losing the terminal reply, while keeping an exact historical success claim separate.
- Reuse a physical address under a fresh namespace and reject an old ticket with the same local serial.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 for refinement to the provider reducer, the live-ticket bound, and arbitrary-trace refusal.
