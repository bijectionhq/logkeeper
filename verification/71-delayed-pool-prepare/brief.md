# Study 71 · Late pool preparation and exact terminal closure

2026-11-23

## Question

Can an already issued move plan reach a pool after source cancellation, with both exact capacity accounting and bounded terminal metadata preserved through pool recovery?

## Sources

Use the [custody channel](../21-custody-channel-lifecycle/report.md), [copy fence](../39-certified-activation-replay/report.md), [pool authority recovery](../45-pool-authority/report.md), [exact source outcome](../49-unified-source-history/report.md), [physical accounting](../52-shared-extent-accounting/report.md), and [distributed preparation](../70-distributed-preparation/report.md).

## Model and comparisons

Compare exact local abort fencing with timeout refund, custody release before physical closure, forgotten local fences, and reuse of the original receipt after source abort.
Track the actual prepared grant and actual physical debit separately.
Allow receipt and plan duplication, pool takeover, delayed provider work, and closure compaction.
Prove the scoped accounting and fence projection over the existing Lean reducers for arbitrary interleavings.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- A verified historically issued plan can acquire a charged exact grant at an open custodian after source abort.
- An exact fence excludes new preparation through recovery, floor advancement, and reuse of another admission identity.
- A terminal acknowledgment can transfer responsibility to the original charged custody.
- Returning physical capacity requires exact stable physical absence.
- An ordered source abort cannot be replaced by a late receipt.
