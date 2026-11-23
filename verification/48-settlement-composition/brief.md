# Study 48 · Compose source compaction with physical settlement

2026-11-23

## Question

Can the source forget a funded seal or abort while old physical writes remain possible, and what capacity can be reused at that point?

## Sources

Use the [requirements](../requirements.md), [physical fence](../39-certified-activation-replay/report.md), [provider I/O](../40-provider-io-closure/report.md), [numeric ledger](../43-concurrent-capacity/report.md), [source seal](../46-funded-source-seal/report.md), and [result book](../47-source-outcomes/report.md) studies.

## Model and comparison

Compose two local pools, their outstanding provider tickets, the ordered source decision, and participant acknowledgment at the result book.
Compare release after stable absence, transfer to independently charged local custody, and release against an admission fence alone.
Include same-capacity and wrong-domain transfers, controller recovery, extended provider outage, and asynchronous result delivery.
Keep actual target data readiness and certificate transport as premises.

## Properties and acceptance

- Only the exact chosen source outcome can authorize an acknowledgment.
- A pool closes admission and either proves stable absence or owns the full physical debt at its original resource location before discharging source evidence.
- Returning a result row preserves every needed numeric debit. An obsolete resident may still consume a unit after source compaction.
- Refuse to acknowledge a sealed install before its exact target install exists.
- Reconcile a canceled result while a provider remains unavailable if independently funded custody can cover the outstanding work.
- Replay exact acknowledgment and compaction evidence without consulting an old controller.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 to instantiate the source result interface with exact candidate decisions and certified local conditions, and check numeric and replay composition.
