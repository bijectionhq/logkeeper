# Study 45 · Move a capacity pool's authority

2026-11-23

## Question

Can a pool change its owner and compact canceled reservations without reopening old admission, dropping a prepared debit, or borrowing already committed capacity?

## Sources

Use the [requirements](../requirements.md), [custody channel model](../21-custody-channel-lifecycle/report.md), [custodian recovery](../24-custodian-recovery/report.md), and [pointwise accounting](../43-concurrent-capacity/report.md) and [provisional capacity](../44-prepared-capacity/report.md) studies.

## Model and comparison

Give the pool a durable channel that uses issued serials, a floor, and live debits.
Compare exact ownership transfer with alternatives that copy only occupancy or only the last staged control snapshot.
Check a competing representation that retains each canceled reservation permanently.
Give the move's decision authority a separate transition from each pool's application of its decision.
Distinguish a pool's physical identity from the current map of owners.
Assume the same physical pool and enforced resource limit survive the ownership change.
Treat voluntary reduction in the resource limit separately.

## Properties and acceptance

- Refuse an aborted reservation after its local release, even after compaction and ownership change.
- Preserve live prepared and committed debits and exact retries through ownership change.
- Fence a delayed prior-owner operation and permit a current-owner operation against the same immutable reservation key.
- Bound explicit cancellation rows by the acknowledged issuance window.
- Check ordinary work against charged capacity and refuse a planned shrink that would underfund live usage.
- Complete a funded reservation through the new owner when the old owner is offline.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 to connect exact cut recovery to ordinary admission, live debit preservation, and compact refusal.
