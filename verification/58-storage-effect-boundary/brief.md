# Study 58 · Put the guard at the storage effect boundary

2026-11-23

## Question

Can bounded reusable provider slots prevent an old write from resurrecting an erased allocation, and which independent provider obligations still need settlement?

## Sources

Use [provider I/O closure](../40-provider-io-closure/report.md), [positive live admission](../41-provider-ticket-compaction/report.md), and [physical accounting](../52-shared-extent-accounting/report.md).
Compare the required atomic primitive with documented S3 conditional writes, version deletion and multipart behavior.

## Model

Compare an atomic same-location guard and effect with a separate precheck and later raw write, absence-conditioned creation, reusable content tags, and controller-local fences.
Reuse an already provisioned physical slot with a non-reused scoped permission.
Keep staged or retained physical copies in independent custody.
Use a pure durable slot reducer in Lean and compose its disposition with the existing stable absence contract.

## Properties

- The provider checks and consumes a positive live permission at materialization.
- A fenced slot stays closed to old permissions across restart, clear and reuse.
- A compact vacant guard uses constant space across all prior allocations.
- Confirming payload absence leaves outstanding staged or retained physical effects charged until their own closure and stable absence.
- Initial provisioning and destruction of the entire guard bank require their own authority and evidence.

## Tools

Use TLC 2.19 with a single worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for closure, non-reuse, and projection onto the existing provider contract.
