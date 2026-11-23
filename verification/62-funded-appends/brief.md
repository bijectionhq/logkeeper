# Study 62 · Charge append capacity before ordering

2026-11-23

## Question

Can an ordered append consume a pool-backed journal window without a new pool transaction, while retaining the original append decision through storage pressure and recovery?

## Sources

Use the [joint ordered source](../49-unified-source-history/report.md), [exact extent debits](../52-shared-extent-accounting/report.md), [joint recovery dependencies](../54-joint-recovery-protection/report.md), and [regional retirement](../61-regional-retirement/report.md).

## Model and comparisons

Compose a durable source window cursor and exact command with the regional source and pool reducers.
Compare the same stream commands under a prepaid window, under capacity estimated before a competing grant, and under replay that consults current pool availability.
Use the pool ledger's actual debit for a provisioned immutable window identity.
Charge live move preparations to the same finite pool in the bounded comparison.
Keep framer, consensus, and provider adapter mechanics behind their prior contracts.
Run TLC 2.19 and Lean 4.35.0 using the study runner.

## Properties

- Every successful append in the composition consumes a disjoint positive range of its exact stream's already funded window.
- A successful append retains its source position, payload, and offset on replay from the same certified basis.
- A competing deployment or move cannot consume a window's budget after the pool grants it.
- Refusal cannot burn bytes from a window's source cursor.
- An exact window debit cannot return while the window is still owned by the source.
- Exact local admission remains possible at full physical capacity when the stream already owns a fitting window.
