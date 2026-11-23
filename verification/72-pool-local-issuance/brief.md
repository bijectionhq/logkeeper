# Study 72 · Pool-local physical identities and joint recovery

2026-11-23

## Question

Can physical allocations be minted on arrival at the original pool with no dependence on other pools or plan issue order, while a replacement owner recovers the same allocator, fences, and charged extents?

## Sources

Use the [pool authority](../45-pool-authority/report.md), [ranked configuration closure](../32-configuration-closure/report.md), [pointwise physical accounting](../52-shared-extent-accounting/report.md), and [late preparation](../71-delayed-pool-prepare/report.md).

## Model and comparisons

Keep logical plan and custody keys fixed at issue.
Mint physical versions under the original local pool sequence when a grant first succeeds.
Compare with versions fixed by plan order, bare serials used as physical keys, and independent recovery of stale allocator, gate, or debit components.
Use two pools and three plans in TLC.
Prove local issuance, exact scope and accounting, and projection of ranked recovery to the joint state in Lean.
Use TLC 2.19 and Lean 4.35.0.
