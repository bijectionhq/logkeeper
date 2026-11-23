# Study 68 · Consolidate the ordered stream laws and acceptance programs

2026-11-23

## Question

Do funded chosen commands implement one stream state machine that preserves logical bounds and admits the required append, read, fence, trim, and retirement sequences?

## Sources

Use the [logical kernel](../07-reference/report.md), [ordered source reducer](../49-unified-source-history/report.md), [funded chosen replay](../64-chosen-append-recovery/report.md), and [atomic activation](../66-move-recovery/report.md).

## Model and comparisons

Project every command of the existing funded chosen reducer to the logical kernel, including refusals and resource-only commands.
Run acceptance commands through that existing reducer.
Use its actual reachable states as the starting points for one-rule countermodels.
Separate logical reachability from the physical and quorum premises needed to choose each frame in a live deployment.
Use Lean 4.35.0.

## Properties

- Every successfully replayed frame history projects to a legal logical kernel trace.
- The projected trace preserves the committed prefix, configured log debts, replay holds, and terminal authority.
- A funded append, exact read, writer fence, bounded replay and trim, and retirement can be expressed by chosen frames.
- Weakening individual writer, trim, or resource guards makes the relevant declared property false in the same logical state space.
