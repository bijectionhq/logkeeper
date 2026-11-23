# Study 63 · Bind a durable vote to an isolated physical version

2026-11-23

## Question

Can a voter stage a competing append for the same logical range without damaging the earlier accepted prefix, and with a finite independently charged footprint?

## Sources

Use [journal rotation](../26-journal-rotation/report.md), [ranked durable voting](../27-prefix-consensus/report.md), [shared physical debit](../52-shared-extent-accounting/report.md), [guarded provider effects](../58-storage-effect-boundary/report.md), and [funded appends](../62-funded-appends/report.md).

## Model and comparisons

Model the used portion of one voter's media, including an independently protected older extent.
Use the existing durable acceptor and charged pool authorities.
Separate allocation, exact byte persistence, locator persistence, accepted binding, and reclaim.
Compare isolated physical allocations with writes keyed by logical offset, publication before either durability barrier, and release while an older selectable cut still holds the allocation.
Test reuse of a slot with a new generation, including delayed writes from the old generation.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- The reported accepted vote always has exact recoverable bytes and a durable physical binding.
- Competing writes at one logical position do not alias.
- Each staged and pinned physical allocation retains its own debit.
- A later vote can take over without destroying an independently pinned exact copy.
- Replacement at finite capacity accounts for every physical copy that has to coexist.
