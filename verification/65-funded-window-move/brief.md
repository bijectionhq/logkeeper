# Study 65 · Turn an exact move reservation into funded journal service

2026-11-23

## Question

Can a fully prepared move open its replacement journal without a second capacity purchase while old journal data and a live borrower remain at the predecessor?

## Sources

Use [pointwise pool admission](../43-concurrent-capacity/report.md), [exact funded source seal](../46-funded-source-seal/report.md), [physical extent accounting](../52-shared-extent-accounting/report.md), [funded local appends](../62-funded-appends/report.md), and [chosen window replay](../64-chosen-append-recovery/report.md).

## Model and comparisons

Prepare distinct immutable allocation identities in the same ledger used by ordinary allocation and retained bytes.
Bind the exact vector to the ordered source decision and install a chosen destination window from that vector.
Compare pointwise exact ownership with incomplete or foreign receipts, returning an incumbent debit early, and buying the same allocated capacity again.
Model two pool budgets, a competing move, ordinary traffic, and a protected predecessor extent.
Use TLC 2.19 and Lean 4.35.0.

## Properties

- The actual shared ledger funds each exact version in a sealed move's vector.
- Equal bytes or an equal total in the wrong scope supply no authority.
- Installation preserves pointwise physical occupancy and requires no additional capacity.
- The new window uses the exact already held destination version.
- A live predecessor window or borrow retains its own charge across installation.
