# Study 09 · Stream contents and shared capacity observations

## Question

Can shared log storage provide unconditional reserved admission and hide other streams' load while accepting work up to its entire durable capacity?

## Scope and comparisons

Use S09 and B01 from the [requirements](../requirements.md).
Compare an observer of one stream's immutable records with an observer of the accept-or-reject response.
Model work-conserving shared capacity and a protected reserve with exact natural-number charges.
Committed storage cannot be reclaimed on demand.
A frame proof checks content separation for arbitrary finite sequences of writes to other streams.
Arithmetic proofs check the observable admission counterexample, protected capacity, and lack of room after borrowing.

Use Lean 4.35.0 and exercise both frame and capacity controls.
Authentication, timing, queue behavior, and cloud limits remain outside this study.
See the [report](report.md) for results.
