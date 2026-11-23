# Study 61 · Compose regional retirement and shared custody

2026-11-23

## Question

How can one deployment retire and release its original custody while another deployment continues reading shared bytes and using the regional pool?

## Sources

Use [deployment-scoped retirement](../04-retirement/report.md), [shared immutable custody](../19-shared-object-custody/report.md), [ordered stream authority](../49-unified-source-history/report.md), [shared extent accounting](../52-shared-extent-accounting/report.md), and [bounded pool incarnations](../55-pool-incarnations/report.md).

## Model

Compose separate stream reducers with one authoritative pool ledger and exact read operations.
Use a shared immutable allocation outside either deployment's disposal scope, and one private allocation in the retiring deployment's scope.
Compare completion by exact read identity with decrementing an aggregate counter by physical version.
Compare scoped retirement against waiting for every borrower of a shared extent and conflating logical closure with physical erasure.

## Properties

- Retirement closes only the selected logical stream and admits no later borrow for it.
- Physical disposal retains every live reference, precise borrow, and original authorized provider effect.
- A repeated completion affects only its own operation.
- Stream-scoped settlement can finish with a survivor's independent read still outstanding.
- Physical credit returns only on exact disposition, and can support later ordinary admission for another deployment.

## Tools

Use TLC 2.19 with a single worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 to check the shared regional reducer and its projections.
