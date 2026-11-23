# Study 89 · Transfer unfinished delivery at the exact seal

2026-11-23

## Question

Can a successor activate from one authenticated sealed cut and finish, or settle, an already incurred physical delivery after the predecessor route disappears?

## Sources

Use the [sealed read attachment](../82-joint-read-recovery/report.md), [invocation floor](../84-read-invocation-floor/report.md), [ranked local publication](../86-atomic-recovery-publication/report.md), and [independent delivery book](../88-retained-delivery/report.md).

## Model and comparisons

Put the read section, the old writer's consumed floor, and the outstanding delivery book in one authenticated control object.
Before accepting the ordered seal, compare the decoded attachment to the control state of the prospective applied seal.
The seal consumes the next ordered position and preserves the delivery book.
At the target, reopen the bytes named by that seal and require custody of both kinds of dependencies, then run the existing exact installation decision.
Preserve ownership of the original physical borrow at its provider.
The reference uses finite books of arbitrary size and treats the complete immutable manifest and its provider promises as inputs.
The bounded model uses two same-data-frontier cuts, one physical operation and an outage after seal.
Compare rollback by data frontier, split control, omitted dependencies after read closure, original-provider reassignment, counter reset, predecessor settlement and mandatory predecessor recontact.

## Properties and programs

- A chosen seal carries the source's exact read section, consumed floor and delivery book at one ordered boundary.
- Missing original custody blocks activation even after the logical read closes.
- A fully mounted target can activate after the predecessor route disappears.
- A pending delivery completes with the authenticated original caller and original still-held borrow.
- The installed owner can apply the original provider's stable settlement and preserve every other row and the issuance floor.
- The sealed predecessor refuses that ordered settlement.

## Reproduction

Use TLC 2.19 with Java 21, Lean 4.35.0 and Python 3.13.
Run negative controls first.
Keep output under .results/.
