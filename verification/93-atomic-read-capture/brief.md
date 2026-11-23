# Study 93 · Atomically capture and authorize first use

2026-11-23

## Question

Can an explicit recoverable read atomically capture its original result and authorize its first paid delivery during advancing checkpoints?

## Sources

Use [snapshot admission](../18-snapshot-admission/report.md), [ordered reissue](../87-ordered-reply-admission/report.md), [retained delivery](../88-retained-delivery/report.md), and [fresh and exact read contracts](../92-read-contracts/report.md).

## Model and comparisons

Compare the split capture and first-use program, a fused command with a fixed prepared basis, and a fused command using a paid delegated credit whose scope includes the basis selected at application.
Apply the same advancing-view schedule to each.
After split capture, retain the chosen basis while preparing its first use.
Distinguish an allocated physical charge from the ordered assignment decision.
Keep both exact read and delivery rows in the successful command while preserving independent close and settlement.
Use a finite two-view churn cycle in TLC and the existing typed admission and delivery reducers in Lean.

## Properties and programs

- Successful atomic capture chooses its read result, exact basis and separately held first delivery in one command.
- Failure leaves the tentative read, nonce and delivery state unconsumed.
- An exact delegation can cover more than one ready basis without authorizing an uncovered view.
- Assignment and unused credit fencing compete in the installed order.
- The installed authority can fence an unused older credit after writer replacement.
- The first delivery can complete under its independently held exact borrow after the authorizer disappears.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
Run negative controls before the reference cases.
Keep tool output and traces in .results/.
