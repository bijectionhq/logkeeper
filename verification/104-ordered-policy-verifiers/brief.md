# Study 104 · Order read-policy verification and its rotation

2026-11-23

## Question

Can the installed journal retire a read-policy signer while recovering all previously chosen grants, without a live policy service or a separate archive lookup?

## Sources and comparisons

Use [the installed grant policy](../103-grant-read-policy/report.md), [canonical signed replies](../80-applied-barrier-receipt/AppliedBarrierReceipt.lean), and [actual crash-selectable journal retention](../26-journal-rotation/report.md).
Compare current-only replay, retaining historical public verification material in the exact selected media, accepting retired authority for fresh offers, and collection based on a visible selector.
Also compare a required synchronous policy-service lookup during replay and a required signature from the retiring policy signer for its own replacement.
Hold the old result, same epoch order, reachable installed owner, and rotation authorization fixed.
The bounded model tests one earlier successful width change, one verifier rotation and one checkpoint replacement.

## Acceptance

- Choose a width change with an exact signed offer.
  Rotate to a newer authorized verifier while the old signing service is unavailable.
- Crash before and after durable selector installation.
  Recover the original width and the current verifier from either permitted path.
- Refuse a new width change with the retired version or a substituted signed scope.
  Admit a valid current offer and settle the earlier verifier's physical retention after all selectors have released it.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
The runner records all comparisons, assumptions, and proof rejections under .results/.
