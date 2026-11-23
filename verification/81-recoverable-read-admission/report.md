# Study 81 · Recover a protected read admission before its first receipt

2026-11-23

## Verdict

A successful protected read admission records the original marker result in the same ordered decision that captures and reserves its exact snapshot basis.
The immutable result and hold travel together in the authenticated control image.
A reachable successor can reissue the original result even after compaction removes the marker frame.
Lookup uses the authenticated original invocation, which the caller already knows before any response.
The new permit is internal to the reservation, and retries reuse the live row without another charge.

A marker without protected admission makes no promise of exact result recovery.
While the stream remains live, the caller can start a fresh attempt after reconciling the old one.
Retirement prevents that fresh admission.
An already admitted invocation can continue with its original evidence and protected inputs.
Exact completion or effective stop releases its logical row and reservation.

## Bounded comparison

[ReadRecovery.tla](ReadRecovery.tla) uses one read, one prior marker, a possible retirement, a failed issuer and a compacted journal suffix.
The case for duplicate admission has two available slots.
The other cases have one.
The model starts postfailure recovery with the admitted result or its deliberately weakened counterpart.
TLC checked the progress cases under weak fairness for their modeled enabled actions.
The refusal and reuse cases check safety.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Protected admission, issuer lost before receipt | 7 | The original result is returned. |
| Protected admission, retirement and issuer loss before receipt | 8 | The original result remains recoverable. No fresh admission is needed. |
| Marker without protected admission, still live | 6 | A fresh attempt can succeed. |
| Marker without protected admission, retired | 5 | The old marker gives no authority to admit a new read. |
| Effective stop and slot reuse | 13 | The former permit cannot act on the replacement. |
| Free second slot | 7 | Retrying the live invocation takes no additional credit and recovers the original result. |

| Negative control | Trace or result |
| --- | --- |
| Keep the result only in the failed issuer | The original hold remains funded and the exact result stays unavailable. Temporal counterexample. |
| Infer a receipt from the surviving pin | After compaction the reissuer invents a different result in six transitions. |
| Retain the result without its protected basis | The unprotected result is served in six transitions. |
| Require the old suffix even with the retained row | Compaction permanently prevents reissue. Temporal counterexample. |
| Require the lost response's new permit | The caller cannot present the permit that the failed issuer never sent. Temporal counterexample. |
| Retry fresh through terminal retirement | A previously unprotected attempt gets new admission in five transitions. |
| Match a recycled slot without its serial | Delayed old work acts after reuse in seven transitions. |
| Charge a duplicate invocation when another slot is free | A second charge is recorded in three transitions. |

The model separates the tentative marker from protected admission and omits actual storage and cryptography.
The source recovery comparison assumes the chosen control state and its protected inputs are available to a successor.
The slot-reuse check exercises logical reclamation after an exact effective stop.

## General proofs

[RecoverableRead.lean](RecoverableRead.lean) checks fourteen theorems over the actual successful chosen marker and the existing snapshot reducer.

The admitting transition requires the marker's exact current source image, a successful ordered result, the matching snapshot head, and funded room.
It captures the protected basis and records a bounded result row at the same decision.
A live row has exactly one hold serial and one invocation identity.
Append, publication, trim and placement changes that preserve the held bases preserve the row invariant.
An exact authenticated stop clears its row and hold, preserves other reads, and prevents an old permit from acting on a recycled slot.

Reissue reads only the bounded result rows and their existing holds.
The refinement theorem proves that a reissued packet could have been emitted by Study 80's original guarded issuer, using the actual chosen marker evidence carried as proof.
Storage need not reload that evidence's full historical suffix to reissue.
The acceptance theorem composes capture and recovery from an exact restored control image, and returns the original canonical packet using the authenticated invocation alone.
An absent or unauthenticated invocation supplies no packet.

The canonical row is the binding serial and Study 80's receipt body.
For word width w, its exact payload length is 1 + 10w bytes.
The inventory has only the configured finite result slots.
Account for each selectable copy and the snapshot hold framing under their existing control budgets.
Effective stop can release existing rows even when the serial space or slot budget is full.

## Amendments and acceptance

[A318–A321](../amendments.md#study-81--2026-11-23) bind the recoverable result to protected admission, match retries by original invocation, and bound retention and release.

- P151. Admit a protected read, lose the issuer before any receipt or permit reaches the caller, and compact the original marker. Restore the exact control image and reissue the original result by authenticated invocation, including when retirement followed admission.
- P152. Lose a tentative marker before protected admission. The live deployment can retry under a fresh invocation. The retired deployment refuses fresh admission.
- P153. Retry a live invocation with a free slot and prove it consumes no additional row. After exact closure and slot reuse, refuse the old permit.

The first program runs in the Lean admission and recovery reference under exact restored control and scoped signer premises.
The temporal and retry distinctions are bounded TLC results.

## Residue

The implementation must select and authenticate the snapshot holds and their result rows as the same actual ordered control image.
The proof treats the current snapshot projection and later exact restore as premises.
It does not supply the combined control-image codec, complete checkpoint and handoff transport, signer rollover or physical endpoint stop qualification.
The provider can still block progress by losing required protected inputs or failing to establish effective stop.
The baseline carries no guarantee of indefinite retry after closure.

## Reproduction

Run with TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner checks the controls first and saves commands, configurations and logs under .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/81-recoverable-read-admission/run.py
```
