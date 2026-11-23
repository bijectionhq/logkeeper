# Study 77 · Order worker eligibility at the journal

2026-11-23

## Verdict

The stable journal orders the worker roster alongside grants.
A signed nomination must match the candidate's current exact enrollment as well as the predecessor and successor writer bindings.
Withdrawing a live holder removes that enrollment and leaves a fenced vacancy in the same decision.
A vacancy retains the preceding writer as an epoch and placement anchor for a higher grant.
It authorizes no writer work.
An independently authenticated retirement can close a vacancy through the same journal.

A withdrawal names its original enrollment and uses no fresh serial.
New enrollment alone advances a bounded issuance watermark.
An unrelated roster change preserves a current nomination.
These choices avoid requiring unrelated roster stability or available identity space to withdraw an already admitted writer.

## Bounded comparison

[Eligibility.tla](Eligibility.tla) uses three workers, one old nomination with a retained signed binding, a single successor grant, and a maximum issued serial of six.
Initially the original enrollments have serials one through three.
The exhaustion scenario starts with the watermark at six and the same live rows.
The model trusts an exact capability for fresh operations and makes both its original and current issued bindings available for replay.
The model checks that an active writer has its exact current enrollment, that withdrawals affect the exact enrollment, and that current serials are distinct and bounded by the issued watermark.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Race old and fresh nominations and withdrawals | 541 | The three invariants hold up to the bound. |
| Withdraw the current writer and retire the vacancy | 3 | Retirement follows from fair service of withdrawal and retirement, with no candidate takeover. |
| Withdraw and retire at enrollment exhaustion | 3 | The same progress holds when no fresh enrollment serial remains. |
| Enroll or withdraw another worker while the candidate remains eligible | 16 | The candidate's existing nomination remains usable and takes effect under weak fairness. |

| Weakening | Counterexample |
| --- | --- |
| Trust the signature without reading current enrollment | Withdraw the candidate, then grant from its old ticket. Two transitions. |
| Match the worker ID and ignore the enrollment serial | Withdraw, re-enroll the same worker, then grant from the previous enrollment's ticket. Three transitions. |
| Keep the current grant during withdrawal | Withdraw its holder. The grant outlives its eligibility in one transition. |
| Match only the worker ID on withdrawal | Withdraw and re-enroll the worker, then deliver the previous enrollment's withdrawal. It removes the new row in three transitions. |
| Require a writer to retire | Withdraw the only current grant. The vacant stream can stutter forever despite fair service of eligible work. |
| Spend a fresh serial on withdrawal | At the serial ceiling, withdrawal and retirement can stall with the original writer still active. |

The first liveness harness applied fairness to a replacement action excluded by the retirement scenario.
That assumption excluded the stalled behavior.
The harness now grants fairness only to actions present in the scenario, and checks the disabling control before the passing baselines.

## General proofs

[OrderedEligibility.lean](OrderedEligibility.lean) checks twelve theorems with standard axioms only.
The roster reducer bounds the number of live rows and the issued watermark, removes an exact row, advances the watermark on re-enrollment, and preserves another worker's exact row.
An exhausted watermark still permits exact withdrawal.
The actual chosen source reducer refuses stale admission and withdrawal, rejects a nomination whose exact authenticated binding is missing, and fences the current holder in the same decision that removes its enrollment.
That step preserves committed history, paid windows, and both move books.
The ordinary higher-grant command can fill the vacancy with the same funded window and exact cut.
The vacancy excludes writer append and fresh barrier, and the authenticated administrative command can retire it without a replacement.
Raw worker withdrawal and roster editing at a sealed source are refused.
The lower ordered retirement theorem still settles an exact prepared move under either a live or vacant authority anchor.

The roster and watermark are part of the authenticated logical control image.
The ranked replay theorem recovers identical roster and authority from either certified base and its exact suffix.
This result uses the exact-base and frame coverage assumptions from Study 75.
It covers the image, replay, and kernel guard.
It abstracts the physical encoding, signatures, and deployment.

## Amendments and acceptance programs

[A306–A308](../amendments.md#study-77--2026-11-23) specify exact enrollment identity, fenced vacancy with administrative retirement, and fresh issuance at enrollment only.

- P143. Withdraw an eligible candidate, deliver its old nomination, re-enroll it, and deliver the previous nomination and withdrawal again. Refuse all late requests and admit a newly authenticated nomination for the new enrollment.
- P144. Withdraw the current writer and return the exact cut. Refuse old appends and barriers while vacant. Install a higher eligible grant using the same paid window.
- P145. Retire the fenced vacancy at the serial ceiling. Keep the previously committed history and preserve exact settlement of work already admitted.
- P146. Recover the roster and installed authority from either exact journal base with a suffix that includes worker eligibility decisions.

The P143 race, P144 refusal and replacement, and P145 retirement are partly checked in separate models or under exact attachment premises.
P146 is conditional on certified exact control images and suffix coverage.

## Residue

The signature relation must authenticate lineage, the exact worker and enrollment, and the expected and proposed grants.
The administrator must acknowledge an effective change only once the ordered scope and result are known.
Authenticated election, canonical checkpoint and seal encoding of the roster, and complete cross-group transport of the exact control image still need refinement.
Real RTDB must replay through the exact returned cut before serving.
The complete P142 trace and provider failure qualification remain open.

## Reproduction

Run with TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner verifies the TLC jar and Lean version, tests the six model weakenings first, and stores raw output under .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/77-ordered-worker-eligibility/run.py
```
