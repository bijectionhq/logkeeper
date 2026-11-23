# Study 13 report · Installation and membership durability

2026-11-22

## Verdict

A copy receipt can be authentic and still be unusable for activation after target membership changes.
Even when membership stays fixed, reclaiming the bytes can invalidate an earlier proof.
An install must verify the exact received image and enforce its recoverability under the target membership at the same ordered decision that grants ownership.

## TLC results

Both designs satisfy the two safety laws under the finite bound, with four durable identities, one replacement, one AZ loss, and one sealed record.

| Design | States | Checked acceptance trace |
| --- | ---: | --- |
| Revision-bound receipt | 432 | Copy and recertify in the new membership, activate, and release the source in six transitions. |
| Registered prepared image | 480 | Hold the pending image as a durability obligation across the membership change, activate with its surviving proof, and release the source in six transitions. |

| Amendment | Weakened rule | Shortest counterexample |
| --- | --- | --- |
| A38 | Activate from a stale pre-copy proof. | Copy twice → certify → replace voters → activate with the old proof. A current recovery majority lacks the record after five transitions. Another trace takes seven transitions and loses the serving copy after one AZ is lost and the source releases. |
| A39 | Reclaim certified bytes without invalidating the proof. | Copy twice → certify → reclaim a certified member's copy → activate at the same revision. A legal recovery majority lacks the record after five transitions. |
| A40 | Release source storage on the staging acknowledgment. | Copy twice → certify → lose an AZ → change target membership → release the source. No eligible side has the payload after six transitions. |

## General proof

Four reported Lean theorems compose the existing proof modules with standard axioms only.
`activation_refines_and_preserves_durable_cut` ties the installed authority view to the exact target journal state and its current recoverable cut.
`prepared_image_can_activate` constructs activation when the seal, live reservation and current durable image are present.
`every_available_quorum_recovers_after_activation` derives exact recovery for any current usable majority and any retained entry.
`registered_image_stays_ready` derives coverage through a trace of certified journal transitions whenever the installed image remains unchanged.

Three proof controls fail at the intended refinement obligations when installation permits a different image, uses another member list, or omits current-quorum coverage.
The recovery result quantifies over an independently supplied authoritative membership at the destination, tied by equality to the members actually attesting the cut.

## Decision and residue

The reference gate checks against the target membership at activation and protects the staged bytes through that decision.
A receipt from an earlier revision can guide incremental copying.
It can supply active durability only if the target has accepted the image as an obligation and transfers that coverage through reconfiguration.
The source retains custody until the target has durably activated the sealed cut.
Provider-specific disposal after activation still uses the retirement and inventory protocol.

The check covers one replacement at a time in TLC.
Continuous target reconfiguration, how competing reservations share quota, receipt formation under real crash recovery, and exact-copy attestation remain open.
Discretionary membership changes and ready installs need scheduling rules that prevent starvation.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/13-install-durability/run.py
```

The runner composes the current Lean kernel, reservation proof, placement proof and journal proof directly and checks the weakening controls before the baseline.
