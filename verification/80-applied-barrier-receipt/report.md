# Study 80 · Certify a chosen read marker's applied result

2026-11-23

## Verdict

A quorum can choose a read marker whose ordered application refuses.
The installed journal issues a positive barrier receipt only after applying the exact chosen marker successfully.
The receipt records the result at that marker's ordered position.
A later append can advance the current head without changing that result.

The receiver authenticates the exact canonical bytes under the journal scope in the receipt.
It matches the invocation and requires the protected materialized cut.
An already-issued packet, its verification material, and the protected data are sufficient at delivery after issuer loss.
The receiver can verify that packet without asking the source to make another decision.

## Bounded comparison

[AppliedBarrierReceipt.tla](AppliedBarrierReceipt.tla) explores one pending invocation and one marker at a fixed ordered position.
The successful marker reads cut one.
One later append can make cut two materializable.
Each candidate varies exactly one issuance, field matching, or delivery dependency.
The foreign scenario supplies a genuine attestation for a different journal with matching numeric invocation, position and cut.
The overlapping retirement scenario orders retirement after issuance and before source loss and delivery.

| Reference scenario | Distinct states | Result |
| --- | ---: | --- |
| Successful marker and offline receipt delivery | 14 | Exact successful issuance and exact delivery hold. Delivery eventually completes with weak fairness for the enabled path. |
| Successful result before retirement, delivery after retirement and source loss | 10 | The protected invocation can complete with the same receipt under weak fairness. |
| Chosen marker under retired authority | 3 | Application offers no positive receipt. |
| Genuine foreign attestation | 4 | A different journal's attestation provides no serving authority. |

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Issue as soon as the command is chosen | Choose and issue before application. Two transitions. |
| Issue a positive receipt for a chosen refusal | Choose, refuse at application, and issue. Three transitions. |
| Read the newest head when issuing | Choose and apply at cut one, advance to cut two, and issue cut two. Four transitions. |
| Omit the result cut from verification | The valid cut-one receipt is delivered as cut two after the later append. Seven transitions. |
| Omit the application position from verification | A valid receipt is delivered at a substituted position. Six transitions. |
| Omit journal scope from verification | Use a genuine foreign signature on the matching numeric fields to satisfy the local invocation. Three transitions. |
| Require the original signer online at delivery | The exact receipt and protected cut remain available after source loss, and delivery can stutter forever. |

The finite model holds the accepted payload and data frontier fixed except for the one later append.
It models signature matching by exact approved fields and journal scope.

## General proofs

[AppliedBarrierReceipt.lean](AppliedBarrierReceipt.lean) checks nine theorems with standard axioms only.

- A representable receipt round-trips through a canonical encoding of one domain byte and nine fixed-width numeric words. The proof covers lineage, placement, writer, invocation identity, ordered position and cut. The verification gate authenticates the exact received bytes. Signature and key metadata sizes have separate budgets.
- Certificates for the same marker position in a common exact journal origin agree on its preceding frames. Replaying that exact prefix makes the applied result unique. The witness validates the marker's ordinal against the prefix length.
- A positive issuer output implies an exact chosen marker and a successful read under the writer active at that position. Its cut equals the history length at application. A certified refusal at that slot cannot issue a positive packet.
- Receiver acceptance implies a decodable packet issued by this guarded issuer, under the scoped authentication premise. The receiver matches the pending invocation and its protected cut. The positive construction issues and accepts the exact genuine packet without a live source query.

The result uses the full chosen prefix in the proof, with a certified exact origin and replay witness.
The receiving packet does not transmit the prefix.
The reference issuer's signer is an explicit trusted interface that can mint only for the permitted application result.
No proof here verifies a cryptographic signature implementation or actual key policy.

## Amendments and acceptance programs

[A315–A317](../amendments.md#study-80--2026-11-23) separate durable choice from successful result issuance, bind the entire canonical receipt to the exact journal scope, and preserve offline verification for already-issued live evidence.

- P25. Deliver the original applied cut after a later append advances the head.
- P149. Match the actual non-reused invocation and require protected materialization.
- P150. Refuse a positive packet for a chosen refusal. Refuse a changed cut, changed marker position, or foreign journal attestation. Deliver the genuine packet after source loss for the already admitted invocation when its protected cut and verification material are available.

## Residue

The proof assumes exact retained certification and replay, scoped authenticity of the received packet, and protected availability of the returned cut.
Actual signer authorization, verifier key rollover and evidence retention, and RTDB snapshot materialization need refinement.
This study tests delivery after a packet has been issued.
Recovering a chosen marker whose result has never been emitted still needs a usable issuing replica with the exact certified state and dependencies.
The remaining frame and other command-result encodings and provider integration stay open.

## Reproduction

Run with TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner verifies the TLC jar and Lean version, runs the controls before the baselines, and saves raw output under .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/80-applied-barrier-receipt/run.py
```
