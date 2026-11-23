# Study 04 report · Terminal retirement and physical erasure

2026-11-22

## Verdict

Logical retirement and durable erasure completion require different evidence.
A serving quorum can commit terminal retirement.
Physical erasure completes after each inventoried location has fenced delayed writes and accounted for its bytes.
A location that still holds inaccessible data leaves erasure pending.

## Properties and comparison

The baseline satisfies custody, stable absence, complete acknowledgment, and fair progress with custody access.
TLC explored 1,320 states with three possible locations and 17,328 with four.
The competing progress claim under majority access alone fails with three locations.
The [brief](brief.md) describes the model and fairness assumptions.

| Amendment | Check | Counterexample |
| --- | --- | --- |
| A16 | `unrecorded_copy` violates `CustodyKnown` in one transition and `ErasureStable` in six. | Send an unrecorded copy to a second location. Completeness later checks only the first location and leaves the second copy. |
| A17 | `absence_only` violates `ErasureStable` in six transitions. | Reserve a destination → retire → attest absence at both locations without fencing → complete → deliver a delayed copy. |
| A17 | `forget_fence` violates `ErasureStable` in nine transitions. | Complete with a fenced packet still in flight → forget the destination's fence → deliver the packet. |
| A18 | `only_majority` violates `AllAcknowledged` in eight transitions. | Record three locations and complete after only two have been fenced and acknowledged. |
| A18 | `ProgressWithMajority` fails with one unreachable custody location. | Take the location with existing data offline → retire → stutter with the location inaccessible. |

The liveness trace shows that fair processing of accessible work cannot make inaccessible erasure proceed.
The model can stutter forever after closure with the surviving locations accessible.

## Acceptance program and developer cost

The client obtains a durable terminal receipt and later retrieves an erasure completion receipt.
A queued packet cannot recreate an erased copy because the receiving location still enforces the fence.
TLC reaches safe completion with a delayed packet still pending in seven transitions.
The custody inventory remains relevant after a serving group has been replaced.

## General proof and controls

Lean proves `completed_erasure_has_no_resident_copy` and `cannot_deliver_after_erasure` for any location type and every finite trace of the abstract machine.
The only reported axioms are `propext` and `Quot.sound`.
The delivery-without-fencing control and the absence-only-completion control fail at the intended cases of the Lean invariant proof.

## Residue

The model treats the destination write gate and the evidence of absence as trustworthy.
It leaves scope of a provider's physical-erasure evidence, storage drivers, authenticated generations, and fence compaction to later studies.
Destroying a decryption key would be a different contract.
It requires separate rules for cached keys, ciphertext copies, and the threat model.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/04-retirement/run.py
```

The pinned versions are the TLA+ tools 1.7.4 distribution and Lean 4.35.0.
The runner saves exact commands, model configurations, solver output, and mutation diagnostics under `.results/`.
