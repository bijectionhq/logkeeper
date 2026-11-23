# Study 61 · Settle one deployment inside a shared pool

2026-11-23

## Verdict

An exact read can outlive the deployment's ordered close and retains its original physical hold until it completes or is effectively stopped.
Completing a read by physical version alone can consume a different read's hold on that version.
Retirement can settle once the retiring deployment's own custody and its exact erasure scope have settled, even when a surviving deployment keeps reading a version under independent custody.
Private bytes return their capacity on exact disposition.

## Bounded comparison

[RegionalRetirement.tla](RegionalRetirement.tla) models two streams in one pool with two units of capacity.
One unit holds a shared immutable version outside the retiring stream's erasure scope and the other can hold its private version.
The model separates ordered close, reference detachment, fencing, erasure, refund, read admission, and read completion.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Two read identities | 2,738 | All five safety invariants hold. |
| Three read identities | 12,674 | The same five invariants hold. |
| Survivor holds a shared read indefinitely | 12 | Safety holds and retirement settles under weak fairness of retirement, detachment, and settlement. The initial state has no private extent or retiring deployment's outstanding read. |

| Weakening | Shortest counterexample |
| --- | --- |
| Complete by version | Start two reads of the same version. Complete the first read, then redeliver its completion. The duplicate consumes the second hold. Four transitions. |
| Admit from a stale root | Close the stream and start a new read using its still-registered root. Two transitions. |
| Refund on stream close | Close the stream and return the private version's unit before disposing of the version. Two transitions. |
| Accept detachment as disposition | Close the stream and detach both of its references. Certify erasure while its private version still exists. Four transitions. |
| Wait for every shared reader | Retire and detach the original references, with the survivor's independent read still live. The system can stutter at that state forever under the same fairness. |

## General proofs

[RegionalRetirement.lean](RegionalRetirement.lean) checks eleven theorems with standard axioms only.
The regional reducer projects to traces of the existing stream kernel and steps of the pool incarnation reducer.
Together these preserve per-stream kernel validity, pointwise physical pool bounds, exact live borrow counts, unique serials, and the separate borrow quota across arbitrary finite traces.
An outstanding exact read retains its charged physical backing.
Only the named live hold can be consumed by an authenticated exact stop, and its serial cannot later reappear.

Closing a stream excludes new holds at the regional gate and keeps settled read custody settled.
Retirement leaves the survivor's stream state and existing borrow unchanged.
A survivor with space in its read quota can acquire an independent hold even at full physical byte capacity while the other stream is ready for erasure certification.
Certification requires the original version's disposition for every version in scope.
The two Lean negative controls reject reopening read admission after retirement and certifying before original disposition.

## Amendments

[A235–A238](../amendments.md#study-61--2026-11-23) bind completion to the individual read, separate independent custody from the retired scope, and retain each original physical debit until disposition.

## Acceptance programs

- P92. Close A, detach its references, fence and erase its private version, certify A's erasure, and return the private unit. B then appends using that unit while its initial read remains live. TLC finds an eight-transition witness.
- P93. Admit two reads of one version and retransmit the first completion. TLC preserves the other hold and its backing across the baseline state spaces. Lean proves the first serial stays absent and the exact finish preserves other live entries.
- P94. Complete A's retirement while B keeps its independent read indefinitely. The fair finite run verifies progress and the weakened guard gives a stuttering counterexample.

## Residue

Authenticated immutable ownership, complete erasure scope, and durable exact endpoint completion are model premises.
A shared extent inside the retiring deployment's scope still needs a verified independent rehome before disposal.
The proof covers fresh admission at the regional gate and continued custody for previously admitted operations.
The serving-window refinement still has to place that gate relative to overlapping reads.
The finite comparison abstracts the provider's staged effects and crash recovery through its fenced disposal step.
The Lean composition checks the stream and physical reducers together, with ordered stream steps leaving the pool unchanged.
The finite append witness charges one physical unit, and the general proof still needs exact append and prepared-move funding in the same product.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/61-regional-retirement/run.py
```
