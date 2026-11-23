# Study 51 · Authenticate the complete checkpoint envelope

2026-11-23

## Verdict

Check one authenticated envelope for the expected lineage, ordered position, prefix, format, and data frontier.
Opening uses the exact named control, data, and evidence objects.
The expected data frontier alone cannot distinguish valid objects from different cuts.

A control-only checkpoint can reference the same immutable data root as its predecessor.
Its new envelope binds the new control state and evidence while retaining that root.
Every required evidence descendant keeps its own durable custody through open and recovery.

## Bounded comparison

[CheckpointEnvelope.tla](CheckpointEnvelope.tla) has three candidate cuts, three data identities, and three evidence manifests.
The two cuts in the requested lineage share a data frontier and immutable data root, with different control and evidence identities.
A foreign cut shares the requested numeric position.
Manifest registration abstracts durable coverage of its full dependency set.

The reference explored 108 distinct states.
Correct selection, exact component loading, and complete evidence coverage for selected and opened checkpoints hold at that bound.

| TLC weakening | Shortest safety counterexample |
| --- | --- |
| Select by numeric position without lineage | Select a foreign cut at the requested position in four transitions. |
| Select by data frontier alone | Select the earlier ordered cut at the same data frontier in four transitions. |
| Substitute control state at the same data frontier | Open the newer cut with its predecessor's control in six transitions. |
| Substitute a root at the same data frontier | Open the selected envelope with a different data object in six transitions. |
| Accept any evidence manifest in the lineage | Open the selected envelope with an earlier evidence manifest in seven transitions. |
| Register a manifest without its descendants | Select it without the required physical evidence in three transitions. |
| Forget a registered dependency pin | Reclaim a dependency and open the certified envelope without its evidence in seven transitions. |

## General proofs

[EnvelopeCodec.lean](EnvelopeCodec.lean) defines the executable framing codec.
It uses a checkpoint domain byte, a format byte, and seven fixed-width fields.
For field width `w`, the encoded length is `2 + 7 × w` bytes.
Lean proves decode after encode and exact re-encoding of every accepted byte sequence.
Two distinct envelopes therefore cannot have the same canonical encoding.
The trailing-byte control breaks the exact-consumption proof.

[EnvelopeRecovery.lean](EnvelopeRecovery.lean) checks the expected format, lineage, ordered cut and data frontier against the authenticated envelope.
Successful checked opening resolves each component by the identity in the canonical message, covers every required dependency, and retains each named dependency.
The proof reuses the authenticated command-prefix and checkpoint premises to recover data and replay joint control from the same certified cut.
It also shows that two valid opens naming the same immutable data object recover the same data body.
The controls fail when the checker ignores the ordered position or opens without durable dependency coverage.
The two modules check nineteen reported theorems using standard axioms only.

## Amendments

[A196–A199](../amendments.md#study-51--2026-11-23) require exact component binding, complete cut selection, canonical framing, and durable descendant custody.
The single envelope is the checked representation of those bindings.

## Acceptance programs

- P61. Register the new evidence and open the second ordered cut with its new control state and the same data root used by the first cut. TLC reaches the witness in six transitions. The matching controls exercise the wrong-cut and wrong-lineage variants.
- P62. Register the exact evidence closure before selection and keep the referenced objects through opening. The manifest-only and lost-pin controls demonstrate the two independent failures.

## Residue

The codec covers the envelope framing and treats each field's bytes as an already canonical identity or numeric word under its format.
Body encodings, position rollover, and cryptographic adapters remain separate obligations.
Authentication checks and catalog lookup are modeled as predicates and immutable typed mappings.
The recovery theorem assumes that the authenticated producer certified the decoded control image, exact data basis, and complete dependency set from the chosen prefix.
The finite model abstracts transitive discovery into the manifest's expanded set and checks custody through selection and open.
Concurrent root and evidence charges and the production custody adapter remain to be composed.

## Reproduction

Run with Python 3.13, Java 21.0.13+9, TLC 2.19 and Lean 4.35.0.
The runner saves model configurations, traces, and proof diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/51-checkpoint-envelope/run.py
```
