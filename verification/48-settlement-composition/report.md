# Study 48 · Compose source compaction with physical settlement

2026-11-23

## Verdict

A logical abort lets a pool close the move's exact key.
Provider writes already issued under that key can still land.
The pool can certify settlement once it proves stable absence or durably holds the entire remaining physical obligation and charge at that same pool.
The source can then reclaim its own exact-result slot after all acknowledgments, even when the provider cannot complete erasure.
The surviving physical debit continues to constrain ordinary admission.

A successful install receipt must bind the exact funded decision and its recovered history.
Target placement alone is insufficient as the same placement can receive other moves.

## Properties and comparison

[Settlement.tla](Settlement.tla) models an ordered abort or funded seal, two pools, and one possible issued write per pool.
Each reserved or adopted debit occupies one unit in its physical pool.
Ordinary work shares the same capacity.
Local closure stops issuance, while already issued writes may still land until effectively fenced.
The outage removes provider control operations for the first pool, while previously issued work can still take effect.
Controller recovery preserves the local book.
The separate [InstallBinding.tla](InstallBinding.tla) compares exact and weakened matching of same-placement install receipts.

| Baseline | Bound | Distinct states | Checked result |
| --- | --- | ---: | --- |
| Exact installation binding | Three candidate receipts | 12 | The exact-install invariant holds. |
| Wait for verified absence | Two pools, two units each | 66,752 | All five safety laws hold. The separate outage control falsifies result settlement. |
| Allow independently charged custody | Two pools, two units each | 143,328 | Five safety laws and eventual abort settlement hold at the bound. |
| Allow custody with one provider control path unavailable | Two pools, two units each | 61,112 | Same laws hold at the bound. |
| Allow custody with one provider control path unavailable | Two pools, three units each | 127,488 | Same laws hold at the bound. |

The five safety laws bound numeric usage, keep possible physical writes and surviving bytes charged, preserve endorsed receipts across recovery, require installed target evidence, and preserve needed charges after source compaction.
The temporal law gives weak fairness to local fencing, eligible debit adoption or settlement, receipt intake and compaction.
The abort cases use an available local charge and assume reachable decision and participant authorities.
They place no fairness requirement on the old provider control path.

| TLC weakening | Shortest safety failure or temporal result |
| --- | --- |
| Refund on abort | Prepare, issue a write, and choose abort. The pending write loses its debit in three transitions. |
| Treat local fence as physical disposition | Choose abort and close the key with a pending write, then release its debit in five transitions. |
| Adopt in a different physical pool | Close the key and move its pending write's debit to another pool in five transitions. |
| Forget the new debit at controller recovery | Adopt and endorse a debit, then lose it during recovery in six transitions. |
| Accept target evidence before install | Prepare both pools and seal, then acknowledge the target before install in four transitions. |
| Wait for erasure before any abort receipt | With the provider control path down, a fair execution keeps the source result after local key closure. |
| Match only the target placement | Receive and accept evidence for another decision at that target in two transitions. |
| Match the funded decision but omit the cut | Receive and accept evidence for another history under the same decision identity in two transitions. |

[SettlementComposition.lean](SettlementComposition.lean) connects the reference stream lifecycle, provider I/O guards, numeric charge reclassification, installed target quorum, and the reserved source result reducer.
Lean checked nine theorems using standard axioms only.
The source can record its exact retirement abort in its reserved row without a participant reply.
An accepted local abort receipt derives permanent refusal of the exact registration key and stable physical absence or traceable custody backed by a sufficient debit for that exact decision and physical pool.
An already issued write can remain eligible after the pool reclassifies the debit, with the same total usage at every pool.
An exact target receipt carries the funded decision and installed history, and any current recovery majority can recover that history under the stated installation premises.
The final participant's exact receipt allows sparse source compaction while preserving another slot's lookup and the issuance value.
The two Lean controls reject ignoring the charged pool and matching installation evidence only by target placement.

## Amendments

[A184–A187](../amendments.md#study-48--2026-11-23) separate logical abort from numeric refund, retain physical ownership through result compaction and recovery, and require exact funded target evidence.
For a target co-located with other moves, the same serving scope does not carry their settlement authority.

## Acceptance programs

- P54. Queue the write, choose abort, close the exact key, and reclassify its debit at the same pool. Recover its controller and compact the source result with the provider control path unavailable. Complete the old write against the surviving debit at full pool capacity. TLC reaches compaction with the write pending in thirteen transitions and the later effect in fourteen.
- P55. Refuse same-placement evidence for another move or command cut in the binding model. In the two-pool model, install the funded seal and compact its source result at capacity while both installed debits stay charged. The compacted-seal witness takes fourteen transitions.

## Residue

The numeric proof treats the full physical footprint and its association with each exact debit as trusted inputs.
The bounded physical model uses one move and two independently charged pools.
The source reducer checks authenticated evidence for an exact decision, local body, and cut.
Construction of that evidence from the actual ranked command encoding, and simultaneous byte accounting across multiple moves and repeated changes of ownership, still need proof.
The proof uses the previous certified-target and provider effect contracts and does not implement either one.

## Reproduction

Run with Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner saves configurations, traces, and raw proof diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/48-settlement-composition/run.py
```
