# Study 83 · Replay the read book and journal together

2026-11-23

## Verdict

The chosen suffix must contain the complete protected-read operation.
A journal-only projection can agree on ordinals and operation tags while silently substituting the evidence for a read.
Opening an exact checkpoint therefore supplies the combined starting state.
The one chosen suffix then reconstructs journal and read state together through its cutoff.
The full admission binds the original invocation, slot, and reservation evidence.
The full logical close binds the exact permit and immutable completion or stop evidence.

Apply original decisions under their historical rules and evidence.
A recovery-time request to reauthorize an already chosen admission or release can stall after historical endpoints disappear.
Serving still requires the current installed authority and physical coverage of the recovered reads.
Physical stop evidence can arrive at a successor before its logical release position is known.

## Bounded comparison

[OrderedReadReplay.tla](OrderedReadReplay.tla) explores a fixed data frontier.
The chosen history admits the first read, closes it, reuses its slot for a second read, and receives a delay of the first close.
Either the empty base or the base after the first admission is selectable.
The chosen close can be unapplied when the process dies.
A complete physical suffix may contain an intact, unchosen close of the new read past the cutoff.
A rival may carry the correct journal operation with different admission evidence.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Full exact coverage available | 26 | Both bases reach the second admitted result after the old endpoints go offline. The extra staged close is ignored. |
| Incomplete or rival suffix | 13 | No partial or substituted history can issue a result. |
| Missing current basis custody | 24 | Exact historical reconstruction can finish. Reissue stays disabled. |

The positive progress property is conditional on obtaining a complete exact physical suffix and a currently covered basis.
Recovery, finishing, and serving use weak fairness in that case.
The incomplete cases check safety.

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Compare the journal-only projection | A rival with changed admission evidence reaches recovered state in five transitions. |
| Record admission without its hold | A result survives without its protected basis in two transitions. |
| Skip the chosen release | The old invocation answers after slot reuse should have finished in six transitions. |
| Close by slot without checking the permit serial | A delayed close releases the second read in five transitions. |
| Serve from historical evidence alone | Recovery issues a result with current physical coverage missing in six transitions. |
| Recheck live endpoints while replaying | A covered exact suffix can stall forever with historical issuers offline. Temporal counterexample. |

## General proofs

[OrderedReadReplay.lean](OrderedReadReplay.lean) checks eleven theorems with standard axioms only.

- Either certified combined base plus the complete exact suffix through a chosen cutoff restores one journal and read book. Rival and incomplete suffixes refuse. A physical continuation beyond the cutoff does not enter replay.
- The joint decision uses the actual journal marker and captures its current exact basis. Passing a bare read marker through the journal entry point refuses. Lean rejects the deliberate mutation that reopens that entry point.
- Logical close applies against the exact serial. It advances the ordered position and clears the result and hold together without changing data. The sealed predecessor refuses. A delayed old close preserves the reused slot.
- Starting with an empty sound book, every recovered live result comes from a successful protected admission at its exact frame in the chosen history and holds its original protected basis. Ordinary journal transitions preserve rows and holds.
- The recovered reply path checks current authority and custody after replay. With those conditions and the authenticated original invocation, it recreates the packet without calling its historical issuers.

The read model reuses the original admission, paired-basis, and release invariants.
It instantiates row provenance with the complete chosen operation rather than a separate chosen marker.
The ranked cutoff and the base certification are inputs to the replay proof.
The only authority that chooses a logical close also orders the corresponding read book update.

## Amendments and acceptance programs

[A326–A329](../amendments.md#study-83--2026-11-23) bind complete frame identity, make logical control changes recoverable under original evidence, and distinguish replay from current serving.

- P157. Recover a chosen close and reused slot from either selectable base at a fixed data frontier. Exclude a staged tail beyond the cutoff and refuse a suffix that supplies a rival projected read. Refuse the delayed close of the first permit without releasing the second hold.
- P158. Recover with both original evidence issuers offline. Reissue the exact admitted result while the current authority and required custody are verified. Refuse reissue when the current custody is missing.

## Residue

The model treats evidence validation as historical and immutable for the selected policy and key epoch.
It assumes a genuine stop witness excludes future acquisition under that permit, and that pinned custody still protects any operation allowed to finish.
Complete canonical byte framing, exact current ranked cutoff discovery, and the binding from the named envelope to its certified combined prefix still need refinement.
The pure snapshot projection checks aligned head, retained floor and checkpoint cut for ordinary journal commands.
The real journal-to-snapshot projection still needs exact root registration and identity evidence.
The proofs of ranked replay and sealed activation remain linked through the certified-image interface.
Authority, physical dependency enumeration, endpoint and provider stop, and source-to-target installation still need concrete adapter evidence.
The model relies on fresh invocation identities from the authenticated caller and checks bounded slots and serials.
Actual per-frame and per-checkpoint metadata charges remain to be accounted for and qualified.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner records commands, configurations and raw traces in .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/83-ordered-read-replay/run.py
```
