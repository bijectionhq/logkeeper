# Study 50 · Replace replay evidence with a certified continuation

2026-11-23

## Verdict

An ordered evidence object can be needed by a crash-selectable replay suffix, a live physical borrow, or an outstanding recipient.
Reclaim it only after all three uses are covered independently.
If a recipient accepts a current-state attestation of the exact decision, a certified checkpoint can provide that attestation after the original command and evidence leave.
The same compact state can lie after different original command positions.
An original reply needs its own retained provenance.

## Properties and comparison

[JointCheckpoint.tla](JointCheckpoint.tla) models one move result, its acknowledgment and compaction, one staged checkpoint, a visible and durable selector, provider receipt objects, physical borrows, and one crash.
After publication and before selector sync, either base can still be selected by a crash.
The offline scenario prevents the original consumer from applying the result.

| Policy and scenario | Distinct states | Checked result |
| --- | ---: | --- |
| Certified checkpoint attestation, consumer available | 5,035 | Four safety laws and recovery progress hold up to the bound. |
| Certified checkpoint attestation, consumer unavailable | 141 | Same results hold. A witness drops the original receipt before local acknowledgment. |
| Keep the original receipt, consumer unavailable | 63 | Same safety and restart laws hold. Exhaustive search excludes early receipt reclamation in this case. |

Safety covers exact replay from every surviving selector, exact evidence for an outstanding result, physical borrow protection, and correctness of reissued evidence.
Recovery progress assumes fair application of an exact recoverable base and retained tail.
The retain-original policy keeps the old proof while the recipient remains unavailable and spends a separate retained-evidence credit.

| TLC weakening | Shortest safety counterexample |
| --- | --- |
| Reclaim using only the visible cut | Publish a new visible cut and trim before selector sync. The older crash choice loses its tail in four transitions. |
| Drop the live result row from the checkpoint | Publish an image without the chosen result in three transitions. |
| Claim checkpoint coverage while omitting attestation evidence | Retire the original proof while no selectable image can replace it in five transitions. |
| Ignore physical borrows | Borrow a proof and remove it while the borrow remains live in six transitions. |
| Drop the owed original under a retain-original policy | Reclaim the proof while the unresolved recipient has no equivalent evidence in five transitions. |

## General proofs

[JointCheckpoint.lean](JointCheckpoint.lean) checks nine reported theorems using standard axioms only.
Given sound evidence coverage, exact reclamation preserves the use of every selectable tail, live borrow, and unresolved claim.
Choosing either previously covered base after a crash preserves those conditions.
The checkpoint projection separates the control header, checked stream identity and data-root reference from the logical data history.
An authenticated projection of the unified replay state can attest the exact retained result for its named outstanding participant at the checkpoint's position.

Two unified histories place the same abort at different command positions and produce equal complete joint states.
Their ordered replies differ.
An original position therefore cannot be decoded from the state alone.
A current-state receipt names its own cut, and any still-owed historical reply carries separately retained original evidence.

For result width `W`, header ceiling `H`, and row ceiling `R`, Lean proves that two selectable control images fit within `2 × (H + W × R)` bytes under the stated size premises.
It also constructs a one-slot book that exceeds an arbitrary byte budget when row size is uncapped.
The bound covers the header and result books. Staging, retained tail attachments, borrowed evidence, physical data, and any replay-reservation representation outside the header have separate budgets.
The three Lean controls reject using only the visible replay basis, releasing borrowed evidence, and reissuing a claim for a different stream.

## Amendments

[A192–A195](../amendments.md#study-50--2026-11-23) require complete evidence dependencies, exact authenticated reissue or retention, distinct provenance for historical replies, and explicit encoded size limits.

## Acceptance programs

- P59. Publish and sync the checkpoint for the live result. Trim the original command and evidence, power cycle, reopen, and issue the exact result at the checkpoint cut while the consumer is unavailable. TLC reaches the program in nine transitions. The two removal controls separately exercise an older selector and a live borrow.
- P60. Order the same prepared cancellation before or after an unrelated refused command. Lean checks that the final states agree and the replies differ by position.
- After acknowledgment, advance the checkpoint through exact result compaction. Trim all the old commands and proof bodies, power cycle, and reopen. TLC reaches this in fourteen transitions.

## Residue

Reissue requires the participant to accept authenticated state evidence for that exact claim.
Some effects or reply contracts require the original signed artifact. For those claims, the checkpoint substitute must preserve the original material rather than regenerate a current-cut statement.
The proofs assume accurate evidence dependency enumeration and an authentic current-cut statement.
The checked byte bound applies to supplied encoded sizes. It does not verify a concrete codec, a cryptographic representation, a finite identity rollover policy, or the physical data root.
The two-root rotation proof and the joint replay proof still need composition with the real data-root codec and concurrent physical custody accounting.

## Reproduction

Run with Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner saves model configurations, traces and Lean diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/50-joint-checkpoint/run.py
```
