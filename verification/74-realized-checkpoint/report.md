# Study 74 · Checkpoint the realized move and settle every original scope

2026-11-23

## Verdict

The source keeps one outstanding acknowledgment per original pool.
Each signed pool acknowledgment covers every recovery scope assigned to that pool in the original realized seal.
A scope qualifies when its exact admission fence is effective and the original custodian certifies stable absence or durable charged custody.
The target independently acknowledges the exact installation.
The source can compact the move row after every participant acknowledges.

Keep the current serving window's identity and physical extent in the window book.
The window stays charged through its own lifecycle after the move row compacts.
A canonical control body can carry the original seal after its frame is reclaimed.
Both crash-selectable recovery routes must protect their exact replay inputs and evidence until the stable selector advances.

## Bounded comparison

[RealizedCheckpoint.tla](RealizedCheckpoint.tla) checks two recovery extents at the same pool, an independently backed serving window, and two crash-selectable cut references.
TLC checked four invariants over 89 distinct states.
A five-transition witness reclaims the old frame and reopens the realized vector while the second scope is still unsettled.
An eight-transition witness certifies absence for one scope and continued custody for the other, compacts the source row, and reaches a checkpoint that still carries the serving window.

| Weakening | Shortest counterexample |
| --- | --- |
| Acknowledge a pool after one extent settles | Install, settle one of the two original extents, and acknowledge the entire pool. Three transitions. |
| Publish a truncated control body | Install and publish a checkpoint without the entire vector for the still-owed move. Two transitions. |
| Substitute a same-price extent in the control body | Install and publish a checkpoint that resolves a different original physical version. Two transitions. |
| Reclaim against the visible selector alone | Install, expose the new checkpoint, and reclaim the frame while power loss can still select the old cut. Three transitions. |
| Drop the serving window when compacting its move | Install, settle both scopes, acknowledge the pool, and compact. The active window's binding disappears in five transitions. |

## General proofs

[SealBody.lean](SealBody.lean) checks six theorems over a concrete canonical field layout.
A body encodes the exact source lineage, move slot and serial, ordered seal position, target placement, append extent, and complete ordered recovery list.
Each extent carries the original pool incarnation, local physical serial, custody key, binding, and byte charge.
The parser applies the byte ceiling before splitting the body into fields.
It rejects truncated and extra data and recovers exactly the canonical encoded body.
With word width `W` and a limit of `N` recovery extents, the seal body occupies at most `1 + (7 + 5 * (N + 1)) * W` bytes.
An authenticated named envelope body with the same atom decoder opens to the same exact realized record and retains the manifest's required evidence.

[CompleteSettlement.lean](CompleteSettlement.lean) checks seven theorems.
The checkpoint reader retrieves the original record by its source slot and checks lineage, move serial, outcome, and binding, and requires the stored seal position to fall within the chosen control cut.
The actual ordered source reducer refuses a partial pool report and leaves its book intact.
An authenticated complete certificate removes only its own participant from the source row.
A remaining participant prevents compaction of the realized body.
Once the source reducer allows compaction, the outcome and its realized slot can disappear while the independent current window stays.
The existing evidence retirement predicate refuses removal of any frame still used by either selectable recovery route.
The Lean negative control weakens the pool certificate to one matching extent and fails the all-scope proof.

## Amendments

[A290–A294](../amendments.md#study-74--2026-11-23) define the complete participant acknowledgment, bound and authenticate the realized body, preserve both recovery bases, and separate the serving window from its move result.

## Acceptance coverage

- P131. Reject a signed report for only one of two original same-pool scopes. Accept a complete report with one verified absence and one retained custody claim.
- P132. Drop the old frame once a stable certified checkpoint supplies the exact outstanding realized record. Refuse the truncated or substituted checkpoint and the early frame reclaim.
- P133. Compact the settled move with a separately live serving window. Its exact binding remains in the recovered control cut.

## Residue

The model fixes the seal body format and validates its structure and limits.
The atom decoder and authenticated catalog are explicit inputs.
The deployment still needs concrete scalar, custody-key, and binding encodings with bounded widths and content-addressed immutable lookup.
The typed control composition covers selection and slot recovery for the realized record.
The full serialized control and command bodies, population from arbitrary ranked histories, and alternate historical bases with different exact suffixes still need a combined refinement.
The pool attestation verifies exact scope coverage from supplied authenticated fence, absence, or custody evidence.
Concrete provider events must establish those facts under the fault envelope.
The finite study covers a chosen move with committed installation.
Canceled plans use the distinct existing path for closing every originally planned key, including scopes that never received a grant.
The seal body bound excludes enclosing control records, authentication material, and external dependency storage.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records exact commands, configurations, theorem checks, and traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/74-realized-checkpoint/run.py
```
