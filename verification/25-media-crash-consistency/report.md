# Study 25 report · Journal media crash consistency

2026-11-22

## Verdict

A replica can publish a compacted base after the head has advanced by preserving the exact ordered suffix shared by both recovery generations.
The compactor captures an immutable cut and finishes the replacement off the append path.
It makes the complete replacement durable before it can become selectable.
Until the selector itself is durable, the old base and the suffix reachable through it remain part of the crash recovery path.
Foreground writes can continue during both the copy and the selector switch under that coverage rule.

A durability vote attests exact bytes and their recoverable location.
A complete local frame is a candidate for reconciliation until the ordered authority certifies it as committed.

## Bounded results

The three safety laws hold in 898 distinct states with two records and 6,578 with three for the shared-suffix candidate.
Each bound permits two different record values, one rotation and one crash.
Every acknowledged record remains retained in these runs.
The head-match candidate also satisfies all three safety laws in 5,390 distinct states with three records.
It additionally satisfies the assertion that the acknowledged head never advanced past the candidate's base cut before publication.
The latter assertion is deliberately false for the shared-suffix candidate.

| Amendment | Weakening | Shortest counterexample |
| --- | --- | --- |
| A86 | `ack_before_bytes` | Write, sync its recovery name, acknowledge, and crash without the frame. Four transitions. |
| A86 | `ack_before_name` | Write, sync bytes, acknowledge, and crash without the recovery name. Four transitions. |
| A87 | `skip_gap` | Write two frames and recover only the later one after the first fails validation. Three transitions. |
| A87 | `intact_means_committed` | Write a record and crash with its frame still visible. Treat it as committed without a certificate. Two transitions. |
| A88 | `publish_incomplete_base` | Capture an acknowledged prefix and publish before a complete image is durable. A crash selects the unusable replacement. Seven transitions. |
| A88 | `unlink_before_selector_sync` | Make the base durable, rename the selector, and reclaim the predecessor. A crash restores the old selector. Ten transitions. |
| A89 | `omit_intervening_tail` | Materialize the captured cut, acknowledge another record, and crash into a replacement missing that suffix. Twelve transitions. |
| A89 | `redirect_before_selector` | Rename, then acknowledge a write reachable only through the replacement. A crash restores the predecessor and loses the write. Twelve transitions. |

The shared-suffix candidate publishes after the head advanced in eleven transitions.
In fifteen transitions the replica acknowledges a write during the copy and another while the replacement selector is volatile, then recovers both through the old selector.
In seventeen transitions the replica acknowledges the two writes, durably switches, removes the predecessor, and recovers the same exact suffix through the replacement.
In two transitions a valid uncertified frame survives recovery while the committed cut stays empty.
These are acceptance traces within the stated bound.
Any positive advancement permanently invalidates a fixed captured candidate under a head-match rule.
Repeated retries or freezing the head can make that rule usable.
Progress under indefinitely continuous load is outside this finite search.

## General proofs

Lean checked nine theorems with standard axioms only. [Proofs](MediaCrash.lean)
For arbitrary record lists, decoding preserves every correctly synced frame and stops at the first invalid slot.
The model proves that each permitted selector has a recoverable base through arbitrary traces in the single-rotation protocol.
A guarded vote gives the exact acknowledged prefix when the media meets its byte and namespace barriers.
A fixed captured prefix and the actual suffix reconstruct the same recovered list under either permitted selector, including later acknowledged appends.
A recovery majority intersects every vote majority under the same membership and therefore has an exact local copy under those media rules.
The head-match arithmetic also holds for arbitrary positions.

Four Lean controls weaken the decoder, predecessor reclaim guard, byte barrier, and name barrier.
Each fails at its declared proof obligation.
The proof does not rely on the number of records or on a bound on the number of appends that can intervene.

## Current journal and remaining work

The standalone journal at revision `85a594e` writes a temporary compacted image, syncs it, renames it, syncs the directory, and then removes older segments.
It processes the capture and bulk work through the journal write path.
Its restart logic scans records with length and CRC checks.
These source observations describe the incumbent, while the model evaluates a different overlap protocol with a shared suffix. [Journal source](../../src/server/journal.rs)

The model assumes that the selected identity is resolved atomically, its successful namespace barrier is binding, and a successful data barrier preserves the exact frames.
The crash checker represents missing and torn frames before that barrier.
Decoder exactness and validation of the full base are explicit obligations.
Detectable damage must fail closed or use a separately verified copy.
An opener that sees a new name after an interrupted process must establish its durability before using it to justify predecessor reclamation.
The incumbent opener removes preceding segments before replaying the selected chain.
A process interruption after rename followed by power loss during recovery is a specific qualification case for the media contract. [Journal open and compaction](../../src/server/journal.rs)
The fault guarantee excludes undetected corruption, media destruction inside a surviving replica, and storage that violates its durability contract.
Group consensus and verified commit recovery, repeated or competing rotations, physical extent selection and active read borrows need their respective refinement and composition checks.
A later study covers warm restart, repeated selector changes, and exact physical pins under this media contract. [Repeated rotation model](../26-journal-rotation/report.md)
Checkpoint publication and logical trim remain stream-level decisions.
The model gives no latency or maintenance throughput bound.

## Amendments

Apply [A86–A89](../amendments.md#study-25--2026-11-22).
They refine the durable-vote boundary and the physical compaction protocol without adding a stream API.

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The TLC release and its checksum are pinned in the shared runner.
Exact commands, checker configurations, proof control diagnostics, and shortest traces are in the study's ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/25-media-crash-consistency/run.py
```
