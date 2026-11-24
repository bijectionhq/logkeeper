# The stream journal: target design

2026-11-24. Owner-approved. This document is the specification that the new Logkeeper journal implements. It is the outcome of:
- four independent designs of the ideal system;
- three second-pass deep dives (fresh-read confirmation, holds versus grace, consensus granularity);
- Study 118 (`verification/118-holds-vs-grace`);
- the RTDB ideal-design study (`/Users/sachaichbiah/code/codesign-agents/reports/rtdb-ideal/REPORT.md`);
- the modularity study (`/Users/sachaichbiah/code/codesign-agents/reports/modularity-study.md`).

The current `src/ordered*` journal and the classic `src/client` and `src/server` stay in place, unchanged, until RTDB has switched. The new journal is built beside them in `src/stream/`, with its contract in the separate crate `contract/` (`journal-contract`).

## 1. What the journal is

A journal is a set of **streams**. A stream is a totally ordered, durable, fenced sequence of opaque **records**. The journal knows nothing about its consumer: no checkpoints, object names, keys, holds, leases, workers, tenants or principals beyond authenticated identities.

## 2. The contract (`journal-contract`)

The contract is the whole interface a consumer sees. RTDB depends on it and never on Logkeeper's internals. The trait, types and errors are already defined in `contract/src/lib.rs`. This section gives their semantics.

| Verb | Semantics |
| --- | --- |
| `create(stream)` | The stream exists, empty: end 0, floor 1, no epoch. Idempotent. Refused with `Deleted` after `delete`. |
| `seal(stream, epoch)` | Fence. Afterwards no append under an epoch below `epoch` commits. Returns the committed end, which contains every append acknowledged before the seal took effect. Sealing twice at the same epoch from the same identity is idempotent. A different identity at an equal or lower epoch gets `Fenced`. |
| `append(stream, epoch, at, payload)` | Commits `payload` as the record at LSN `at` iff `epoch` is the stream's sealed epoch, the caller sealed it, and `at == end + 1`. Returns `at`. Retrying an identical `(epoch, at, payload)` returns `at` even if the first reply was lost. A different payload at a committed `at` returns `Conflict`. |
| `read(stream, from, max, wait)` | Committed records in `[from, from + max)`. If `from` is past the committed end, waits up to `wait` for new commits (long-poll). Returns the floor and the committed end seen. `from < floor` returns `Trimmed`. |
| `head(stream)` | A linearizable committed end: an LSN that was committed at some instant inside the call and is at least every LSN acknowledged before the call started. No clock appears in its safety. |
| `trim(stream, epoch, through)` | Discards records up to and including `through`, where `through` is at most the committed end. Only the sealed epoch may trim. The floor is monotone. |
| `delete(stream)` | Terminal and permanent; the stream ID is never reused. |

**Errors:**
- `Fenced { current }`
- `Conflict { committed_end }`
- `Trimmed { floor }`
- `TooLarge { max }`
- `Full { floor }` (the stream's byte quota is exhausted; `trim` frees space and never needs space)
- `NotFound`
- `Deleted`
- `Unavailable` (retry; the outcome of a mutation may be unknown)

**Contract properties**, which the conformance suite checks on every implementation:
1. Committed records are contiguous from the floor to the end, and irrevocable until trimmed.
2. After `seal(e)` returns `n`, no append under an epoch below `e` commits, and every append acknowledged before the seal is at or below `n`.
3. `head()` is linearizable as defined above.
4. `append` is idempotent for identical retries and conditional on `at`.
5. Reads return exactly the committed records.

**Durability (D03):** an acknowledged record is on two durable copies in two zones. With one zone lost, both survivors must hold it.

**Authorization:** an mTLS identity authorized for the cluster may call any verb on any stream it is allowed to use. Nomination policy (who should seal) is the consumer's business. This relaxes requirement S07 as written, and S07 is an **open owner decision**: implement an optional seal-policy hook (`SealPolicy`, default allow), so S07 can be enforced later without a protocol change.

## 3. The implementation: writer-driven quorum per stream

**Keepers.** Each cluster has keepers, normally three, one per zone, each on a local disk. Each stream has an **ensemble** of three keepers. Keepers never talk to each other on the hot path.

**Writer.** The consumer process that seals a stream is its writer, and it runs Logkeeper's client library (`src/stream/writer`), which is the proposer. The epoch is the ballot.

**Per-stream keeper state:** `promised: (epoch, holder)`, `synced: epoch`, `end`, `commit`, `floor`, `deleted`. It is durable in the keeper's shared log.

**Keeper rules** (wire types in `src/stream/wire.rs`):

| Request | Keeper rule | Durable before the reply |
| --- | --- | --- |
| `Create { stream, ensemble }` | Absent and not tombstoned; idempotent | yes |
| `Seal { stream, epoch, holder }` | `epoch > promised.epoch`, or equal with the same holder. Reply: `synced`, `end`, `floor`, `commit`, and the epoch runs needed to rank histories | yes |
| `Sync { stream, epoch, from, records, complete }` | `epoch == promised.epoch`. Truncates only above `commit`. `complete` sets `synced = epoch` | yes |
| `Append { stream, epoch, at, records, commit }` | `promised.epoch == epoch == synced`, `at == end + 1`, or an identical record already at `at` | yes |
| `Trim { stream, epoch, through }` | Same epoch check; `through <= commit` | yes |
| `Check { stream, epoch }` | Returns `promised`, `synced`, `end`, `commit`. No state change | no |
| `Read { stream, from, max, wait }` | Records up to `commit`, long-polling | no |
| `Delete { stream }` | Permanent tombstone; data removed at the next segment rotation | yes |

**Writer protocol:**
- **seal(e).** Send `Seal` to the ensemble. On a quorum of two promises, adopt the highest history ranked by `(synced, end)`, never by the epoch of the last entry (see `src/client/recovery.rs:3-5`). `Sync` that history to a quorum with `complete`, then serve.
- **append.** Pipelined. A record commits once two keepers acknowledge it at the writer's epoch. `commit` is piggybacked on later appends.
- **Fresh reads, `head`.** Study 29's read index: a `Check` round opened after the invocation, answered by a quorum at the current epoch. If a higher epoch is seen, refuse or retry at the new writer. The writer answers with its commit index. A non-writer answers with the maximum reported end once a quorum reports `commit` at or above it. Batch every waiting `head` into one round per stream per tick, and ride on append acknowledgements when appends are flowing. No lease: no clock appears in any safety argument.

**Shared write-ahead log.** Each keeper keeps one append-only segmented log for every stream:
- records are framed with length and CRC;
- group commit: one write and one sync per round across all streams, with a per-stream byte cap per round;
- a reply follows the covering sync;
- recovery cuts a torn final record and demultiplexes per stream;
- compaction never rewrites every stream: retained data moves to per-stream extents so segments are short-lived, and `delete` forces rotation.

Start from the classic `src/server/journal.rs`, which already has the shared-segment and group-commit shape. Study 117 (`/Users/sachaichbiah/code/logkeeper-k5/verification/117-shared-wal/`) models the shared log.

**Keeper replacement.** A replacement keeper gets a new identity. It is a non-voting learner for each stream until a writer or a background sweeper syncs that stream to it. Until then, the stream's quorum is its two surviving members. A blank keeper must never rejoin under an old identity (Study 117 `EmptyRejoin`).

**Capacity.** Each stream has a static byte quota, and `append` returns `Full`. `trim` needs no space. There is no maintenance lane.

**What is gone, compared with `src/ordered`:**
- grants, enrollments and principal kinds;
- receipts, the retry book and the expiry index;
- holds, barriers, `ReleaseRead` and leases;
- checkpoint preparation, publication, close and settle;
- object references and withdrawal;
- `PublishAndRotate` and key generations;
- funded windows and append classes;
- worker disposal;
- the two-slot whole-image voter media, and per-command prepare and accept over the whole prefix.

## 4. What the consumer (RTDB) owns, for reference

These are not Logkeeper's job, but the journal must not prevent them:
- **Checkpoints** are ordinary records.
- **Pins** for branches, exports and long reads are ordinary records appended by the stream's writer.
- **Object files** use never-reused, epoch-scoped keys, collected by reachability.
- **Encryption and key generations** belong to RTDB; the journal stores ciphertext only.
- **Erasure** is completed by key destruction (D02 extension) in the key authority, after closing outstanding key grants.

## 5. Deployment

Logkeeper ships its own binary (`logkeeper keeper --config FILE`), its own image and its own infrastructure module, which places three keepers in three zones on local disks and outputs a `journal_url`. A consumer receives only the `journal_url` and credentials, and never sees keepers, zones or subnets.

## 6. Verification

- **Lean.** The per-stream keeper and writer protocol refines `PrefixAgreement` and `DurableAcceptor`. The ledger maps directly:
  - ballot = epoch;
  - `prepared` = sealed;
  - `report` = the seal reply;
  - `RankLE` = the `(synced, end)` winner key.

  Prove the five contract properties, with Study 29's read index for `head`.
- **TLA+.** The writer-driven protocol with a zombie writer, AZ loss, keeper replacement, torn tails, a shared log and lost replies, with a reachability witness and a negative control for every guard.
- **Verus.** The keeper rule functions and the writer's acknowledgement and recovery-ranking decisions.
- **Conformance.** `journal-contract`'s suite runs against `MemoryJournal`, `FileJournal` and the Logkeeper client, and checks linearizability with a history checker.
- **Deterministic simulation.** The shipped keeper and writer under seeded faults: crashes, reordering, loss, torn writes and partitions.
