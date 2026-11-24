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

The consumer depends on the `Journal` trait in `contract/src/lib.rs`. Each call
returns a boxed, sendable future yielding a `Result<T, JournalError>`.
`StreamId(u128)` names a stream, `Epoch(u64)` is its writer fence, and `Lsn(u64)`
is its record position. `Identity` is the caller's authenticated client
certificate URI SAN. A handle carries the identity. The first record is at
LSN 1. The **head** is the last committed LSN, or 0 for an empty stream. A
**floor** is the first retained LSN. A `Page` contains `floor: Lsn`,
`records: Vec<(Lsn, Bytes)>` and `head: Lsn`, all from one keeper's view.

| Call | Result | Semantics |
| --- | --- | --- |
| `create(stream: StreamId)` | `()` | Create an empty stream with head 0, floor 1 and no epoch. Idempotent. A deleted ID cannot be reused. |
| `seal(stream: StreamId, epoch: Epoch)` | `Lsn` | Fence lower epochs and return the head, which covers every earlier acknowledged append. An equal-epoch retry by the existing proposer is idempotent. A new proposer at the same epoch is fenced, including a restarted writer using the same identity. |
| `append(stream: StreamId, epoch: Epoch, at: Lsn, payload: Bytes)` | `Lsn` | Commit at `at == head + 1` under the sealed epoch and identity. An identical retained retry returns `at`. A different payload at a committed position returns `Conflict`. |
| `read(stream: StreamId, from: Lsn, max: usize, wait: Duration)` | `Page` | Read the contiguous committed slice in `[from, from + max)` through the serving keeper's head. Wait up to `wait` for records when `from` exceeds the observed head. Try another keeper if the first cannot supply the requested records. Return `Trimmed` only if the requested start is unavailable and is below an observed floor. A page can lag `head()`, include records another keeper trimmed, or include retained records until the serving keeper observes a deletion. |
| `head(stream: StreamId)` | `Lsn` | Return a head that existed during the call and covers every LSN acknowledged before the call began. |
| `trim(stream: StreamId, epoch: Epoch, through: Lsn)` | `()` | Advance the floor through `through + 1` under the sealed epoch and identity. `through` cannot exceed the head. The floor never decreases. |
| `delete(stream: StreamId)` | `()` | Permanently tombstone the stream ID. A keeper with a tombstone refuses subsequent reads and mutations other than an idempotent delete. |

| Error | Meaning |
| --- | --- |
| `Fenced { current: Epoch }` | A higher epoch has sealed, or a different proposer sealed this epoch. |
| `Conflict { head: Lsn }` | The requested position or payload conflicts with the journal. |
| `Trimmed { floor: Lsn }` | A requested position below an observed floor is unavailable. |
| `TooLarge { max: usize }` | The payload exceeds the record limit. |
| `Full { floor: Lsn }` | The stream's byte quota is exhausted. Trim frees quota and needs no space. |
| `NotFound` | The stream does not exist at the responding authority. |
| `Deleted` | The stream was deleted. |
| `Unavailable` | Retry. A mutation's outcome may be unknown. |

Committed records are contiguous and immutable. Seal covers acknowledged
appends and prevents lower epochs from committing new records. Head is
linearizable. Append is conditional and supports retained identical retries.
The conformance history checker compares a read's exact payloads and bounds
with committed history, including prefixes retained below another keeper's
floor. Writes and head use quorum confirmation.

An acknowledged record has two durable copies in different zones. If one
zone fails, the surviving copy is sufficient for recovery, which copies the
record to both survivors.

An mTLS identity listed in `clients` may read and check head. Only identities
listed in `writers` may create, seal, append, trim or delete. The optional
`SealPolicy` defaults to allow. No policy is shipped. The consumer owns the
takeover policy and applies records through the head returned by seal before
serving. A stream moved between ensembles admits writes through at most one
authority across crashes and stale routes.

## 3. The keeper protocol

A stream's **ensemble** is its ordered array of three `KeeperId(u128)` values,
normally one per zone. The writer drives the protocol and the keepers never
coordinate with each other on the hot path. The authenticated transport
supplies the caller `Identity`. Mutating messages carry no claimed identity.
One proposer drives a given epoch. The proposer uses its certificate
identity and shares one writer state among its handles. A writer instance generates a proposal ID and shares it across its handles.
A takeover elects a fresh epoch. A reconnect at the same epoch retries the
existing proposal. The keeper stores and echoes the proposal ID with the promise. Seal requests and
stored or returned promises require the 16-byte proposal ID.

A keeper's **tail** is the last durable LSN, which can include accepted,
uncommitted records. The keeper's **head** is the last LSN it knows to be
committed. `StreamView` contains `promised: Option<(Epoch, Identity, u128)>`,
`synced: Option<Epoch>`, `tail: Lsn`, `head: Lsn`, `floor: Lsn`,
`runs: Vec<EpochRun>`, `ensemble: [KeeperId; 3]` and `learner: bool`.
Each `EpochRun { epoch: Epoch, first: Lsn, last: Lsn }` covers an inclusive
range of records from one epoch. The keeper also persists its deletion
tombstone.

### Requests

All successful mutations are durable before their replies. Idempotent
replies can use existing durable state. `Check`, `Read` and `Recover` only
observe state. `Check` and `Read` require client authorization. All other
requests require writer authorization.

| Request | Keeper rule |
| --- | --- |
| `Create { stream: StreamId, ensemble: [KeeperId; 3] }` | Create if absent and the ensemble contains three distinct nonzero IDs. A keeper outside the ensemble starts as a learner. |
| `Seal { stream: StreamId, ensemble: [KeeperId; 3], epoch: Epoch, proposal: u128 }` | Require the current ensemble, policy approval and a higher epoch or the same epoch, authenticated identity and proposal ID. Reply with the keeper view. |
| `Sync { stream: StreamId, epoch: Epoch, floor: Lsn, from: Lsn, records: Vec<Bytes>, runs: Vec<EpochRun>, head: Lsn, complete: bool }` | Require the promise. Stage the selected history with its exact epoch runs and preserve the prefix through the keeper's head. A staged floor at `from` can skip a trimmed prefix. The view, and so every Seal and Check reply, changes only when a complete Sync installs the staged history and sets `synced`. A new promise discards staged records. An empty, incomplete Sync can advance a synced keeper's floor over a discarded prefix. |
| `Append { stream: StreamId, epoch: Epoch, at: Lsn, records: Vec<Bytes>, head: Lsn }` | Require the promise and a synced voting member. Extend at `tail + 1` or verify the entire retry range. An empty append can publish the head without adding a record. The published head must fit the resulting tail. |
| `Trim { stream: StreamId, epoch: Epoch, through: Lsn }` | Require the promise and a synced voting member. Discard through the requested position at or below the local head. |
| `Check { stream: StreamId, epoch: Epoch }` | Return the durable view. The caller uses the requested epoch to identify eligible replies. |
| `Recover { stream: StreamId, epoch: Epoch, from: Lsn, max: u32 }` | Require the promise. Read retained accepted records, including records above the local head, with no wait. |
| `Read { stream: StreamId, from: Lsn, max: u32, wait_ms: u32 }` | Read retained committed records up to the local head. A page can stop early at the wire byte limit. When the start is past the head and `max` is positive, wait up to `wait_ms`. |
| `Delete { stream: StreamId, ensemble: [KeeperId; 3] }` | Require the current ensemble and membership. Install a permanent tombstone. Reply after a background rotation has durably retired the files containing its ciphertext. |
| `Replace { stream: StreamId, epoch: Epoch, from: [KeeperId; 3], to: [KeeperId; 3] }` | Require the promise and a completed Sync. Install a valid ensemble differing in one slot, with the keeper a member of the new ensemble. The proposer installs both survivors before installing the learner. |
| `Batch(Vec<Request>)` | A node-level envelope of independent single-stream requests from one client process. Authorize each request separately. Admit every authorized request to the same round, decide them in arrival order and reply after that round's single sync. Each request keeps its own rule, refusal and fence. Refuse an empty or nested batch. |

### Replies

| Reply | Meaning |
| --- | --- |
| `Created` | The stream exists. |
| `Sealed(StreamView)` | The authenticated promise is durable and the view describes the keeper's history. |
| `Synced { tail: Lsn }` | The keeper has durably staged or installed the requested range. `tail` is the view's tail. |
| `Appended { tail: Lsn }` | The keeper has durably accepted the append or already held the same range. |
| `Trimmed { floor: Lsn }` | The keeper has durably advanced its floor through the requested position. |
| `Checked(StreamView)` | The keeper's durable view. |
| `Records { floor: Lsn, records: Vec<(Lsn, Bytes)>, head: Lsn }` | One keeper's retained slice. For `Read`, every position is at or below `head`. For `Recover`, the slice can reach the tail. |
| `Deleted` | The stream has a durable tombstone. |
| `Replaced` | The keeper has installed the new ensemble. |
| `Refused(Refusal)` | The keeper refused the request. |
| `Batch(Vec<Reply>)` | One reply for each request of a `Batch`, in request order. |

### Refusals

| Refusal | Meaning |
| --- | --- |
| `Fenced { promised: Epoch }` | The request lacks the current epoch and identity promise. |
| `NotSynced` | The requested epoch has not synced, or the operation requires a voting member. |
| `Gap { head: Lsn }` | The requested range would leave a gap. |
| `Conflict { head: Lsn }` | The requested range conflicts with the keeper's history. |
| `BelowFloor { floor: Lsn }` | The start is below the keeper's floor. |
| `AboveHead { head: Lsn }` | A requested bound exceeds the keeper's head or would publish beyond its resulting tail. |
| `Full { floor: Lsn }` | The stream has exhausted its quota. |
| `TooLarge { max: u32 }` | A record exceeds the configured record size limit. |
| `NotFound` | The stream is absent. |
| `Deleted` | The stream has a tombstone. |
| `Unauthorized` | The request failed authorization, policy or ensemble validation. |
| `WrongEnsemble { ensemble: [KeeperId; 3] }` | The supplied ensemble differs from the keeper's ensemble. |

### Writer and transport

- **Seal.** From two durable promises, choose the history with the highest
  `(synced, tail)`. Fetch accepted records with `Recover` and install that
  history with complete `Sync` on a quorum. Publish the adopted head to a
  quorum before returning it. Retry the selected history at the same epoch
  after an uncertain result.
- **Append.** Pipeline independent keeper lanes. Each lane sends the
  contiguous run of known records from its tail in one `Append`, so
  concurrent appends to one stream share a keeper round. The writer keeps
  committed payloads, within a byte bound, until every lane has accepted
  them. A keeper checks capacity for a new append. An identical retained
  retry bypasses capacity checks. The writer can discard its pending suffix
  after current capacity refusals at its first position from all three
  lanes, provided no unanswered append can still reach that position. An
  unanswered append pins its assigned bytes until the position is chosen
  or the epoch ends. A capacity failure without definitive refusal of the
  suffix returns `Unavailable`. After an uncertain result a lane resends
  one record and adopts the keeper's tail up to the highest position the
  writer has assigned. Two
  durable acceptances at the writer's epoch choose the record. Publish the
  head to a quorum before acknowledging the append, using the head on
  subsequent or empty appends. An isolated append takes an accept round
  followed by a publication round. If the first accept could advance the
  head, one keeper could serve the record while the other two fence that
  writer and adopt a history without it. If the writer instead acknowledged
  on acceptance alone, a fresh read index could sample the acknowledged
  tail while every eligible head remained behind it. With no subsequent
  write and the writer gone, nothing would publish that head. A fence or
  any other publication failure after choice returns `Unavailable`.
- **Head.** Open a fresh `Check` round after the invocation and batch callers
  waiting when it opens. A writer can use append replies from requests sent
  after the round opened. It covers the sampled tails with a chosen head and
  confirms publication. An observer's read index is the maximum tail of an
  eligible quorum at the same promise and synced epoch, from its first
  complete round. It requires quorum head coverage for that position and
  returns it. Later rounds wait for coverage of the same index and do not
  resample it, so continuing appends cannot starve the call. The freshness
  and quorum rules use no leases.
- **Read.** Try the nearest keeper first. Each successful page comes from
  one keeper, with the first reply's head bounding any subsequent chunks.
  Fall back if the keeper cannot supply the requested records. TCP discovery
  ranks the routes by connection time, independently of ensemble order.
  Explicit routes use their supplied order.
- **Replacement.** A new keeper has a new identity and starts as a
  non-voting learner. A sweep plan retains its proposal ID across retries.
  The sweeper seals the two survivors and selects and publishes their adopted
  history, syncs the learner, then replaces the lost member on both survivors
  before installing the new ensemble on the learner. A stale writer cannot use an old ensemble to obtain a write
  quorum.
- **Transport.** `Transport::identity()` is the authenticated caller.
  `read_order(ensemble)` supplies member preference, defaulting to ensemble
  order. `call(keeper, request)` returns a boxed future for a reply or
  `TransportError` (`Unreachable`, `TimedOut`, or `Protocol(String)`).
  A capacity refusal ends delivery of that call. If another copy can still
  reach the keeper, the transport returns an error.
  TLS uses `logkeeper-stream/2`. A big-endian u32 length prefixes each
  protobuf request or reply. The payload limit for a frame is 64 MiB.
  A process shares one long-lived connection per keeper among all its
  streams. Requests queued while a frame is written are coalesced into one
  `Batch`, up to 4 MiB, and frames are pipelined. The keeper decides a
  connection's frames concurrently and answers them in frame order. Waiting
  reads, deletes and requests of 1 MiB or more use separate pooled
  connections, so they never delay the shared connection's replies.

### Keeper storage

One append-only segmented WAL per keeper carries all streams. A frame records
length, CRC, stream and fragment boundaries. A round admits whole
queued envelopes until it holds at least `round_requests` requests. A round
uses at most `round_bytes_per_stream` WAL bytes per stream and fits in the
current 64 MiB segment. Large entries can span rounds and segments. One write
and sync cover a round's mutations. Recovery cuts a torn final frame and
discards incomplete entries. A continuation marker carries unfinished
fragments across a physical rollover. A fresh segment opened after recovery
starts without those fragments.

At a boundary between admissions, a background worker copies pending
retained and staged records into a shared extent pack. It publishes a single
keeper-wide index with the stream views, extent references, and first WAL
segment to replay. The segment name is durable before checkpointing starts.
The worker makes the new pack and its name durable before atomically replacing
and syncing the index. It unlinks the covered segments and obsolete packs
only after the index is durable. A crash before publication leaves the old
index and WAL authoritative. A crash after publication uses the new index
and can finish removing obsolete files. Each rotation uses a constant number
of file and directory syncs.

A delete first syncs its tombstone in the WAL. Its checkpoint copies only
live records into a new pack and retires all old packs and the covered WAL
before replying. The worker also reclaims unreferenced packs during regular
rotation. When mixed packs occupy more than twice their live bytes plus one
segment, the next rotation rewrites them. Rounds continue during the copy and an
idempotent delete waits if its cleanup is outstanding. Reads after a keeper
installs the tombstone are refused immediately. Removal is from the keeper's
durable file namespace. RTDB completes cryptographic erasure as described in
section 4.

Startup loads the index and replays its suffix before serving. Index loading
reads record metadata without scanning packed ciphertext. Startup schedules
any resulting checkpoint work in the background. When the uncheckpointed WAL
reaches four segments' worth of bytes, keepers finish the admitted batch and
ask new mutations to retry until checkpoint progress frees space.
Observations keep running. The replay bound is 256 MiB plus one admission of
whole, wire-bounded envelopes and their WAL framing. The suffix charge is
restored on restart, so repeated crashes cannot reset this limit. Each stream
has a static quota. Trim can advance the floor without available quota.

## 4. What the consumer (RTDB) owns, for reference

These are not Logkeeper's job, but the journal must not prevent them:
- **Checkpoints** are ordinary records.
- **Pins** for branches, exports and long reads are ordinary records appended by the stream's writer.
- **Object files** use never-reused, epoch-scoped keys, collected by reachability.
- **Encryption and key generations** belong to RTDB; the journal stores ciphertext only.
- **Writer takeover** (S07 takeover half, an RTDB requirement):
  - A writer is replaced only after its lease record in the stream has lapsed (plus drift), or after it released the stream with a `Lease{until: now}` record. Reachability failure alone triggers no seal.
  - The writer appends a lease record only while idle, since commits prove it is alive. Parked databases need none.
  - A candidate reads the stream through `head` before sealing.
- **Catch-up before serving:** after `seal` returns head `n`, a new writer applies through `n` before serving. The conformance suite states this as a consumer obligation.
- **Erasure** is completed by key destruction (D02 extension) in the key authority, after closing outstanding key grants.

## 5. Deployment

Logkeeper ships its own binary (`logkeeper keeper --config FILE`), its own image and its own infrastructure module, which places three keepers in three zones on local disks and outputs a `journal_url`. A consumer receives only the `journal_url` and credentials, and never sees keepers, zones or subnets.

### Formats shared by the keeper, writer and deployment

`journal_url`: `logkeeper+tls://HOST:PORT,HOST:PORT,HOST:PORT`, listing the cluster's keepers. A keeper's identity (`KeeperId`) is the UUID in its certificate's URI SAN `urn:logkeeper:keeper:UUID`. The client presents its own certificate, key and CA separately. `create` uses the first three keepers as the ensemble unless one is given.

Keeper configuration (JSON, `logkeeper keeper --config FILE`):

```json
{ "keeper": "UUID", "listen": "0.0.0.0:5448", "data": "/var/lib/logkeeper", "zone": "eu-north-1a",
  "tls": { "certificate": "PATH", "private_key": "PATH", "ca": "PATH" },
  "clients": ["urn:logkeeper:client:NAME"],
  "writers": ["urn:logkeeper:client:NAME"],
  "limits": { "stream_quota_bytes": 8589934592, "max_record_bytes": 33554432, "round_bytes_per_stream": 4194304, "round_requests": 64 } }
```

### Storage premises and deployment qualification

Qualify these premises on each deployed filesystem, mount, kernel, and device
combination. Cut power or use an abrupt reset with equivalent storage fault
semantics on the same device, reopen the keeper, and record the surviving names
and exact bytes. The [deployment qualification](../deploy/README.md#qualify-fsync)
defines the observer, fault controls, and evidence to retain.

| Premise | Qualification test |
| --- | --- |
| A successful file sync preserves the file's written bytes and length, including a truncation. | Reset after acknowledged rounds and at the WAL, pack, index temporary file, and recovery truncation sync boundaries. Compare retained bytes and lengths against the observer. The reply-before-sync build must fail acknowledged-record reconciliation. |
| A successful directory sync preserves preceding creations, renames, and removals in that directory. | Reset after the segment-name, pack-name, index-name, and retirement directory syncs. Verify that the recovery boundary and every referenced pack exist, that the selected index opens, and that durably retired names stay absent. |
| Same-directory rename atomically replaces the index. Between rename and directory sync, recovery may see either complete index. | Reset around the temporary index file sync, rename, and parent directory sync. Before rename the old index must open. After rename and before directory sync either complete index may open, with its referenced storage intact. After directory sync only the new index may open. Compare both paths against the same observer history. |

The keeper's byte proofs use a single checksum premise. The shipped
`crc32fast` backend computes the IEEE CRC-32 defined in
[RFC 1952 §8](https://www.rfc-editor.org/rfc/rfc1952#section-8) over the
input octets in order, including when supplied in multiple
[`Hasher::update` calls](https://docs.rs/crc32fast/1.5.0/crc32fast/struct.Hasher.html).
The proofs reject a checksum that differs from the checksum of the received
bytes. Different bodies can share a CRC.

## 6. Verification

- **Lean.** The per-stream keeper and writer protocol refines `PrefixAgreement` and `DurableAcceptor`. The ledger maps directly:
  - ballot = epoch;
  - `prepared` = sealed;
  - `report` = the seal reply;
  - `RankLE` = the `(synced, tail)` winner key.

  Prove the five contract properties, with Study 29's read index for `head`.
- **TLA+.** The writer-driven protocol with a zombie writer, AZ loss, keeper replacement, torn tails, a shared log and lost replies, with a reachability witness and a negative control for every guard.
- **Verus.** The keeper rule functions and the writer's acknowledgement and recovery-ranking decisions.
- **Conformance.** `journal-contract`'s suite runs against `MemoryJournal`, `FileJournal` and the Logkeeper client, and checks linearizability with a history checker.
- **Deterministic simulation.** The shipped keeper and writer under seeded faults: crashes, reordering, loss, torn writes and partitions.
