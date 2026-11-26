# Logkeeper

Logkeeper is a Rust journal server and quorum client for named streams of opaque records.
The original quorum client takes the ensemble and the writer epoch from the caller.
The client seals an intersecting quorum before opening a writer.
It reports append durability once a write quorum has persisted the record.
Readers receive committed records in stream order.

## Run locally

Use Rust 1.94.1 or newer.

```sh
cargo test --locked --all-features
cargo run --locked -- 127.0.0.1:7654 ./journal-data 65f66914-8889-40a8-91f6-a31476b84014
```

Run a separate process with its own address, directory, and nonzero UUID for each ensemble member.
Use three independent journals and a quorum of two to tolerate one journal failure.
A restart uses the same durable directory and journal identity.
The serving process takes an exclusive journal lock before accepting traffic.
Run listeners on a trusted private network.
A deployment that needs its own discovery, credential, or placement policy can embed `PreparedJournal` and supply its own listener.

## Keeper-hosted consensus streams

Use the `stream` feature and `logkeeper::stream::consensus::Client` for streams
whose keepers elect a leader and allocate writer epochs. Each keeper uses its
own data directory and the same authenticated inventory and catalog UUID.
For example, the first of four keepers can use this file.

```json
{
  "keeper": "00000000-0000-0000-0000-000000000001",
  "listen": "127.0.0.1:5441",
  "data": "./keeper-1",
  "enrollment": "./registry-1",
  "tls": { "certificate": "keeper-1.pem", "private_key": "keeper-1.key", "ca": "ca.pem" },
  "keepers": {
    "00000000-0000-0000-0000-000000000001": "127.0.0.1:5441",
    "00000000-0000-0000-0000-000000000002": "127.0.0.1:5442",
    "00000000-0000-0000-0000-000000000003": "127.0.0.1:5443",
    "00000000-0000-0000-0000-000000000004": "127.0.0.1:5444"
  },
  "peers": {
    "00000000-0000-0000-0000-000000000001": "127.0.0.1:5541",
    "00000000-0000-0000-0000-000000000002": "127.0.0.1:5542",
    "00000000-0000-0000-0000-000000000003": "127.0.0.1:5543",
    "00000000-0000-0000-0000-000000000004": "127.0.0.1:5544"
  },
  "bulk": {
    "00000000-0000-0000-0000-000000000001": "127.0.0.1:5641",
    "00000000-0000-0000-0000-000000000002": "127.0.0.1:5642",
    "00000000-0000-0000-0000-000000000003": "127.0.0.1:5643",
    "00000000-0000-0000-0000-000000000004": "127.0.0.1:5644"
  },
  "domains": {
    "00000000-0000-0000-0000-000000000001": "zone-a",
    "00000000-0000-0000-0000-000000000002": "zone-b",
    "00000000-0000-0000-0000-000000000003": "zone-c",
    "00000000-0000-0000-0000-000000000004": "zone-a"
  },
  "catalog": "00000000-0000-0000-0000-000000000004",
  "readers": [],
  "writers": ["urn:logkeeper:client:app"],
  "administrators": ["urn:logkeeper:client:app"]
}
```

Issue each keeper a certificate with URI SAN `urn:logkeeper:keeper:<uuid>`,
usable for both TLS client and server authentication. The CA assigns a unique
keeper UUID to each incarnation. Issue the application a client certificate
with the exact URI listed in its roles. Administrators can create, replace and
delete streams. Writers can seal, append and trim. All three roles can read.
The keeper requires three distinct declared failure domains in each roster,
including both sides of a joint configuration. The operator verifies the
actual failure domains.

Create the enrollment directory on trusted storage outside the keeper's data
directory. The provisioning authority writes `placement.json` there with the
same `catalog` and `domains` from the keeper configuration. It also writes
`<keeper-uuid>.provision.json` with `keeper`, the canonical absolute `data`
path, the keeper's `domain`, and `certificate_sha256` as the lowercase SHA-256
hex digest of the configured certificate file.

```sh
cargo run --locked --features stream -- keeper initialize --config keeper.json
cargo run --locked --features stream -- keeper --config keeper.json
```

Initialization consumes the authorized UUID before publishing its media.
Preserve the enrollment records and WAL boundary independently of media loss
and prevent registry rollback. Serving opens only checked, installed media.
Use a fresh UUID after media loss or an interrupted install that consumed the
old UUID. A fresh replacement joins as a learner. After the initial copy,
the leader briefly gates writes and matches the full issued prefix on every
newcomer before joint membership. The consensus development format
predating explicit enrollment requires a fresh installation.

Expose `keepers` addresses to application clients. Restrict the `peers` and
`bulk` addresses to trusted keeper networks, with ingress isolation so
application and bulk traffic cannot exhaust the control listener's
pre-authentication resources. The keeper separates TLS handshakes, authenticated
connection budgets, frame limits, and WAL queue admission. Give each keeper a
dedicated data volume or enforce equivalent bounds on other users of that volume.
Provide separate capacity for the enrollment volume. The keeper accepts data
volumes with an allocation unit up to 16 KiB.

Pass the application certificate paths, the inventory, the catalog UUID, and
an operation deadline to `Client::new`. With an authorized client and three
voter UUIDs, a first write looks like this.

```rust,ignore
use bytes::Bytes;
use journal_contract::{Epoch, Lsn, StreamId};
use uuid::Uuid;

let stream = StreamId(Uuid::new_v4().as_u128());
journal.create(stream, voters, 64 * 1024 * 1024).await?;
let sealed = journal.seal(stream, Epoch(0), Uuid::new_v4()).await?;
let at = Lsn(sealed.head.0 + 1);
journal.append(stream, sealed.fence, at, Bytes::from_static(b"first")).await?;
```

Retain the stream ID across create retries and the writer UUID across seal
retries. An unavailable append has an unknown outcome. Retry the same fence,
LSN and bytes while that fence and record are still retained. A fresh `head`
confirms a quorum after invocation and waits for local application. A `read`
returns one keeper's applied page and may lag. Use `read_at_least` to supply a
minimum head, for example a position returned by an append. The client remembers
an authenticated committed roster by stream and genesis and starts one alternate
if its preferred keeper is still pending after 25 ms. It bounds discovery and
fallback to eight peers each, deduplicates page attempts and uses the operation
deadline. A trusted catalog binding lookup can establish that a stream was
never created. Unreachable or obsolete peers leave that question open.
Records can be up to 4 MiB. Trim advances the logical read floor. Delete is
terminal for a stream ID.

Use `configuration` to fetch a revision, then call `replace` with that revision
and the three desired voters. Retry the same revision and target if the
outcome is uncertain. The keeper commits the exact catalog staging receipt
before entering joint consensus. Once retained, that receipt supports the
matching change during catalog outage. A later leader can finish committed
joint membership without the catalog or original caller.

An administrator can query `replica_generation` on a keeper and call
`retire_copy` with the stream, target keeper, a different keeper serving the
current placement proof, the committed revision and the exact local generation.
The target verifies exclusion from the entire committed roster, including both
sides of a joint roster, before durably detaching that generation. Acknowledgment
means detach is durable. Cleanup resumes after restart and waits for pins on that
generation. Staging records a new generation and its target revision before
copying, then compares the exact receipt, generation and durable log cut before
installation. The keeper retains its term and vote across both transitions.

The configured catalog keeper durably assigns genesis and records discovery
contacts. An unavailable catalog leaves genesis unknown and existing groups
can use authenticated inventory contacts to elect and serve. Creation and
unpublished staging require the catalog. A deployment that needs both
operations to survive a catalog failure needs a separately highly available
catalog with the same linearizable genesis CAS and retained staging semantics.
The shipped catalog has one keeper.

Detected snapshot damage quarantines the affected replica across restarts.
Detected corruption of the keeper identity, WAL, or its trusted boundary
disables the keeper. With the keeper stopped and the WAL intact, restore only
the exact bytes named by the local WAL's snapshot digest.

```sh
cargo run --locked --features stream -- keeper repair-snapshot --config keeper.json --stream STREAM_UUID --snapshot BACKUP_FILE
```

Repair preserves the local term, vote, and log suffix. An indexed snapshot
backup also needs its exact referenced index pages, extents and any legacy
image. Restore those dependencies at their original names before repairing the
root. An unverifiable basis requires a fresh keeper incarnation.

### Keeper storage and upgrade

Admission leaves 64 MiB free for durable protocol control (32 MiB), maintenance
records (8 MiB), maintenance scratch (16 MiB), and bounded external allocations
and filesystem overhead (8 MiB). Ordinary entries reserve bytes and a pending
suffix slot together. A reserved WAL lane services exact snapshot selection and
covered purge alongside the independently admitted control lane. One snapshot
builder at a time reserves up to 12 MiB of scratch on the volume. If the 512-slot
ordinary suffix fills, covered purge can reopen it while bulk is full and
ordinary operations including `Trim` are refused. Application trim still needs
the caller's fence and a committed entry.

Each accepted log entry is a shared immutable segment of at most 5 MiB. WAL
updates write only affected stream leaves (up to 160 KiB each) and a directory
of at most 384 KiB. A sync round takes at most 16 records and stops taking more
after crossing 32 MiB of serialized work. Per-work serialized input is capped
at 68 MiB and 64 appended entries. The directory holds up to 4,096 scopes and
a leaf up to 1,024 accepted entries. Keepers default to 128 locally installed
groups.

A local snapshot writes a root of at most 384 KiB and references payload
already on disk. Its immutable index pages hold up to 128 records each, with
at most 513 pages and 12 changed pages per ordinary build. The first local build
from a legacy image can write all index pages within the same scratch budget.
New appends enforce a 65,536 retained-record ceiling alongside the configured
retained-byte quota. Selection becomes durable through one WAL boundary update
before purge. The cleanup worker considers at most 64 object names at a time
and up to 16 directory entries for one detached generation per pass. Actual
available filesystem space governs reuse, including allocations left behind
by interrupted work and unlinked files with open handles.

The existing bulk ALPN, 1 MiB chunks and `LKRIMG03` wire image remain supported.
Bulk admission is shared by incoming files and private seekable outbound files.
It allows four sessions, up to 256 MiB per file and 512 MiB in total, subject to
available volume space. A sender pins the selected cut and serves the same
bytes at every retry offset. A receiver drops an incomplete session after 30
seconds of inactivity. Size retained data for a wire image within that limit,
including framing and metadata, when replacement by snapshot is required.

The keeper can reopen a selected `LKRIMG03` image in place. A first local snapshot
can reference it as an immutable extent. New selected local roots use
`LKRIDX01` and new WAL directories use `LKRWAL03`. On first startup, an enrolled
framed WAL is migrated through the existing trusted boundary. Budget additional
free space for the encoded live suffix, two allocation units per entry, 160 KiB
plus two allocation units per scope, 1 MiB for the root and overhead, and the
64 MiB headroom. The old WAL stays selected until the new files and boundary
are durable. Before upgrading, prune any former data exceeding the new suffix
or retained-record geometry through supported caller-authorized operations.
Coordinate keeper upgrades before using the new ownership or consensus
commands. Existing application `Read` messages and bulk chunk messages retain
their format. Older keeper binaries require their old media to reopen.

Progress through local pressure requires an exact covering applied cut, enough
allocatable space for the bounded work and continued scheduling of durable I/O.
Protocol recovery also needs eligible peers. Physical write admission resumes
when pins release and the allocator reports enough net space returned.

### Reclamation verification

Local Rust tests exercise both retirement and staging orders, duplicate and
unknown exclusion, restart after durable detach, stale installation callbacks,
same-length wrong log cuts and hard-vote continuity. Storage tests exercise
concurrent ticket settlement and cancellation, measured space refusal,
simultaneous ordinary and bulk byte saturation, full suffix with all bulk
sessions held, incoming admission refusal and retry, and an old seekable
transfer held across selection and purge. WAL fault injection covers synced
files before selection, a synced boundary temporary, durable selection before
purge, and unlink before the writer returns accounting. Integration tests also
reopen framed WAL and legacy images, verify retained bytes, head, trim floor and
membership, and exercise scoped read rejection, one delayed hedge, a disjoint
roster move and a partition. These are deterministic fault cuts and local
filesystem tests. Power-loss behavior depends on the filesystem durability
contract.

The local all-features workspace suite passed 273 tests, including 24 focused
consensus tests. One pre-existing ignored test remained ignored. The default
workspace check and loopback CLI smoke passed. The smoke exercised enrollment,
all three consensus TLS listeners, verified restart, wiped-media refusal and
the legacy keeper CLI.

### Replication admission

Peers classify each AppendEntries request by its decoded entries. Votes,
empty AppendEntries (including fresh-head probes) and batches holding only
blank, membership or staging entries use the control lane. Any batch with an
application command uses the replication lane, which shares the configured
`bulk` address under its own ALPN. Control frames are limited to 64 KiB, and a
control-lane frame carrying application entries is refused. The protocol WAL
queue rejects application entries and oversized metadata. A peer batch holds
at most four entries, matching `max_payload_entries`. An `Admitted` wrapper
decodes only one unwrapped application or staging command.

The receiver reads the 4-byte length before allocating a replication body.
Each in-flight body is charged at four times its encoded size plus 64 KiB to
cover decoding and handoff copies. The receiver allows 256 MiB and 16 frames
in total, with at most 96 MiB and four frames per authenticated sender
across all of its connections and streams. Replication sockets are capped at 32
per receiver and four per sender. Control work is capped at 24 requests in
total and four per sender. At most 64 idle control connections wait for a
header, and the oldest is closed first.

Before dispatch into Raft storage, a follower reserves the batch's upper
bound from the shared disk owner. That bound is the encoded entries plus
768 KiB of WAL metadata and 16 KiB per entry plus one more. Follower appends
use the ordinary physical pool and leave the 64 MiB control and maintenance
floors intact. New follower entries are limited to 496 of the 512 suffix
slots. A busy stream, full transport budget, or refused disk or suffix
reservation produces a retryable `Busy` reply with no acknowledgment. The
leader treats it as a temporary per-target failure. A full suffix also
requests covered purge. The exact ticket travels with the matching ordered
storage write. Cancellation or a dropped socket after dispatch keeps the
charge until the write settles. A failed or partial write keeps the charge and
disables the WAL, and reopening recomputes allocations from the trusted
boundary. Fresh `head`, commit and quorum rules are unchanged.

The durable worker rotates through five queues after each completed round:
peer control, covered maintenance, follower replication, ordinary
application work and maintenance or incoming transfer. Empty queues are
skipped. A round takes at most 16 records and stops after crossing 32 MiB.
Each stream admits one follower batch at a time, so the follower queue holds
at most one batch per stream, at most 16 in total, in FIFO order. A stream
therefore cannot overtake itself, and a ready stream waits behind at most 15
other streams. The per-sender transport caps limit one sender to four of
those slots. This rotation over streams gives the checked `5 * W` service
bound with `W = 16`, assuming each earlier durable round completes. A sender
splits a valid batch that exceeds its lane, and a single entry that cannot fit
is unreachable.

A replica supplies quorum evidence only through Raft's existing voter rules
and only while it is healthy. A quarantined replica refuses the exchange
before storage. On restart, a keeper that led its last term rejoins without
resuming that term's leadership. The vote stays in storage unchanged, and the
keeper still refuses other candidates in that term. A fresh `head` or
configuration read is served only after a leader commits an entry in a new
term, so it includes every write acknowledged before the restart. A
stream's first reads after a full restart wait for that election. The Lean
module `Logkeeper.LeaderJournal.RestartRead` checks this rule, with leader
completeness as a premise, in the Lean worktree's
`verification/lean/restart-read.md`.

Keepers run OpenRaft 0.10.1. Its peer messages differ from 0.9 under
bincode, so the peer ALPNs are `logkeeper-consensus-control/5`,
`logkeeper-consensus-replication/2` and `logkeeper-consensus-bulk/2`. A keeper
on an older version fails the TLS handshake with `no_application_protocol`
instead of failing to decode. Mixed versions are unsupported: upgrade all
keepers in a group together. The application protocol, `LKRIMG03` images
and the on-disk WAL format are unchanged; a test pins the persisted bytes of
votes, log ids, memberships, entries and snapshot metadata to their 0.9
encoding. A leader that cannot confirm a recent quorum now refuses writes
and answers that it has no leader; after 1.8 seconds without a quorum it
gives way to a new leader. Followers run a pre-vote round before raising
their term, so a keeper that rejoins after a partition does not depose a
working leader. A graceful shutdown first transfers every stream the keeper
leads to a caught-up voter, waiting at most 3 seconds, so a rolling restart
does not wait out a lease and an election per stream.

Verus checks the shipped admission, classification, rotation, batch and
restart decisions in `src/stream/consensus/decisions.rs` against laws named
after the Lean theorems. The baseline verifies 48 functions, and 16
production mutations each fail their declared contract. See
`verification/verus/consensus_admission/README.md` for the mapping and the
unverified stateful glue.

Local Rust tests cover these acceptance cuts:

- A mixed batch sent on the control lane is refused. With disk space
  exhausted, the same batch on the replication lane gets `Busy` with no
  outstanding charge and an unchanged log.
- One sender is held at its share and the receiver at its frame limit while
  another sender still enters. A vote and a fresh `head` are served, and a
  covered snapshot and purge commit, all while replication data is saturated.
  Payload resumes after release, and the stopped original voter catches up
  with unchanged membership once the pressure clears.
- With a refusing target, continuous fresh `head` load, a stream busy with
  2 MiB appends and 210 idle authenticated control connections, ten appends
  to an unrelated stream each commit within five seconds. The busy stream
  keeps committing. The refusing target holds no charge, stays at its prefix
  and catches up after its space returns.
- Unit tests cover the per-sender and receiver byte and frame caps, socket
  caps, exact release, control work caps and oldest-first eviction of idle
  control waits. The sender splits oversized valid batches.
- A reservation cancelled before dispatch releases once. A request aborted
  after dispatch keeps its charge until the durable settlement. A racing retry
  gets `Busy` without a second charge, and a later retry succeeds.
- A partial segment, a failed sync, a failure before selection and a failure
  after selection each keep the ticket and disable the WAL. Restart recovers
  the selected cut and clears the charge.
- All five durable queues stay saturated and are served in rotation without
  reordering within a queue.
- A quarantined follower and the leader form a numeric majority, but appends
  and fresh `head` stay unavailable until an eligible voter returns. The retry
  then resolves the unknown outcome.
- A leader restarted with a snapshot older than its acknowledged appends
  does not resume its term. The next fresh `head` returns the last
  acknowledged append from a later term.
- A caught-up newcomer durably confirms the pending entry, which is either the
  joint configuration or the append. The old voters are stopped, so nothing
  commits and fresh `head` stays unavailable until an old voter returns.

The focused consensus tests (36 tests) passed eight consecutive runs. The
all-features workspace suite passed 285 tests. It ignores the one
pre-existing test and the opt-in measurement below. The loopback CLI smoke checked enrollment, all four TLS lanes,
reopening, wiped-media refusal, refusal of the old control ALPN and the legacy
keeper CLI. These checks did not test power loss. Mixed-version keepers are
unsupported.

`measure_consensus_append_throughput` is an ignored test that drives an
in-process four-keeper cluster on one host. Each stream has three voters and
one append in flight. Run it with
`cargo test --features stream --release --lib measure_consensus -- --ignored --nocapture`.
On a 12-core Apple M6 over 10 seconds per case, with Spotlight indexing in the
background, one run measured these rates.

| Streams | Record | Records/s | p50 | p99 |
| --- | --- | --- | --- | --- |
| 1 | 256 B | 623 | 1.5 ms | 2.9 ms |
| 8 | 256 B | 1,548 | 4.2 ms | 17.8 ms |
| 32 | 256 B | 1,948 | 6.9 ms | 206 ms |
| 8 | 64 KiB | 1,134 (71 MiB/s) | 5.7 ms | 22.6 ms |
| 32 | 4 KiB | 1,690 | 8.6 ms | 381 ms |

No follower returned `Busy` and no control request was refused in any case.
Raising the control work caps did not reduce the 32-stream tail. Its cause is
undetermined. Runs on this host varied by more than twofold, and no earlier
baseline exists for the consensus keeper. The vote case confirms the vote was
served. A live leader's lease can still refuse the ballot.

### Journal contract

`ConsensusJournal` implements `journal_contract::Journal` over consensus
streams. Construct it from client credentials and a `JournalConfig` with the
keeper inventory, the catalog keeper, the three voters and the quota for each
stream it creates, the record limit and the operation deadline. Every
principal authorised as a writer can seal, append and trim.

The contract identifies a writer by its authenticated principal. The journal
uses one fixed writer UUID, and the keeper checks the principal on every
seal, append and trim. A same-principal reseal therefore succeeds after a
process restart, and any other principal at an equal or lower epoch is
fenced. The keeper's seal installs the epoch after the expected one, so a
seal that jumps ahead installs each intermediate epoch in turn as separate
compare-and-set steps. Epoch zero is never a sealed writer epoch. `head` is
the keeper's fresh quorum-confirmed head, and `read` returns one keeper's
applied page, which may lag. `append_batch` sends a contiguous group as
keeper batches of at most 256 records and 4 MiB of payload. The keeper
validates each batch's writer, positions, record sizes and quota before it
applies any record, then commits the batch as one Raft entry. A retry of
records already retained with identical bytes returns the batch's last LSN.
An error can leave a committed prefix of whole batches. `Client::append_batch`
exposes one batch directly.

A `JournalConfig` names either fixed `voters` for every stream or a
`placement`: the eligible keepers with their failure domains, plus an
optional `draining` list. With a placement, `create` chooses three eligible,
non-draining keepers in distinct domains by rendezvous ranking of the stream
and keeper identities, so every consumer derives the same voters.
`update_placement` applies a changed eligible set or draining list.
`reconcile_placement` keeps every voter that is still eligible in a distinct
domain, replaces one other voter through `replace`, and returns the new
configuration. Call it until it returns `None`. It also moves a voter whose
keeper does not answer; the stream's leader does the same on its own after
`repair_after_secs`, described below.

Every keeper answers `KeeperStatus`: whether its media is healthy with room
for new streams, how many streams it hosts and leads, and whether it holds a
healthy replica of a given stream. `ConsensusJournal::keeper_status` exposes
it, for example to check that a draining keeper holds no stream. A placed
create first asks the catalog for an existing genesis and reuses it; only a
new stream is placed, skipping keepers that are down or full or carry more
than a quarter above the average stream count, with a fallback to every
accepting keeper. `reconcile_placement` also moves a voter off a full keeper.

Each stream's leader repairs its own stream. A voter that has not
acknowledged the leader for `repair_after_secs` (600 by default), and whose
keeper does not answer or answers without a healthy replica, is replaced by
the best-ranked live keeper with room in a free failure domain, through the
same staged joint change as `replace`. Nothing moves unless two voters are
live, and a keeper repairs at most one stream every 30 seconds. A stream
that lost two voters has no quorum to change its membership and needs an
operator. A replica that hears from no leader for the repair delay asks
other keepers for the stream's current placement; when that placement no
longer names it, the keeper retires its copy, so a voter replaced while it
was down, or moved off by a drain, frees its slot and disk when it returns.

A stream that served no client and appended nothing for `park_after_secs`
(600 by default) is parked: its leader asks each follower holding exactly
its applied log to close the group, then closes its own. A parked stream
runs no timers and sends no heartbeats. A parked follower answers an empty
heartbeat as busy without opening the group; entries, votes, snapshots and
client requests reopen it, and the first request after parking waits for
one election. On one host, 128 idle streams used 0.09 CPU cores parked
against 0.47 unparked.

On peer lanes a keeper keeps at most four requests in flight to each other
keeper, the most a receiver admits from one sender, and queues the rest
instead of opening connections the receiver would refuse. A request that
fails on a pooled connection the receiver had closed retries once on a
fresh one, since peer messages are idempotent. A control frame over its
sender's share waits up to 100 ms for a slot before it is refused.

A keeper with `timed_original` in its configuration, in the stream keeper's
mount format, holds installed keeper trust and, when signing, a commissioned
clock and attestation key. `ConsensusJournal::with_timed_original` installs
the reader's trust and payload limit. `append_timed_original` stages the exact
payload on the first two voters of the stream's sorted roster. Each voter
syncs the stage as a shadow file, samples an upper bound on that durability
event from its clock, and signs it with the roster and configuration
revision. A repeated stage returns the stored sample and never samples again.
The leader verifies both signatures before proposing the record, and the
state machine checks the evidence structure. The evidence and payload are
retained as one record. Reads return only the payload.
`prove_timed_original` returns the verified quorum proof from the leader
after a read barrier. A sample at or after the original's cutoff refuses the
original. Snapshot index spans and wire image frames carry a timed flag in
the high bit of the record length, so earlier images read as ordinary
records. `testing::LocalCluster::start_timed` commissions an Ed25519 key and
a wall-clock sampler on every keeper.

`append` and `append_batch` retry a refusal the keepers report as
`Unavailable`, such as momentarily full write admission or log suffix, with
backoff until the operation deadline. An identical retry is idempotent.

A keeper's `max_streams` counts streams with an open group. Once a deleted
stream's deletion is applied, replicated to every voter the leader sees, and
the group has served no client for 30 seconds, the keeper closes the group and
keeps an in-memory tombstone. Clients are then answered `Deleted` and peers
are refused, and the stream's slot is reused. At startup a stream past the
limit opens on demand instead of being quarantined.

One WAL thread serves every stream on a keeper and takes up to 128 queued
writes per round. A round that runs longer than 20 seconds, such as a disk
sync that never returns, ends the keeper process so the other voters elect
new leaders. Each keeper prints a count of every refusal it answered as
`Unavailable`, by reason, every 5 seconds when the counts change.

The `consensus-testing` feature exports `testing::LocalCluster`. It starts
three voter keepers in distinct failure domains and a catalog keeper on
loopback, with enrolled media and a private CA, issues client certificates
for named principals and can stop and restart individual keepers. The
contract conformance suite and a full-restart test run against it.

```sh
cargo test --locked --features consensus-testing --test consensus_journal_conformance
```

## Integration

Pin a release tag and consume the Rust client from this repository.

```toml
logkeeper = { git = "https://github.com/bijectionhq/logkeeper", tag = "v0.2.0" }
```

A single authority allocates increasing epochs for a stream and supplies an ensemble with intersecting write quorums.
The caller owns checkpoint publication and sets the safe trim boundary.
The journal owns the persisted promise, commit position, and record retention for that stream.
The server, client and journal format ship together.
Version 0.2 adds the durable journal identity handshake from [RTDB](https://github.com/bijectionhq/rtdb/commit/65d0a3d9f1340372d4bd71453b7af980fe02b91f).
For identity-bound streams, the client verifies the journal on connection and requires that identity on operations.
Version 0.1 remains available for installations using the earlier elastic-cell wire layout.
Upgrade those clients and journal services together before using version 0.2 administrative operations.
The `simulation` feature exposes state-machine hooks for tests, with compatibility tied to the pinned release.

The initial release extracts the journal from [RTDB Multi](https://github.com/bijectionhq/rtdb/tree/d445003c4f/rust/crates/logkeeper).
It preserves the original on-disk records.
RTDB's adapter continues to own its storage types, checkpoint policy, and directory membership.

## Ordered journal implementation branch

The `logkeeper::ordered` module implements fixed-cohort grant, append, barrier,
checkpoint and trim decisions. Its voter transport takes an already authenticated
channel and its replay API returns the exact journal interval of a live hold.
The embedding service authenticates coordinator and worker identities before choosing any command.
Checkpoint publication and replenishment require the custodian identity at the exact current grant.
The custodian establishes reconstructability and reserves physical allocations before ordering those commands.

The standalone daemon's `ordered-daemon` feature exposes `logkeeper ordered initialize <manifest>` and `logkeeper ordered serve <manifest>`.
Initialize provisions a fresh voter directory once.
Serve recovers only installed directories and accepts mutual TLS 1.3 using the endpoint certificate pins and roles in the installed manifest.
Peer certificates used for voter traffic have no worker or custodian role in that group.
Application clients retain the installed route and receipt verification keys independently of the serving daemon.
Application wire version 12 (`LKAPPC12`) carries the erasure replay floor and requires signed slot evidence on a successful erasure switch. The withdrawn hold owner query remains restricted to the custodian.
Each page contains at most 64 distinct enrollments in enrollment order and fits the configured application frame.
Pass the last enrollment as a cursor to continue.
Each page reflects its own selected state and gives the journal-time threshold for expiry disposal.
Voter wire version 4 (`LKORPC04`) carries both durable image identities and confirms explicit readback on an erasure accept.
Update the voter cohort and application clients together before using rotation evidence.
Provision fresh voter media and compact recovery images with this protocol.
Keep every previously trusted barrier receipt public key for the lifetime of the logical placement, including its incarnation and generation.
Rotate signers through a cohort successor and distribute the updated trusted `ApplicationRoute.verification_keys` to clients before using its new signers.
Set `predecessor_keys` from the immediate predecessor's active voter roster and carry older public keys in `retained_barrier_keys`.
The seal checks that the successor carries the source's full verification set and that its repair keys come from the source's active roster.
Use the same trusted destination manifest for the seal, reservation, installation, and route publication.
Old public keys verify issued receipts offline. A verified receipt still needs a live hold and its protected basis to serve a read.
Retire old private keys once their cohort and repair signing are finished. Retaining the public keys is sufficient for offline verification.

A voter initialized with an empty `groups` array can persist runtime groups.
Its `management` pins authorize the management protocol over mutual TLS.
Only an administrator can install a group, publish its route or retire it.
`InstallGroup` with `expected_absent: true` can create an absent group.
An identical definition returns the installed route on retry.
A changed definition or a retired deployment is refused.
The daemon syncs the group definition and two voter slots before it publishes the room.
A separate durable `PublishRoute` binds a deployment to its name and organization.
Discover `ApplicationRoute` by deployment UUID or by name using a pinned management credential.
Callers making cell-wide installation or discovery decisions require matching replies from a strict majority of their pinned voters.
`RetireGroup` requires an exact selected checkpoint at the head, a vacant writer, no remaining holds and no checkpoint preparation.
It orders a terminal seal in the next decision slot, then persists a local tombstone that excludes the group from application discovery and service.
The daemon retains sealed voter media for retirement reconciliation.

The ordered implementation can compact an accepted prefix into a bounded recovery base.
Provisioning reserves two durable slots per voter and group.
To select a new slot the voter syncs its body and checksummed generation header together while the prior selected slot stays intact.
Recovery verifies the combined digest before considering a slot, including when a crash partially persists an unsynced replacement.
Before returning any promise or vote the voter installs the same promised ballot and accepted prefix in both slots, in succession.
Either remaining valid slot therefore covers the acknowledged ballot and vote after a tear.
A voter whose slots are both invalid cannot vote.
Recovery syncs the selected slot and its directory before admitting another rotation, including after a warm restart that observes a still-volatile header.
Reusing a slot clears residual bytes from its previous body.
An installed voter needs a filesystem that honours file preallocation and the configured durability barriers.
Ordered window renewal preserves historical window identities and installs a fresh byte cursor.
Each new voter preallocates both files before joining. The volume owner funds their physical footprint, metadata and all co-resident allocations. See the [installation premises](verification/evidence.md#c9-installed-boundaries).
A repair reserves media with `reserve-repair`, orders the exact successor with `seal-repair` on an old coordinator, and consumes the signed package with `install-repair` on each prepared successor.
The predecessor serves no fresh commands after choosing its seal.
The successor installs the exact sealed state in both slots before voting and preserves the original writer, retained receipts, checkpoint holds and paid append cursor.

A custodian orders `PublishAndRotate` against the exact incumbent, head and erasure preparation. One decision selects the clean checkpoint, commits the successor payload key generation and closes new holds on the preceding roots and replay range. Existing hold owners retain access until their holds end.
The command returns signed evidence of a strict accepting majority at the clean checkpoint and successor suffix generation.
Each named voter reads both durable slots after the mirrored write and checks the accepted ballot, prefix and image identities before acknowledgement.
The coordinator obtains those records over authenticated voter channels and signs the rotation receipt and slot evidence together.
The installed client verifies the signature and the cohort it contacted.
Other voters can still hold stale local images, and every eligible recovery majority intersects the acknowledging majority.
The surviving slot of an intersecting voter carries its acknowledged vote or a later one, allowing ranked recovery to select the rotation or a continuation.
The same rule protects the seal through cohort repair.
An exact rotation retry can reissue the evidence while the selected root and suffix generation still match.
