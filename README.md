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

To run consensus keepers in production, see the [deployment
guide](docs/deployment.md) and its [runbooks](docs/runbooks/). Packaging
(image, systemd unit, Kubernetes manifests, example configs) is in
[`deploy/consensus/`](deploy/consensus/).

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
old UUID. A fresh replacement joins as a learner.

Re-initializing a keeper after losing its data volume always needs a new
keeper UUID, even when the registry was lost too and `keeper initialize`
accepts the old one again. Each installation draws a new media
incarnation, and every keeper records in its registry, in
`<keeper-uuid>.incarnations.json`, the incarnation it first saw each peer
under. If the old UUID is reused anyway, its peers still know its old
incarnation and say so in their ping answers. The keeper then marks itself
reused, durably, and logs it. A reused keeper never registers a stream it
does not hold because a peer or a bootstrap names it, so it cannot come back
as an empty voter and help a lagging voter erase committed entries. It takes
replicas only through staging, as a replacement. Peers that saw the other
incarnation stop counting its vote and pre-vote grants. Its old streams
report no replica on it, so their leaders replace it after
`repair_after_secs`. A stream whose other healthy voter is also down stays
unavailable until that voter returns. Give the keeper a new UUID and retire
the old one. After the initial copy,
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
an operation deadline to `Client::new`. With a replicated catalog, also pass
its voters to `Client::with_catalog_voters`. With an authorized client and three
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
an authenticated committed roster by stream and genesis and starts an alternate
if its preferred keeper is still pending after 25 ms, or at once when that
keeper fails. A read with a long-poll `wait` is expected to wait, so it hedges
only once the wait plus 250 ms has passed, and an empty page from a keeper that
waited it out answers the read; each further hedge waits twice as long. It bounds discovery and
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

The catalog durably assigns genesis and records discovery contacts. An
unavailable catalog leaves genesis unknown and existing groups can use
authenticated inventory contacts to elect and serve. Creation and unpublished
staging require the catalog.

By default the configured `catalog` keeper holds the catalog alone. To keep
creation and staging available through the loss of a keeper, give every
keeper the same `catalog_voters`: three sorted keeper UUIDs in distinct
failure domains, one of them the `catalog` keeper.

```json
  "catalog": "00000000-0000-0000-0000-000000000004",
  "catalog_voters": [
    "00000000-0000-0000-0000-000000000002",
    "00000000-0000-0000-0000-000000000003",
    "00000000-0000-0000-0000-000000000004"
  ],
```

The catalog is then a consensus stream of its own, with the reserved ID
`u128::MAX`, whose genesis comes from this configuration. Each catalog voter
registers and initializes it at startup. Only its leader appends, with an
internal writer fence and at exactly the next position, so claims keep the
first-claim-wins rule and stages keep the exact-receipt rule. Clients may
read the stream but not write, seal, trim or delete it.

- **Lookups:** any catalog voter answers a lookup it finds in its applied
  records. It may lag the leader, which is harmless because a genesis never
  changes and contacts are hints. Only the leader, after a read barrier,
  answers that a stream does not exist.
- **Claims and stages:** a follower answers with its leader. The leader takes
  a read barrier, catches up, and appends.
- **Outages:** with one catalog voter down, creation, staging and repair
  continue. With two down, creation and unpublished staging fail with
  `Unavailable`; existing streams keep serving, and a cold client still finds
  a stream that the remaining voter has applied.
- **Compaction:** when more than 1024 records follow the last checkpoint,
  the leader appends a checkpoint of every entry and trims the records
  before it.
- **Maintenance:** the catalog stream is never parked or deleted. Its leader
  repairs it like any other stream, so a catalog voter silent for
  `repair_after_secs` moves to a live keeper in a free domain. The configured
  `catalog_voters` then only serve as first contacts. Leader hints lead to
  the rest.

**Migration:** stop every keeper, add `catalog_voters` to every keeper and
consumer configuration, and restart. The first record of the replicated
catalog is a seed that the `catalog` keeper appends as its leader: a
checkpoint of its single-keeper entries, which may be empty, and a seed
marker. Another leader hands leadership to the `catalog` keeper for this.
Until the seed is complete the catalog refuses claims, stages and "not found"
answers, so it needs the `catalog` keeper once, at the first start. After
that the single-keeper entries are never read or changed again. A consumer
that still lacks `catalog_voters` can still reach the `catalog` keeper, but
it does not follow a leader hint, so its creates fail while another keeper
leads.

A retained record, segment slice or snapshot that fails its checksum or does
not decode quarantines the replica durably: a marker in the registry
(`<keeper-uuid>.quarantine.json`) that survives restarts. The keeper reports
the replica unhealthy in `KeeperStatus`, so the stream's leader replaces it,
and answers `JournalError::Corrupted`. Another failure, such as a read error,
takes the replica out of service only until the keeper restarts. An
administrator clears a marker online (`Client::clear_quarantine`,
`ConsensusJournal::clear_quarantine`) or offline on a stopped keeper. Clear
it only once repair has replaced or restored the replica: a cleared copy
votes again with whatever it still holds.

```sh
cargo run --locked --features stream -- keeper clear-quarantine --config keeper.json --stream STREAM_UUID
```

Detected corruption of the keeper identity, WAL, or its trusted boundary
disables the keeper under strict default startup. With the keeper stopped and
the WAL intact, restore only the exact bytes named by the local WAL's snapshot
digest:

```sh
cargo run --locked --features stream -- keeper repair-snapshot --config keeper.json --stream STREAM_UUID --snapshot BACKUP_FILE
```

Repair preserves the local term, vote, and log suffix. An indexed snapshot
backup also needs its exact referenced index pages, extents and any legacy
image. Restore those dependencies at their original names before repairing the
root.

When a WAL segment is damaged and strict startup refuses the keeper, offline
salvage on the stopped keeper lets it start again:

```sh
cargo run --locked --features stream -- keeper salvage --config keeper.json
```

Damage in a segment wholly before the WAL checkpoint costs only the streams
the checkpoint names as holding payload in it. Those are quarantined and the
rest keep serving, since every vote and ownership change is in the
checkpoint. A damaged frame past the checkpoint could have held any
stream's vote, trim or deletion, so salvage quarantines every stream on the
keeper, and it refuses on a keeper that holds catalog records. Either way it
writes a clean checkpoint and boundary, the keeper starts strictly, and
repair replaces the quarantined replicas. Strict startup is unchanged.
An unverifiable basis requires a fresh keeper incarnation.

### Recovering a stream that lost two of its three voters

A stream commits and changes membership with two of its three voters, so it
stops when two are lost and leader-driven repair cannot help. An operator can
make the survivor's replica the stream's only history. This can lose
acknowledged records: a committed record reached two voters, which may have
been the two lost ones. Stop the surviving keeper, then run, on its host:

```sh
cargo run --locked --features stream -- keeper recover-stream --config keeper.json --stream STREAM_UUID --acknowledge-data-loss --lost KEEPER_UUID,KEEPER_UUID [--with KEEPER_UUID,KEEPER_UUID]
```

The command takes the keeper's media lock, so it refuses while the keeper
runs. It replays the whole local log, including entries the survivor never
saw committed, and asks every other keeper for its status.

- **Refusals.** It refuses when the survivor is not a voter of the stream's
  latest configuration, when that configuration is joint, and when any other
  voter of it answers with a healthy replica, open or parked: the stream
  still has a quorum, so restart the survivor instead. It also refuses the
  replicated catalog stream. Without `--acknowledge-data-loss` it prints what
  it would do and refuses.
- **Lost voters.** `--lost` must name the configuration's two other voters:
  it is the operator's statement that both are down or fenced, which no
  probe can prove. A lost voter that does not answer the first status request
  is asked twice more, for 5 s each, before it counts as lost, so a slow
  keeper is refused as a live one rather than recovered over.
- **Replacements.** `--with` names two keepers. Without it the command takes
  the two best-ranked live, accepting keepers outside the lost configuration,
  in failure domains distinct from each other and from the survivor's. They
  must answer.
- **Staging.** Each replacement stages an installed, empty copy of the
  stream. A replacement refuses when its own open replica votes in its
  configuration, which means the survivor's view is stale. The command then
  stages the move in the catalog and refuses if the catalog does not record
  it: the catalog's record is what fences the lost voters (see below), so a
  recovery needs the catalog. Clients also see the new voters first among the
  contacts. A refused replacement leaves the catalog untouched; a recovery
  that stops after the catalog recorded it leaves the old configuration
  fenced, so run it again to completion.
- **The durable step.** One WAL round on the survivor, `Record::Recover`,
  holds a vote for the survivor in a term 2^32 above every term it has seen
  and two entries in that term. `Command::Recover` stages the move and seals
  the stream under a reserved recovery writer at an epoch one above every
  epoch the survivor applied. The membership entry names the survivor and the
  two replacements. A crash before the round's boundary leaves no trace of it
  and the command can run again. A crash after it, or a second run, reports
  the recovery as already written.

Then start the survivor. Its replacements vote for it with their empty logs,
it becomes leader in the new membership and replicates its log to them, which
commits the recovery. The stream's head is the survivor's.

The recovery fence admits no append or trim. Every `seal` returns
`JournalError::Recovered { head }` until a writer or an administrator calls
`Journal::acknowledge_recovery(stream)` (also
`ConsensusJournal::acknowledge_recovery`), which returns the head and
replaces the fence with an ownerless one at the same epoch. Writers then seal
above it. The operator already accepted the possible loss with
`--acknowledge-data-loss`; the second call only records that the consumer
noticed, so a consumer may acknowledge on its own and resume, recording the
recovery durably and reporting it, rather than waiting for a person. A
consumer that sees `Recovered`, or a head below what it was acknowledged,
must treat it as data loss and rebuild from the journal instead of its own
previous head.

**Lost voters and placement certification.** Two lost voters are a quorum
of the configuration the recovery left, and a lost voter may still hold the
lost suffix, even from a snapshot it reopens. Raft cannot tell them from a
healthy pair, so every copy must be *certified* in the keeper process that
opened it before it campaigns (its network sends no vote or pre-vote) or
serves a read (`decisions::serves_reads`). A copy is certified by an append
from a leader whose vote does not lose to its own (that leader campaigned
certified), by a bootstrap that registers it empty, or by the catalog: the
keeper asks for the stream's latest staged move (`Request::Staging`), which
every replacement and every recovery records before it changes the stream.
`decisions::fences_copy` fences a copy whose effective configuration is
neither side of that move, joint or uniform, and for a recovery every
configuration but its target. A fenced copy retires on the highest placement
proof another keeper certifies. Certification is kept in memory per copy
generation and survives parking, so a stream's normal path makes no catalog
round trip: only a copy that opened without hearing a leader asks, after a
restart. A catalog outage therefore holds back only such copies: after a
whole-cluster restart, streams elect once the catalog answers. The
replicated catalog stream certifies itself.

So a returning lost voter, alone or with the other, never campaigns and
never serves the lost suffix; it asks the catalog, is fenced and retires,
even when the survivor has since been replaced and neither lost voter knows
any current voter. The recovered voters also refuse every frame from a peer
outside their membership whose vote is below theirs (appends, votes,
pre-votes, snapshot chunks, hand-offs and parks) without an answer, so a lost
voter never learns the recovered term. Independently, before a keeper first
votes in a stream after it starts, it asks every other keeper for the
configuration its own copy finalized (`Request::LocalConfiguration`), and
refuses the vote and retires when one finalized a newer revision that names
it nowhere; that check stays open while a keeper does not answer, which
certification does not. The TLA+ model in `verification/tla` checks
certification (`RecoveryBothReturn`, `RecoveryBothReturnLiveness`).

**Residual risk: lost voters that never stopped.** Certification fences
copies that reopen. A lost voter that kept running through the recovery,
partitioned from the survivor but in contact with the other lost voter, stays
certified: the pair keeps leading the old configuration until it touches a
recovered voter. Closing that needs leases bounded by the catalog, so that a
catalog outage would stop every stream after the lease; that cost is the
owner's call. Until then the runbook's rule stands: confirm on each host that
both lost keepers are down or fenced before recovering
(`docs/runbooks/lose-two-voters.md`).

**Why readers cannot mix histories.** The recovered entries and every later
entry carry terms above every term in the survivor's history and, with the
2^32 gap, in the lost voters' histories. Raft's log matching then makes any
log that holds a recovered entry agree with the survivor's log below it.
Only the survivor and the replacements vote in the recovered membership; a
replacement holds nothing but what the survivor sends it. A lost voter cannot
reach a quorum that includes a recovered voter, and its copy retires on a
placement proof certified by the recovered membership. So every committed
record a reader sees after the recovery comes from the survivor's log or was
appended after the recovery, never from the lost suffix. Writers before the
recovery are fenced by the recovery epoch, so none of their appends commits
after it.

### Keeper storage and upgrade

Admission leaves 88 MiB free for durable protocol control (32 MiB), maintenance
records (8 MiB), maintenance scratch (40 MiB), and bounded external allocations
and filesystem overhead (8 MiB). Ordinary entries reserve bytes and a pending
suffix slot together. A reserved WAL lane services exact snapshot selection and
covered purge alongside the independently admitted control lane. One snapshot
builder at a time reserves up to 36 MiB of scratch on the volume. If the 512-slot
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
at most 2,049 pages. A build rewrites only the pages that changed since the
previous snapshot, and the scratch budget covers a full set, since keeper
batches can change every page between two snapshots.

A WAL segment is deleted once no entry slice holds it, so one retained record
would keep its whole 64 MiB segment. The keeper counts each segment's live
bytes as slices are created and dropped, and prints the segments before the
published checkpoint in usage buckets every 5 s when they change. Every 10 s,
with up to 2 s of jitter, a compaction pass takes the sealed segments before
the checkpoint whose live slices hold under half their bytes and that nothing
else holds (a parked copy's pins, a quarantine), least live first. A stream
whose WAL suffix still holds entries there is first asked to snapshot and
purge, and gets 30 s. The remaining slices, held by snapshots and applied
images, are then copied to the active segment grouped by stream, at most
16 MiB a pass, as `Record::Relocate` frames on the maintenance lane, booked
against the maintenance floor and suspended unless ordinary writes keep room
for twice the batch. Once a copy's round is durable every holder reads it.
The old segment stays until a checkpoint captured after the copy is published
and, for a stream with a selected snapshot, until that stream selects a
snapshot rebuilt after the copy; that rebuild writes every index page again,
within the full-page-set scratch. `segments.compacted_bytes` counts the bytes
copied. A crash before the round's boundary leaves the old copy in use; after
it, replay ignores the frame and the old copy is read until the next
checkpoint, so the copy is at worst dead bytes for a later pass.

`Record::Relocate` is a WAL format addition, appended last to the record enum
like `Record::Recover`; checkpoints, segment headers and snapshot formats are
unchanged. A keeper built before it refuses to open a WAL whose frames after
the published checkpoint hold one (bincode reports an unknown variant), so
roll back only after a checkpoint has passed the last compaction, or with the
keeper's data replaced. Once the cluster feature level lands, relocation
should wait for it.
New appends enforce a 262,144 retained-record ceiling alongside the configured
retained-byte quota. A further append or batch past the ceiling returns
`Full` until a trim lowers the count. Consumers that checkpoint and trim on a
record count should do so at half the ceiling; RTDB checkpoints at 131,072
retained records. Selection becomes durable through one WAL boundary update
before purge. The cleanup worker considers at most 64 object names at a time
and up to 16 directory entries for one detached generation per pass. Actual
available filesystem space governs reuse, including allocations left behind
by interrupted work and unlinked files with open handles.

Each retained record costs a voter 64 bytes in the applied record index, and
the current local snapshot keeps its own 64-byte copy for the cut it serves.
Records of one batch entry share a single extent handle, also after restart.
A stream at the ceiling measured 137 bytes per record per voter after a full
restart, about 36 MB (16 MiB applied, 16 MiB snapshot, the rest handles and
index-page dependencies). Directly after the fill, before any restart, the
same stream measured about 265 bytes per record per voter, including
write-path state that a restart does not rebuild.

The existing bulk ALPN, 1 MiB chunks and `LKRIMG03` wire image remain supported.
Bulk admission is shared by incoming files and private seekable outbound files.
It allows four sessions, up to 256 MiB per file and 512 MiB in total, subject to
available volume space. A sender pins the selected cut and serves the same
bytes at every retry offset. A receiver drops an incomplete session after 30
seconds of inactivity. Size retained data for a wire image within that limit,
including framing and metadata, when replacement by snapshot is required.

The keeper can reopen a selected `LKRIMG03` image in place. A first local snapshot
can reference it as an immutable extent. New selected local roots use
`LKRIDX02`, which also stores the epoch each retained record was written
under, and new WAL directories use `LKRWAL03`. An `LKRIDX01` root, or an
`LKRIMG03` image installed from a peer, reopens with no record epochs, so
until those records are trimmed an append matching one is judged by its
bytes alone. A keeper before `LKRIDX02` cannot reopen such a root, so do
not downgrade below it. On first startup, an enrolled
framed WAL is migrated through the existing trusted boundary. Budget additional
free space for the encoded live suffix, two allocation units per entry, 160 KiB
plus two allocation units per scope, 1 MiB for the root and overhead, and the
88 MiB headroom. The old WAL stays selected until the new files and boundary
are durable. Before upgrading, prune any former data exceeding the new suffix
or retained-record geometry through supported caller-authorized operations.
Keepers before the 262,144-record ceiling refuse snapshots of streams holding
more than 65,536 records, so upgrade every voter before a stream grows past
that.
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
at most 64 entries, matching `max_payload_entries`. An `Admitted` wrapper
decodes only one unwrapped application or staging command.

Admission counts peer messages, not connections or batch frames. The
receiver reads the 4-byte length of a replication batch frame and charges it
before allocating the body, waiting while the sender or the receiver is full;
the wait stalls only that sender's connection. Once the frame is decoded, its
charge is exchanged under one lock for one charge per message, and a message
past the budgets is answered `Busy`. Each in-flight message is charged at
four times its encoded size plus 64 KiB to cover decoding and handoff copies.
The receiver allows 256 MiB and 384 messages in total, with at most 96 MiB
and 128 messages per authenticated sender across all of its connections and
streams, which leaves 256 message slots for other senders. Control work is
capped at 384 messages in total and 128 per sender, leaving 256 for other
senders; a control message over its sender's share waits up to 100 ms for a
slot and is then refused. Verus checks these decisions and that releasing a
message restores both meters exactly. At most 64 idle control connections
wait for a header, and the oldest is closed first; a connection with
messages in flight is not idle.

Before dispatch into Raft storage, a follower reserves the batch's upper
bound from the shared disk owner. That bound is the encoded entries plus
768 KiB of WAL metadata and 16 KiB per entry plus one more. Follower appends
use the ordinary physical pool and leave the 88 MiB control and maintenance
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
skipped. A round takes at most 128 records and stops after crossing 32 MiB.
Each stream admits one follower batch at a time, so the follower queue holds
at most one batch per stream, at most 16 in total, in FIFO order. A stream
therefore cannot overtake itself, and a ready stream waits behind at most 15
other streams. One sender's 128 messages can fill all of those slots and
wait behind them; the bound still holds. This rotation over streams gives the checked `5 * W` service
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
bincode, and the control and replication lanes carry multiplexed batch
frames.

**Rolling upgrades (N and N-1).** Each lane has an ALPN for this release (N)
and keeps the previous release's (N-1): application
`logkeeper-consensus/2` and `/1`, control `logkeeper-consensus-control/9` and
`/8`, replication `logkeeper-consensus-replication/4` and `/3`, bulk
`logkeeper-consensus-bulk/3` and `/2`. Every listener accepts both, and
clients and peers offer N then N-1. On an N-1 connection a keeper speaks the
N-1 codec: its liveness ping is the N-1 `Liveness` frame, its replies and
`KeeperStatus` take their N-1 layout, and it maps errors N-1 does not know
(`Unsupported`, `Corrupted`) to `Unavailable`; requests N-1 does not know are
refused locally. Those degrade safely against an N-1 keeper: the
returning-voter check (`LocalConfiguration`) counts it as not answering and
asks again, and a copy that must certify itself through an N-1 catalog
(`Staging`) stays uncertified, so it neither campaigns nor serves reads
until a leader's append certifies it. So upgrade the catalog keeper, or the
catalog voters, first. On an N connection, pings and `KeeperStatus` also carry the
keeper's `build_version`, `features` bits and finalized `cluster_version`, and
an unknown request or frame gets a typed `Unsupported` without closing the
connection. A keeper two releases apart fails the TLS handshake with
`no_application_protocol`; it counts as alive, accepts no new streams and is
never repaired, so a version mismatch never triggers repair. Only adjacent
releases mix: upgrade from N-1 to N, one keeper at a time
(`docs/runbooks/rolling-upgrade.md`). The compatibility tests run real
binaries of the N-1 commit against this one.

**Write-version gate.** The catalog holds a finalized cluster feature level,
1 until an administrator finalizes. `Client::finalize_version(2)` probes
every keeper in the inventory and refuses with `Unsupported` while one lacks
the gate, or `Unavailable`, worth retrying, while one does not answer. Until
then N writes only N-1 formats, so a keeper can go back to N-1: checkpoints
stay `LKRWAL04`, no cluster-version record is written, segment compaction
only asks owners to snapshot and purge instead of writing `Relocate` frames,
and a parked copy writes no park mark, so it reopens at restart. After it,
checkpoints become `LKRWAL05`, compaction copies cold slices, parks are
durable, and N-1 refuses the media. A format a later release adds follows
the same rule: it is written only once `write_version_allows` it, and a
request it adds is refused on N-1 connections in `Request::supported_on`. Keeper configuration ignores
an unknown top-level field with a warning, so a configuration may name a
newer release's setting first; nested settings and `JournalConfig` stay
strict.

**Placement changes and retired keepers.** The rule of three active keepers
in distinct failure domains applies only where a roster is chosen: a new
genesis, a stage's target and a recovery's replacements. Replay, snapshots,
ingress and proofs only check that the voters are three sorted keepers the
inventory knows, so a domain reassignment or a retirement never quarantines
a replica. Leaders count a configuration that breaks placement
(`placement.violation`), and repair moves it, waking it if it is parked.
`retired` keepers in `placement.json`, `Config`, `JournalConfig` and
`Client::with_retired` take no new streams; a draining one, still in
`keepers`, still serves and is still asked before a recovery or a
finalization.

The `LKRIMG03` images and the WAL records are unchanged before
finalization; a test pins the persisted bytes of
votes, log ids, memberships, entries and snapshot metadata to their 0.9
encoding. A leader that cannot confirm a recent quorum refuses writes
and answers that it has no leader; after 1.8 seconds without a quorum it
gives way to a new leader. Followers run a pre-vote round before raising
their term, so a keeper that rejoins after a partition does not depose a
working leader. A graceful shutdown first transfers every stream the keeper
leads to a caught-up voter, waiting at most 3 seconds, so a rolling restart
does not wait out a lease and an election per stream.

Placement certification adds `Request::Staging` to the end of the
application protocol, whose ALPN stays `logkeeper-consensus/1` so clients
need no upgrade. A catalog keeper, or replicated catalog voter, older than
this build refuses the request, and a restarted copy that cannot certify
does not campaign: upgrade the catalog keepers first.

Verus checks the shipped admission, metering, classification, rotation, batch,
restart, recovery, repair, keeper incarnation and upgrade-gate decisions in
`src/stream/consensus/decisions.rs` against laws named after the Lean
theorems. The baseline verifies 133 functions, and 68 production mutations
each fail their declared contract. See
`verification/verus/consensus_admission/README.md` for the mapping and the
unverified stateful glue.

Local Rust tests cover these acceptance cuts:

- A mixed batch sent on the control lane is refused. With disk space
  exhausted, the same batch on the replication lane gets `Busy` with no
  outstanding charge and an unchanged log.
- One sender is held at its share and the receiver at its byte budget, and
  their next frames wait unread, while another sender still enters. A vote and a fresh `head` are served, and a
  covered snapshot and purge commit, all while replication data is saturated.
  Payload resumes after release, and the stopped original voter catches up
  with unchanged membership once the pressure clears.
- With a refusing target, continuous fresh `head` load, a stream busy with
  2 MiB appends and 210 idle authenticated control connections, ten appends
  to an unrelated stream each commit within five seconds. The busy stream
  keeps committing. The refusing target holds no charge, stays at its prefix
  and catches up after its space returns.
- Unit tests cover the per-sender and receiver byte and message caps, a
  batch read that waits for its sender and splits into exact message charges,
  exact release, control work caps and oldest-first eviction of idle control
  waits. The sender splits oversized valid batches.
- On one multiplexed connection, 128 concurrent messages travel in one frame
  and each caller gets its own reply; a slow reply holds back no other, a
  late one is dropped, and a failure answers only its own message. A dropped
  connection fails its waiters and the next call reconnects. Heartbeats for
  16 streams reach a keeper in one frame, where parked streams answer
  `Busy`, a repeated park is accepted, a deleted stream fails alone and the
  connection keeps serving.
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
keeper inventory, the catalog keeper and, with a replicated catalog, its
`catalog_voters`, the three voters and the quota for each stream it creates, the record limit and the operation deadline. Every
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

Every keeper pings every other keeper on the multiplexed control channel
every 2 seconds and keeps when each last answered, with the keeper-wide
status it reported. A keeper unreachable for `repair_after_secs` is dead.
A ping carries the sender's media incarnation, and its answer carries the
receiver's and the one the receiver first saw the sender under. Until one
peer has answered, a keeper registers no stream it does not hold: peer
traffic for such a stream is refused and retried, and a bootstrap pings at
once.

Each stream's leader repairs its own stream. A voter that has not
acknowledged the leader for `repair_after_secs` (600 by default), or whose
keeper is dead, and whose keeper does not answer pings or answers without a
healthy replica, is replaced by the best-ranked live keeper with room in a
free failure domain, through the same staged joint change as `replace`.
Nothing moves unless two voters are live. Every 30 seconds a keeper queues
the repair work of all streams it leads, in priority order: finish a joint
change, remove stale learners, then replace dead or quarantined voters. Up
to four repairs run at once, streams take turns, and a stream whose repair
fails waits a backoff that doubles from 30 seconds up to 10 minutes, so one
stuck stream does not hold up the others. Health comes from the ping table
rather than a status call per stream. A stream
that lost two voters has no quorum to change its membership and needs an
operator. A replica that hears from no leader for the repair delay asks
other keepers for the stream's current placement; when that placement no
longer names it, the keeper retires its copy, so a voter replaced while it
was down, or moved off by a drain, frees its slot and disk when it returns. A
learner that a timed-out replacement left in the membership would keep
receiving the stream's replication; the leader removes a learner it has
seen for 60 seconds while no replacement holds the stream.

A stream that served no client and appended nothing for `park_after_secs`
(600 by default) is parked: its leader asks each follower holding exactly
its applied log to close the group, then closes its own. A parked stream
runs no timers and sends no heartbeats. A parked follower answers an empty
heartbeat as busy without opening the group; entries, votes, snapshots and
client requests reopen it. The voter that led the stream campaigns as soon as
it reopens and its followers grant it at once, so the first request after
parking waits for one vote round instead of an election timeout (about 35 ms
on loopback); when that voter's keeper is unreachable, the first reachable
voter campaigns when the old leader's lease ends. A leader parks a stream
without a follower whose keeper is dead, so a zone outage does not keep every
stream awake. A parked stream has no leader to repair it: every keeper
reopens, at most eight per sweep and with a doubling backoff, its parked or
unopened copies of streams whose configuration names a dead keeper, and
their leaders repair them. Parked streams whose voters all live stay parked.
On one host, 128 idle streams used 0.09 CPU cores parked
against 0.47 unparked.

A parked copy keeps no state machine. Once its group has stopped, it keeps
pins of the segments its selected snapshot and applied records lie in, a
hold on its standalone objects (index pages and entries from before
segments), and its configuration; the WAL suffix pins itself. A full stream
of 262,144 records parked in about 3 MiB of heap per voter instead of about
33 MiB. The pins are also written as a park mark, `parked` in the copy's
directory, naming the selected snapshot they were taken for. A restarted
keeper keeps a copy whose mark matches its selected snapshot parked, without
loading its image, until traffic reopens it; a mismatched or damaged mark is
ignored and the copy opens. Opening a copy removes its mark.

At `max_streams`, opening another stream closes the least recently used copy
that served no client, grew no log and ran no repair for 30 s (or
`park_after_secs`, if shorter), instead of refusing. Copies the keeper
follows go first; one it leads first hands its leadership to a matched
follower. An evicted copy is parked with a mark and refuses empty heartbeats
until entries, a vote, a snapshot or a client reopen it. `stream.evicted`
counts evictions.

On the control and replication lanes a keeper keeps one long-lived
connection to each other keeper, opened on first use and again after it
fails. Every message carries a request id. A writer task sends the messages
queued for that keeper in one batch frame, up to 256 messages, the lane's
frame limit or 1 ms of collecting, and never waits on an empty queue; the
empty heartbeats of many streams that fall due together therefore share a
frame. A reader task hands each reply to its caller by id. The receiver
admits each message on its own, runs the messages of one connection
concurrently within the sender's share, answers each under its id and
batches replies that finish together. A message refused for its stream, for
example a deleted one, fails alone; a message on the wrong lane or under
another keeper's name closes the connection. A sender keeps at most the
receiver's per-sender share in flight to each keeper, 128 messages per lane,
and queues the rest. Each caller times out on its own and a late reply is
dropped. A broken connection fails the messages it had sent, which Raft
retries after its usual backoff, and hands unsent ones to a fresh
connection. Snapshot chunks on the bulk lane still use one request per
pooled connection, at most sixteen in flight to each keeper.

A keeper paces the bytes it sends in snapshot transfers, across all its
streams, to `snapshot_send_bytes_per_second` (64 MiB/s by default; zero
disables pacing), so catch-up and repair do not saturate a cross-zone link.
A `JournalConfig` with a `placement` may name the consumer's own `domain`;
reads then go first to a voter in that domain, then to the keeper that
answered last. After each seal such a journal also asks the stream's leader to hand
leadership to the voter in its domain, which saves a cross-zone round trip
per append; a leader does so only when that voter has matched its log and
no hand-off reached or left it in the last minute. The leader records the
preferred domain and forwards it to the other voters, which keep it in
memory, and every 30 seconds each leader moves a stream back to the voter in
its preferred domain under the same rules, provided that voter's keeper
accepts streams. Leadership therefore returns to the writer's domain after a
park, a restart, a graceful hand-off, shedding from a full keeper or an
election, without a new seal. A full restart of every voter forgets the
preference until the writer's next seal.

A keeper whose media is unhealthy or full hands every stream it leads to a
follower that has matched its log and whose keeper accepts streams, since
it cannot write even when its followers have room.

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
for named principals and can stop and restart individual keepers.
`LocalCluster::start_replicated_catalog` hosts a replicated catalog on two
voters and the catalog keeper instead. The contract conformance suite and a
full-restart test run against both.

```sh
cargo test --locked --features consensus-testing --test consensus_journal_conformance
```

#### Randomized consensus fault-injection and linearizability harness

`src/stream/consensus/simulation/` runs real in-process consensus keepers over
the `Network`/`Rpc` seam with seeded fault injection (symmetric and asymmetric
per-lane partitions across control, replication, bulk and application lanes;
message drops, delays, reply drops and peer duplicates; graceful stops, abrupt
crashes and WAL before/after-sync crash cuts; slow disks and disk-full
shedding; parking/waking, membership replacement, leader preference, replicated
catalog outages, offline `recover-stream` + `acknowledge_recovery`, and
wipe-and-reinitialize). Every run checks per-stream linearizability with
`journal_contract::conformance::history::linearizable`, durability, monotonic
heads, writer fencing, ambiguous `append_batch` atomicity, delete permanence
and post-run cross-voter convergence.

```sh
# Default run, part of the normal suite: 6 seeds across all non-wipe profiles,
# the large-batch test, 2 wipe-and-reinitialize seeds, the 6d75fec amnesia
# schedule with reused-ID recognition off and on, and the bug reproductions
cargo test --locked --features stream --lib stream::consensus::simulation -- --nocapture

# Replay a specific failing seed (optionally with wipe-and-reinitialize and automatic shrinking)
LOGKEEPER_CONSENSUS_SEED=1 LOGKEEPER_CONSENSUS_ALLOW_WIPE=1 LOGKEEPER_CONSENSUS_SHRINK=1 \
  cargo test --locked --features stream --lib consensus_fault_harness_replay_seed -- --ignored --nocapture

# Extended randomized soak run (default 50 seeds; override with LOGKEEPER_CONSENSUS_FIRST_SEED / LOGKEEPER_CONSENSUS_SEEDS)
LOGKEEPER_CONSENSUS_SEEDS=50 \
  cargo test --locked --features stream --lib consensus_fault_harness_soak -- --ignored --nocapture

# Search wipe seeds for Raft amnesia with reused-ID recognition turned off
cargo test --locked --features stream --lib consensus_fault_harness_detects_amnesia_bug -- --ignored --nocapture
```

`LOGKEEPER_CONSENSUS_ALLOW_WIPE=1` adds wipe-and-reinitialize steps to replay
and soak runs. `LOGKEEPER_CONSENSUS_IGNORE_REUSE=1` makes the keepers accept a
keeper ID reused on new media, as they did before media incarnations, so a
run shows the harness still finds that bug.

See [verification/simulation/README.md](verification/simulation/README.md#consensus-keeper-fault-injection-harness)
for the fault model and checked invariants.

### Operations

The admin listener exposes metrics, probes, status, and operator mode changes.
`logkeeper admin` runs administrative requests. The debug bundle collects
diagnostics from the admin listener and the offline inspection tools.
Alert rules and a dashboard live in
`deploy/prometheus/logkeeper-alerts.yml` and `deploy/grafana/logkeeper.json`.

#### Admin listener

Enable a separate HTTP/1.1 admin listener with `admin` in the keeper
configuration:

```json
  "admin": {
    "listen": "127.0.0.1:9100",
    "mtls": false,
    "cluster": {
      "<keeper uuid>": "10.0.1.12:9100",
      "<keeper uuid>": "10.0.2.12:9100"
    }
  }
```

- `listen` defaults to `127.0.0.1:9100`. It must differ from the keeper's
  client, peer and bulk listeners.
- Plain HTTP (`"mtls": false`, the default) may only bind a loopback address.
  To scrape from another host, set `"mtls": true`: the listener then serves TLS
  1.3 with the keeper's credentials and requires a client certificate signed by
  the cluster CA. It serves administrators and cluster keepers, and gives
  principals in `admin.metrics_readers` access to `/metrics`, `/live`, and
  `/ready`.
- `admin.probe_listen` optionally serves `/live` and `/ready` over plain HTTP
  on a separate loopback address. A Kubernetes exec probe can call it from
  inside the pod.
- `cluster` names the admin listeners of the other keepers. Only
  `logkeeper keeper debug-bundle` reads it.
- The listener serves at most 16 connections at once and sheds the next one
  immediately. One 5 s deadline covers each connection's TLS handshake,
  request and response; request headers are limited to 8 KiB and a request
  body is never read. A failing or panicking request never stops the keeper.
- Endpoints: `GET` or `HEAD` `/metrics`, `/live`, `/ready`, `/safe-to-stop`,
  `/problems` (alias `/problem-streams`), `/status` and `/drain`; `POST`
  `/drain`, `/undrain` and `/decommission` set the operator mode (below) and
  answer the `/drain` report. Only an administrator (or anyone on a plain
  loopback listener) may `POST`; other keepers get `403`. Anything else
  answers `404`; other methods `405`.

#### Operator mode: drain

A keeper is `serving`, `draining` or `decommissioning`. The mode is a file,
`operator-mode.json`, in its data directory, written and synced before it
takes effect, so it survives restarts until the operator clears it. A
draining keeper:

- hands every stream it leads to a voter that matched its log and whose
  keeper accepts streams, retrying every second;
- starts no election of its own (OpenRaft's election timer is off, and it
  does not campaign after waking a parked stream); it still votes, so the
  other voters elect without it;
- reports `accepting: false`, so placement and repair choose other keepers,
  and no leader hands it a stream, even one its writer prefers.

Do not drain all three voters of a stream at once: none of them would
campaign. `GET /drain` reports `mode`, `led`, `hosted`, `voter_streams` and
`drained` (draining and leading nothing). A decommissioning keeper also moves
its replicas through quorum repair. Wait for `safe_to_delete` before stopping
it for permanent removal.

On Unix, SIGHUP reloads authorized TLS credentials for new connections.
See the [certificate rotation runbook](docs/runbooks/certificate-rotation.md).

#### Admin CLI

`logkeeper admin COMMAND --config operator.json [--json]` runs one
administrative request. The file (see `deploy/consensus/operator.example.json`)
holds a client certificate whose URI is in the keepers' `administrators`, the
keepers' application addresses, the catalog and its voters, and, for the
commands that read them, every keeper's admin listener (`admin`, with
`admin_mtls`, default `true`). Over mTLS each admin listener must present the
certificate of the keeper it is listed under. Output is `key: value` lines, or
JSON with `--json`; the exit status is non-zero when a command fails or a
report is incomplete.

| Command | What it does |
| --- | --- |
| `create --stream UUID --quota-bytes N [--voters A,B,C]` | Creates the stream on the voters, or on three keepers of the file's `placement` in distinct domains. Safe to retry with the same arguments |
| `status --stream UUID` | Configuration, leader, head, each voter's replica (`healthy`, `quarantined`, `none`, `unknown`) and the voters' `/problems` entries for it |
| `status --keeper UUID` | That keeper's `/status` |
| `replace --stream UUID --old K --new K` | Replaces one voter of the current configuration; `--expected REV --voters A,B,C` names the whole target |
| `prefer-leader --stream UUID --keeper K` | Asks the leader to hand leadership to `K` (subject to the 60 s hold-down) |
| `acknowledge-recovery --stream UUID` | Clears an operator recovery's fence and prints the head |
| `retire --stream UUID --keeper K` | Retires `K`'s copy of a stream whose configuration no longer names it, certified by the leader |
| `problems` | Every keeper's `/problems`, merged by stream, and which keepers did not answer |
| `drain --keeper K [--wait-secs N]` | Marks `K` draining and waits (120 s by default) until it leads nothing; non-zero exit if it still leads some |
| `undrain --keeper K` | Clears the mark: `K` elects, leads and takes placements again |
| `decommission --keeper K [--wait-secs N]` | Moves leadership and replicas off `K` and waits until it is safe to delete |
| `drain-status --keeper K` | `K`'s mode, the streams it leads and hosts, and those it votes in |
| `clear-quarantine --keeper K --stream UUID` | Clears the replica's quarantine marker after repair |
| `finalize-version` | Enables the new write format after the rolling upgrade |

Administrators may now also send `PreferLeader`, which used to be a writer's
request; it moves leadership and writes nothing.

#### Metrics

`GET /metrics` serves the Prometheus text format (`0.0.4`). A scrape computes
its gauges from the keeper's state at that moment; nothing runs between
scrapes, so an unscraped keeper pays nothing. Labels are bounded: `keeper`,
`follower` and `domain` take one value per keeper in the inventory, the other
labels a fixed set. Each keeper reports every keeper's liveness, so the
liveness families grow with the square of the cluster size.

| Family | Meaning |
| --- | --- |
| `logkeeper_build_info{version,keeper,domain,control_alpn,replication_alpn,bulk_alpn}` | Build and wire versions, always 1 |
| `logkeeper_consensus_wal_healthy`, `_media_responsive`, `_accepting` | WAL thread running; no WAL round past the slow-round gate recently; keeper accepts new streams (what it reports to placement) |
| `logkeeper_consensus_operator_mode{mode="serving\|draining\|decommissioning"}` | 1 for the operator mode the keeper is in |
| `logkeeper_consensus_streams{state="hosted\|open\|led\|parked\|quarantined\|deleted"}` | Replica counts |
| `logkeeper_consensus_problem_streams{reason}` | Hosted streams per `/problems` reason, every reason exported, zero included |
| `logkeeper_consensus_refusals_total{reason}` | Requests refused `Unavailable`, by reason (`write.*`, `head.*`, `peer.*`) |
| `logkeeper_consensus_commit_duration_seconds` | Leader write latency, admission to Raft decision |
| `logkeeper_consensus_commit_stage_seconds{stage="queue\|wal\|replication\|apply"}` | The same latency by stage: WAL queue wait, the durable WAL round, the leader's durable append to the start of its apply (follower appends, quorum commit, apply queue), and one apply batch |
| `logkeeper_consensus_slow_proposals`, `_oldest_proposal_seconds`, `_slow_proposals_total` | Proposals in flight for at least 1 s, the oldest one's age, and proposals that took that long to commit or fail |
| `logkeeper_consensus_wal_round_records`, `_wal_round_bytes`, `_wal_round_duration_seconds` | Per WAL round: records, bytes, duration |
| `logkeeper_consensus_wal_fsync_duration_seconds{target="segment\|boundary"}` | fdatasync latency |
| `logkeeper_consensus_wal_slow_round_seconds`, `_wal_round_limit_seconds` | The 2.5 s slow-round gate (the keeper hands off leadership and refuses votes) and the 20 s watchdog limit (the keeper exits) |
| `logkeeper_consensus_disk_available_bytes`, `_disk_reserved_bytes`, `_disk_ordinary_floor_bytes` | Volume free space, bytes reserved for writes in flight, and the floor below which ordinary writes are refused |
| `logkeeper_consensus_replication_lag_entries_max{follower}`, `_total{follower}`, `_streams{follower}` | Raft entries each follower lags behind across the streams this keeper leads |
| `logkeeper_consensus_elections_total{outcome="started\|won"}`, `logkeeper_consensus_votes_total{kind,outcome}` | Elections and the votes and pre-votes this keeper answered |
| `logkeeper_consensus_snapshots_sent_total{outcome}`, `_snapshots_received_total{outcome}`, `_snapshot_bytes_sent_total`, `_snapshot_bytes_received_total`, `_snapshots_built_total` | Snapshot transfers |
| `logkeeper_consensus_repairs_total{kind="joint\|learners\|voter",outcome}`, `_repairs_in_flight` | Automatic repairs |
| `logkeeper_consensus_repair_pending_streams`, `_repair_oldest_pending_seconds`, `_repair_backoff_streams` | Led streams that need a repair, how long the oldest has waited, and streams backing off after a failed repair |
| `logkeeper_consensus_stream_parks_total`, `_stream_park_declined_total`, `_stream_wakes_total{trigger="peer\|client\|repair"}` | Parking |
| `logkeeper_consensus_keeper_liveness{keeper,domain,state="alive\|suspect\|dead"}`, `_keeper_accepting{keeper,domain}`, `_keeper_silent_seconds{keeper,domain}` | This keeper's view of every keeper |
| `logkeeper_consensus_retained_records_total`, `_max`, `_retained_bytes_total`, `_max`, `_wal_suffix_entries_max` | Retention summed and at the largest stream |
| `logkeeper_consensus_critical_total` | Critical invariant violations (see below) |

#### Probes

- `GET /live`: `200` while the WAL thread runs and the keeper is not stopping,
  else `503`.
- `GET /ready`: `200` once startup replay finished, the liveness table has
  heard from a peer, no hosted replica is quarantined, and every hosted replica
  is parked or caught up with a leader that matched it within two election
  timeouts. A leader that no quorum acknowledged within the silence limit
  counts as `leader_without_quorum`: OpenRaft 0.10.1 keeps an isolated leader
  in the `Leader` state until its quorum-loss probe, long after its lease
  expired. `503` lists each unmatched stream and why.
- `GET /safe-to-stop`: `200` when the liveness table is populated and no
  hosted stream has another voter unreachable or silent, or a joint
  configuration in flight. `503` lists each blocking `(stream, voter, reason)`.
  Gate rolling restarts on it: stop one keeper at a time, and wait for the
  restarted keeper's `/ready` before checking the next one.
- `GET /status`: the `KeeperStatus` the keeper reports to its peers, its
  version and ALPNs, WAL and media health, and its settings with the private
  key path redacted.

#### Problem-streams report

`GET /problems` lists every hosted stream with an anomaly, each tagged with
one or more reasons:

- `leaderless`: open, with no leader or a leader no quorum acknowledges.
- `under_replicated`: a voter is unreachable, silent, or 64 or more entries
  behind its leader.
- `parked_with_dead_voter`: parked while its configuration names a dead voter.
- `joint_config`: in a joint membership configuration.
- `near_suffix_ceiling`: unpurged WAL suffix at 75% or more of its 512 entries.
- `near_record_ceiling`: retained records at 75% or more of 262,144.
- `near_quota_ceiling`: retained bytes at 75% or more of its byte quota.
- `led_outside_preferred_domain`: led outside its writer's preferred domain.
- `quarantined`: the local replica is quarantined.

#### Logs, audit records and critical violations

The keeper logs structured `tracing` events to stderr, with `keeper` and
`stream` fields. A repeated warning is logged at most every 5 s per key and
stream; the next one carries the `dropped` count. Human-readable lines are the
default; select JSON lines with `"log_format": "json"`, `--log-format json` or
`LOGKEEPER_LOG_FORMAT=json`. `LOGKEEPER_LOG` or `RUST_LOG` set the level
(default `info` for `logkeeper`, `warn` for other crates such as `openraft`).
A message never spans lines: newlines in it are escaped.

Administrative actions (`replace`, `prefer_leader`, `acknowledge_recovery`,
`retire`, `operator_mode`, the repair loop's own replacements and retirements, and offline
`recovery`) log an audit record under target `logkeeper::audit` with
`audit=true`, `action`, `actor`, `keeper`, `stream` and `outcome`.

A state only a keeper bug can reach (a committed catalog record that does not
decode, a panicking WAL checkpoint writer or admin request) goes through
`critical!`: tests panic on it, while production logs it at `error` under
target `logkeeper::critical`, counts it in
`logkeeper_consensus_critical_total`, and carries on with its own recovery.

#### Offline inspection and verification

These read-only commands need a **stopped** keeper: they take the exclusive
`LOCK` of its data directory and refuse to run beside a live keeper. They
create, truncate and migrate nothing.

```sh
# Per stream: vote, membership, log range, applied and snapshot index, fence,
# head, retained records and bytes, ownership, and quarantine. Parking is not
# persisted, so a stopped keeper reports no stream parked.
logkeeper keeper inspect --config keeper.json [--stream UUID] [--json]

# Both boundary slots, the checkpoint digest and references, every WAL
# segment header and frame CRC, and the running SHA-256 chain against the
# checkpoint and the trusted boundary. Exits non-zero when verification fails.
logkeeper keeper verify --config keeper.json [--json]

# The frames of one WAL segment, by keeper and segment ID or by file.
logkeeper keeper dump-segment --config keeper.json --segment 1 [--limit N] [--json]
logkeeper keeper dump-segment --file ./keeper-1/raft-segments/00000000000000000001.seg [--limit N] [--json]
```

#### Debug bundle

```sh
logkeeper keeper debug-bundle --config keeper.json [--admin ADDR]... [--data DIR] [--out FILE]
```

writes one tar archive (`logkeeper-debug-<keeper>-<unix time>.tar` by
default) holding:

- `config.json`: the configuration file with every key, secret, password,
  token and credential value replaced by `<redacted>`;
- `keepers/<keeper>/{metrics.txt,problems.json,status.json,ready.json,safe-to-stop.json,live.json}`
  from this keeper's admin listener, every listener in `admin.cluster`, and
  each `--admin ADDR`, over mTLS with the keeper's own certificate when
  `admin.mtls` is set;
- `offline/inspect.json` and `offline/verify.json` when `--data` names a
  stopped keeper's data directory;
- `manifest.json`: which endpoints answered each path, and the error of each
  one that did not. An unreachable keeper does not fail the bundle.

#### Alerts and dashboard

Scrape each keeper's admin listener as `job="logkeeper"` and load
`deploy/prometheus/logkeeper-alerts.yml`. A test renders `/metrics` and fails
when the rules or the dashboard name a series the keeper does not export. The
rules read the keeper's own gates rather than copying them:

| Alert | Severity | Fires when | First response |
| --- | --- | --- | --- |
| `LogkeeperKeeperDown` | critical | a scrape target is down for 2 m | check the process and its admin listener |
| `LogkeeperKeeperDead` | critical | peers have not heard from a keeper for the repair delay | leaders replace it; restore or retire the host |
| `LogkeeperWalUnhealthy` | critical | the WAL thread stopped | restart the keeper; run `verify` if it will not start |
| `LogkeeperMediaSlow` | warning | a WAL round passed 2.5 s within the last 10 s, for 1 m | the keeper already handed off its leadership; check the disk |
| `LogkeeperNotAccepting` | warning | a serving (not drained) keeper accepts no new streams for 10 m | slow media, a stopped WAL, or a full volume |
| `LogkeeperCriticalInvariant` | critical | `critical!` fired | collect a debug bundle and the `logkeeper::critical` lines |
| `LogkeeperFsyncSlow` | warning | fsync p99 above 40% of the slow-round gate for 10 m | check the disk and its neighbours |
| `LogkeeperWalRoundNearSlowGate` | warning | WAL round p99 above half the slow-round gate for 10 m | as above |
| `LogkeeperWalRoundNearWatchdog` | critical | WAL round p99 above a quarter of the 20 s watchdog for 2 m | move load off the keeper before the watchdog ends it |
| `LogkeeperDiskHeadroomLow` / `Critical` | warning / critical | free bytes above reservations under 4× / 1.5× the ordinary floor | trim streams or grow the volume |
| `LogkeeperDiskFillingUp` | warning | the 6 h trend reaches the floor within a day | as above |
| `LogkeeperStreamLeaderless` | critical | a hosted stream has had no leader for 1 m | `/problems`, then the voters' liveness |
| `LogkeeperStreamUnderReplicated` | warning | for 5 m | repair replaces a voter silent for the repair delay |
| `LogkeeperParkedStreamDeadVoter` | warning | for 10 m | the wake sweep should reopen it for repair; check `/problems` |
| `LogkeeperQuarantinedReplica` | critical | a replica is quarantined | its leader repairs it; `verify` the stopped keeper |
| `LogkeeperJointConfigStuck` | warning | a joint configuration lasts 15 m | check the target voters' liveness |
| `LogkeeperStreamNearRecordCeiling` / `NearSuffixCeiling` / `NearQuota` | warning | a stream passes 75% of a ceiling | the writer should trim; for the suffix, check snapshots |
| `LogkeeperRepairQueueStuck` | warning | a repair waited over 15 m | `logkeeper_consensus_repair_backoff_streams` and the repair log lines |
| `LogkeeperSlowProposals` | warning | proposals stay in flight over 1 s for 5 m | `logkeeper_consensus_commit_stage_seconds` names the stage |

`deploy/grafana/logkeeper.json` (data source and keeper variables) charts the
same families in four rows: overview, writes and commit stages, WAL and disk,
and replication and repair.

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
