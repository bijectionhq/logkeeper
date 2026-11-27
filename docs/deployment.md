# Deploying the consensus keeper

This guide is for operators who run Logkeeper's consensus keeper in production,
mainly as the journal of RTDB Multi. The [README](../README.md) documents the
APIs. This guide covers hosts, disks, identities, bring-up and day-two
operations. The [runbooks](runbooks/) hold the step-by-step procedures.

The procedures use the consensus keeper's admin endpoints, offline inspection
tools, and N/N−1 compatibility. [Missing features](#missing-features) lists
the operations that still require other tooling.

Packaging lives in [`deploy/consensus/`](../deploy/consensus/):

| File | What it is |
| --- | --- |
| `Dockerfile` | Multi-stage image, non-root (uid 10001), media and registry volumes, healthcheck on `/live` |
| `release.py` | Build and verify a commit-pinned OCI image archive for Linux amd64 and arm64 |
| `logkeeper-consensus.service` | Hardened systemd unit with a 30 s stop timeout |
| `kubernetes/` | Kustomize bundle for six single-keeper StatefulSets across three zones |
| `keeper.example.json`, `placement.example.json`, `provision.example.json` | One keeper's config and its registry authority files |
| `rtdb-journal.example.json` | The RTDB side: a Logkeeper `JournalConfig` |
| `operator.example.json` | What `logkeeper admin` reads: the operator's credentials and every keeper's application and admin address |
| `tests/validate.sh` | Renders and validates the manifests |

`cargo test --features stream --test deploy_examples` checks that the example
configs parse the way the keeper and the client read them, and that they agree
with each other.

## Release candidate and qualification

Run the **Consensus qualification** workflow manually on the commit under
review. It requires the normal CI suite, the fixed fault-injection window in
both profiles, the full TLC checks, the Lean consensus and correspondence
checks, and the selected Verus production proofs and controls. The scheduled
run rotates the fault seed window each week. The reports retain the commit,
seed ranges and failures. The manual run emits an OCI candidate artifact only
after the checks pass. The artifact contains `release.json`, the image archive
and their transport checksums in `SHA256SUMS`. Keep the qualification reports
with the candidate and the previously qualified digest for rollback.

For a local build, create a Docker Buildx `docker-container` builder with
[this workflow's BuildKit image](../.github/workflows/consensus-qualification.yml).
The builder needs both Linux platforms for the standard bundle. Use a new
output path for each attempt.

```sh
python3 deploy/consensus/release.py --ref HEAD --builder logkeeper-release --output candidate
(cd candidate && shasum -a 256 -c SHA256SUMS)
```

The build takes source files from the specified Git commit and uses the locked
Cargo dependencies, pinned base images, dated Debian package archives, and
commit timestamps. Refresh the base digests and Debian snapshot together when
qualifying updated dependencies. The release record lists the OCI image index
digest and each platform manifest digest. Compare the OCI digests across
independent builds using the same builder image and platform set. Verify the
registry's digest after an authorized staging import, and pin that digest in
the staging configuration. Distribute the archive and qualification evidence
through trusted release storage and use `SHA256SUMS` to check transport.

## What a keeper is

A keeper is one process, `logkeeper keeper --config FILE`, built with the
`stream` feature. It hosts one Raft group per stream (OpenRaft 0.10.1) on a
shared segmented WAL. It listens on three TCP ports, each with mutual TLS 1.3:

| Lane | Config map | Who connects | ALPN (current, previous) |
| --- | --- | --- | --- |
| Application | `keepers` (and `listen`) | Clients such as RTDB, and other keepers | `logkeeper-consensus/2`, `logkeeper-consensus/1` |
| Control | `peers` | Keepers only: votes, heartbeats, pings, parking, leader transfer | `logkeeper-consensus-control/9`, `logkeeper-consensus-control/8` |
| Bulk and replication | `bulk` | Keepers only: AppendEntries batches and snapshot files | Bulk `/3`, `/2`. Replication `/4`, `/3` |
| Admin | `admin.listen` | Probes, metrics scrapers, operators | Plain HTTP on loopback, or mTLS |

Every address in the inventory (`keepers`, `peers`, `bulk`, and `admin.cluster`)
is `IP:port` or `name:port`. A DNS name resolves at every connect, trying each
address it returns, so a keeper that comes back on a new IP (a rescheduled pod)
is found again under the same name. The name is never trusted for identity:
every connection checks that the peer's certificate URI names the keeper the
route was for, and refuses it otherwise. A keeper binds the `peers` and `bulk`
addresses its own inventory lists for itself: an IP address as given, a name
on `0.0.0.0` at its port. `listen` stays an IP address. Addresses are compared
as text, so two names for one endpoint, or a name and the IP it resolves to,
are not detected as duplicates: the keeper does not resolve names when it
reads its configuration, since a name may not resolve yet (a pod not yet
scheduled). Such a mistake is still caught at connect time, because a route
that reaches the wrong keeper is refused. Give each keeper one spelling
everywhere.

A stream has three voters in three distinct failure domains, or five
voters (see [when to use five voters](#when-to-use-five-voters)). It commits
with a quorum: two of three, three of five. Each stream's leader:

- places, repairs and parks the stream;
- replaces a voter that has been silent for `repair_after_secs` (600 s by
  default) with a live keeper in a free domain, one voter at a time, but only
  while a quorum of voters is live;
- parks the stream on every voter once it has been idle for `park_after_secs`
  (600 s by default).

## Topology

**Three or more keepers across three failure domains.** Placement needs
between 3 and 1,024 keepers and three distinct domains in every roster,
including both sides of a joint change. Use one domain per availability zone.
With three keepers, every stream lives on all of them. Two layouts work:

- **Minimum: 3 keepers, one per zone.** Losing a keeper leaves every stream
  on two voters and nowhere to repair to, because the dead keeper's domain is
  the only free one. Streams stay writable. A second loss in another zone stops
  them until a keeper returns or an operator runs `recover-stream`.
- **Recommended: 6 keepers, two per zone.** Automatic repair then moves a dead
  keeper's streams to its sibling in the same zone after `repair_after_secs`,
  with no config change. You can replace a failed disk later, at leisure, with
  every stream back on three live voters. `recover-stream` also needs two
  live keepers outside a stream's lost configuration, so it only works with
  spare keepers. New streams are placed by rendezvous ranking of stream and
  keeper IDs, skipping keepers that are down, full, or more than a quarter
  above the average.

The keeper inventory is static: `keepers`, `peers`, `bulk` and `domains` are
read at startup. Adding a keeper means restarting every keeper with the new
inventory ([add, drain or remove a keeper](runbooks/add-drain-remove-keeper.md)).
Changing the inventory at runtime does not exist yet. Plan the keeper count
up front.

### The catalog

The catalog assigns each stream's genesis (ID, first voters, quota), records
staged membership changes, answers location lookups and grants keepers
leases. When leases are enabled, existing streams can read and write during
a catalog outage until their keepers' leases expire. Creation (a new RTDB
database) and staged repair need a catalog quorum.

- **Catalog keeper (`catalog`)**: one keeper holds the catalog alone. If it is
  down, nothing can be created or repaired. If its disk is lost, the record of
  which streams exist is lost too. Use it only for development.
- **Replicated catalog (`catalog_voters`)**: the catalog is a consensus stream
  of its own on three or five keepers. It is never parked, and the
  normal leader-driven repair repairs it. Since placement certification
  (commit `59038f5`), a copy that restarts without hearing from its leader
  asks the catalog before it campaigns or serves reads. After a whole-cluster
  restart, streams therefore elect only once the catalog answers. Start the
  catalog voters first, or together with the rest. Three voters tolerate one
  loss and five voters tolerate two. Recovery of the catalog itself requires
  returning enough voters to regain quorum.
  **Use five `catalog_voters` for new production clusters.** List the same
  sorted UUIDs on every keeper and in every client config. Put at most two
  of five voters in any one failure domain. With three voters, use three
  distinct domains. One voter must be the `catalog` keeper, which seeds the
  replicated catalog at first start.

Migrating from a single catalog keeper is a full stop: stop every keeper, add
`catalog_voters` to every keeper and consumer config, then start them all. The
`catalog` keeper must be up for the first start. Before bootstrapping five
voters, upgrade all keepers and consumers to a release that supports five.
See the README section "Keeper-hosted consensus streams".

The examples and the Kubernetes manifests list five catalog voters: five of
the six keepers, two each in two zones and one in the third. A three-voter
catalog still starts, but every keeper logs a warning at start, the catalog's
leader repeats it every few minutes, `logkeeper_consensus_catalog_voters`
reads 3, and the alert `LogkeeperCatalogBelowFiveVoters` fires after an hour.
The gauge reports the catalog's live membership as each keeper knows it (its
catalog replica's finalized configuration, else the configured genesis), so
it reads 5 once the catalog grew, even though the configs still name three.

#### Growing the catalog from three to five voters

The catalog grows online, through joint consensus, while it keeps serving
leases, creation and staging:

1. Upgrade every keeper and consumer to a release with cluster level 8, then
   finalize it: `logkeeper admin finalize-version`. A catalog refuses to grow
   before that (`Unsupported`).
2. Pick two more voters among the enrolled keepers so that no failure domain
   holds more than two of the five. Add keepers first if the inventory has
   fewer than five (adding a keeper restarts every keeper, one at a time).
3. Read the catalog's current revision: `logkeeper admin status --stream
   ffffffff-ffff-ffff-ffff-ffffffffffff`.
4. Grow it: `logkeeper admin replace --stream
   ffffffff-ffff-ffff-ffff-ffffffffffff --expected REVISION --voters
   A,B,C,D,E`, the three current voters and the two new ones. The catalog
   installs replicas on both new voters before it commits the joint
   membership, then finalizes the five. A retried command with the same
   revision answers the configuration already reached.
5. Check `logkeeper_consensus_catalog_voters` reads 5 on every keeper and the
   alert clears.

Leave `catalog_voters` in every config as it was: it names the catalog's
genesis, which a grown catalog keeps, and a keeper refuses a configuration
that differs from its durable genesis. Clients find the new voters through
the old ones' leader hints. Only the width can grow; a catalog never shrinks
from five to three.

### Co-locating with RTDB

RTDB Multi nodes and keepers can share hosts, but keep them apart where you
can:

- **Disk.** One WAL thread serves every stream on a keeper and fsyncs on every
  round. A WAL round over 2.5 s marks the media slow for 10 s. A slow keeper
  hands its streams' leadership to followers, refuses votes and new streams,
  and reports `accepting=false` (commit `b571b61`). A watchdog ends the keeper
  when a round stalls for 20 s. Give the keeper its own data volume. RTDB's local cache and checkpoint builds must not
  share it.
- **Failure domains.** A host that runs a keeper and an RTDB writer loses both
  together. That is tolerable, since another voter elects and RTDB fails over,
  but RTDB's writer lease (5 s) and the keeper's election timeout (450 to
  900 ms) add up on that path.
- **Reads.** Set `domain` in RTDB's `JournalConfig` to the RTDB node's zone.
  Its reads then go first to a voter in that zone. After each seal, the
  stream's leader moves to that zone once the voter there has caught up. It
  moves at most once every 60 s.

If you co-locate, reserve CPU and memory for the keeper (cgroup limits or
Kubernetes requests), and put its data on a separate device.

## Sizing

### Disk

Each keeper has two volumes:

- **Media** (`data`): WAL segments, snapshots, index pages. It must allow
  allocation units of at most 16 KiB.
- **Registry** (`enrollment`): the enrollment records, the trusted WAL
  boundary slots, and the incarnations each keeper has seen its peers under.
  It is small (well under 1 MiB per keeper; 1 GiB is plenty) and must not live
  inside the media directory. Put it on storage that survives loss of the
  media volume, and never roll it back.

Size the media for the sum of every hosted stream's retained bytes, plus fixed
headroom:

```text
media bytes >= (sum over streams hosted here of retained bytes) x 1.4   # measured framing and index overhead, 256 B records
             + 88 MiB      # admission headroom: control, maintenance, scratch
             + 36 MiB      # one snapshot build's scratch
             + 512 MiB     # incoming bulk snapshot transfers (4 sessions, 512 MiB total)
```

The ceilings that bound retained bytes:

- **Retained-byte quota** (`quota_bytes`): set per stream by its creator.
  RTDB takes it from `quota_bytes` in its `JournalConfig`.
- **Retained-record ceiling:** 262,144 records per stream on Logkeeper
  `main` (commit `7aa2225`). A further append returns `Full` until the writer
  trims.
- **Record size:** at most 4 MiB.
- **Unpurged log suffix:** at most 512 entries per stream.

A stream at its ceiling holds at most `min(quota_bytes, 262,144 x record
size)`. With R voters per stream (3 or 5) and N keepers, a keeper hosts on
average `R x streams / N` streams.

RTDB's journals stay far below the ceiling in steady state. RTDB checkpoints to
object storage and trims each stream when its retained suffix reaches 131,072
records ([RTDB side](#rtdb-side)). A stream normally holds at most 131,072
records plus whatever arrives while a checkpoint is being built.

### CPU and memory

The figures below were measured with the `consensus-streams` example:

```sh
cargo build --release --features consensus-testing --example consensus-streams
target/release/examples/consensus-streams --sync-mode fsync --streams 128 --active 0 --seconds 10 [--park-after 5]
target/release/examples/consensus-streams --sync-mode fsync --streams 16 --active 16 --seconds 20
```

**Conditions:**

- One Apple M6 laptop (12 cores, 24 GiB), with all four keepers (three voters
  and the catalog keeper) and the client in one process, on one APFS SSD.
- No network latency. The runs used plain `fsync` (`--sync-mode fsync`; the
  example now defaults to `full`), which on macOS
  does not drain the drive's cache (`sync_mode: full` costs about 2.3 ms per
  flush there). On Linux, both modes flush the device, so expect lower
  throughput than this table on Linux disks with real flush latency.
- 256-byte records, 16 records per batch unless stated otherwise.
- Release build of Logkeeper `main` at `6d43248`.
- CPU and peak RSS are for the whole process, so they cover three voters'
  worth of work. Divide by three for one keeper, as the "per keeper" columns
  do.
- Disk is the bytes of every file under the cluster directory, which holds
  three voters' copies.

| Workload | Process CPU | Per keeper | Peak RSS (process) | Disk (3 copies) |
| --- | --- | --- | --- | --- |
| 1 stream, idle | 0.01 cores | — | 39 MiB | 0.0 MiB |
| 128 streams, idle, not yet parked | 0.17 cores | 0.06 cores | 170 MiB | 0.5 MiB |
| 128 streams, idle, parked | 0.01 cores | 0.003 cores | 145 MiB | 0.5 MiB |
| 1 stream appending (23,600 records/s, reaches 236,000 records) | 1.2 cores | 0.4 cores | 1,177 MiB | 230 MiB after 10 s |
| 16 streams appending (108,000 records/s) | 4.8 cores | 1.6 cores | 1,766 MiB | 2,107 MiB after 20 s |
| 128 streams appending single records (2,100 batches/s, p50 54 ms, p99 148 ms) | 1.1 cores | 0.36 cores | 215 MiB | 29 MiB after 10 s |

What these figures mean for sizing:

- **Stream limit:** run at least Logkeeper `043e8e5`. Before that commit, a
  keeper restarted while holding more than `max_streams` streams could lose
  the snapshot objects of the streams it skipped.
- **Idle open stream:** about 0.5 millicores per voter for heartbeats.
  Parking removes that cost, and parked streams hold no Raft group. The
  default `max_streams = 128` counts open groups only. Each stream's state
  machine stays in memory while it is parked, which is open item 9 in the
  design doc. Budget about 1 MiB of RSS per hosted stream for the group and
  its buffers: (170 − 39) MiB for 128 streams on three voters.
- **Retained records** dominate memory. Each record costs a voter 64 bytes in
  the applied index, plus 64 bytes in the current snapshot. The README
  measured 137 bytes per record per voter after a restart, and 265 bytes
  directly after a fill. The 16-stream run above gives about 280 bytes per
  record per voter, including write-path state. A single stream filled to
  236,000 records in 10 s peaked much higher, at about 380 MiB per voter
  (1.6 KiB per record), which is transient write-path and snapshot-build
  state on top of the index. Budget 300 bytes per retained record per voter in
  steady state, and leave room for a peak of about 400 MiB per voter for each
  stream that is filling toward the ceiling at full speed. A stream that RTDB
  trims at 131,072 records costs about 40 MiB in steady state.
- **Disk per record** at 256-byte payloads is about 340 bytes per voter
  (2,107 MiB / 3 copies / 2.17 M records). Budget 1.4 times the payload size
  for small records.
- **Write CPU:** about 0.15 cores per 10,000 records/s per keeper on this
  machine, in 16-record batches. Single-record batches cost about ten times
  more per record. Cross-zone deployments add network time, not
  CPU.

A starting point for a production keeper serving up to 128 active RTDB
databases is 4 cores, 8 GiB of RAM, and a dedicated NVMe of
`streams x R / N x quota_bytes x 1.4` plus 1 GiB, with R = 3, or 5 for
five-voter streams. The Kubernetes manifest
requests 2 cores and 4 GiB and caps memory at 8 GiB. Measure on your own
hardware before you commit to these numbers. The example runs unchanged on
Linux.

### When to use five voters

A stream's replication factor is fixed when it is created: 3 by default, or
5 with `replication_factor: 5` in the consumer's `JournalConfig` (or `admin
create --replication-factor 5`).

| | Three voters | Five voters |
| --- | --- | --- |
| Commits with | 2 | 3 |
| Keeps writing after losing | any 1 voter | any 2 voters |
| Needs operator recovery after losing | 2 | 3 |
| Disk, memory and write CPU, per stream, cluster-wide | 3 copies | 5 copies (5/3 as much) |
| Commit latency | the faster of 2 followers | the 2nd-fastest of 4 followers |
| Domains | 3 distinct | 5 distinct when available, else at least 3 with at most 2 in any one |
| Keepers for automatic repair | 4+ (spares in free domains) | 6+ |
| Keepers for `recover-stream` | survivor + 2 spares outside the stream | survivors + 3 or 4 spares outside the stream |

Use five voters for the streams whose loss would be expensive and that must
stay writable through two concurrent failures: a disk dying while another
keeper is down for maintenance, a zone outage during a rolling upgrade, or a
second failure before repair finishes (`repair_after_secs`, 600 s by
default, plus catch-up). Typical candidates are the replicated catalog's
consumers, a cell's control journal and small, critical RTDB databases.
Keep three voters for bulk streams, where the extra two copies cost disk,
memory and CPU on every write for little gain.

Placement of five voters:

- With five or more failure domains, every voter has its own domain.
- With three or four domains, voters share domains so that none holds more
  than two: 2+2+1 over three domains, 2+1+1+1 over four. Losing any one
  domain then leaves at least three voters, a quorum. Losing two domains of
  three can stop the stream, as with three voters.
- Two domains cannot hold five voters without one holding three, so the
  catalog refuses the genesis. Three voters always need three domains.
- Repair picks a replacement in the emptiest domain first.

Before creating a five-voter stream:

1. Upgrade every keeper to a build with the `REPLICATION_FACTOR` feature.
2. Finalize: `lk admin finalize-version --config operator.json`. The catalog
   refuses five-voter geneses with `Unsupported` until the cluster has
   finalized level 7 (`CLUSTER_VERSION_REPLICATION`), because older keepers
   cannot read a five-voter roster. After finalizing, the cluster can no
   longer go back to the previous binary.
3. Size for `R = 5` in the formulas above and run at least six keepers in
   three or more zones, so repair has somewhere to go.

The measured cost of five voters against three is in the table below
(`LK_MEASURE_VOTERS=5`, see [measurements](#five-voter-measurements)).

### Five-voter measurements

Measured with `measure_consensus_append_throughput` (`cargo test --release
--features stream --lib measure_consensus -- --ignored --nocapture`, with
`LK_MEASURE_SECONDS=10` and `LK_MEASURE_VOTERS=3` or `5`) on a MacBook Pro M1
at Logkeeper `05940d3`: seven keepers in one process on one SSD, plain
`fsync`, no network latency, one record per append, each stream appending
serially. Single runs; repeat on your hardware.

| Workload | 3 voters: records/s, p50, p99 | 5 voters: records/s, p50, p99 | 5 vs 3 throughput |
| --- | --- | --- | --- |
| 1 stream, 256 B | 1,945, 0.36 ms, 5.0 ms | 1,511, 0.51 ms, 3.2 ms | 0.78x |
| 8 streams, 256 B | 3,123, 1.1 ms, 29 ms | 2,001, 3.1 ms, 14 ms | 0.64x |
| 32 streams, 256 B | 3,587, 5.0 ms, 39 ms | 2,081, 14 ms, 35 ms | 0.58x |
| 32 streams, 4 KiB | 2,223, 10 ms, 62 ms | 1,628, 18 ms, 48 ms | 0.73x |
| 8 streams, 64 KiB | 831, 4.5 ms, 71 ms | 1,165, 6.4 ms, 18 ms | 1.40x (noise) |

On one host every voter shares the CPU and the disk, so five voters cost
about two thirds more fsyncs and replication work per record and throughput
drops to roughly 0.6 to 0.8 of three voters when the host is the
bottleneck. The 64 KiB row ran faster with five voters, which is run-to-run
variance rather than a property of five voters. Across zones, the commit waits
for the second-fastest of four followers instead of the faster of two, so
expect median latency to track the second-nearest zone. Budget five voters
at 5/3 the disk, memory and write CPU of three, cluster-wide.

## Identity and credentials

Every connection is mutual TLS 1.3 against one CA (`tls.ca`). Identities are
certificate URI SANs:

| Principal | Certificate | URI SAN | Extended key usage |
| --- | --- | --- | --- |
| Keeper | one per keeper incarnation | `urn:logkeeper:keeper:<keeper-uuid>` | serverAuth and clientAuth |
| Client | one per application principal | `urn:logkeeper:client:<name>` | clientAuth |

Each keeper config lists client principals in three roles. The role rules on
`main` (commit `6d43248`):

| Role | Allowed |
| --- | --- |
| `readers` | Locate, head, configuration, keeper status, reads, proofs |
| `writers` | Everything a reader may do, plus seal, append, append batch, trim, prefer leader, acknowledge recovery |
| `administrators` | Everything a reader may do, plus create, replace, delete, retire a copy, and acknowledge recovery; **not** seal, append or trim |

RTDB creates each database's stream, moves it during placement
reconciliation, and writes it. Its principal must therefore be in both
`writers` and `administrators`. Keep a separate operator principal in
`administrators` for human tools. Per-stream authorization does not exist yet:
any writer may write any stream. Do not share keepers between tenants that
must not write each other's journals.

With `admin.mtls: true`, give Prometheus a CA-signed client certificate and
list its URI in `admin.metrics_readers`. This role permits `/metrics`, `/live`
and `/ready`. Administrators and cluster keepers can query the other admin
pages. To probe from a node-local process without a certificate, set
`admin.probe_listen` to a loopback address such as `127.0.0.1:5742`.
That listener serves `/live` and `/ready`. For Kubernetes, use an
`exec` probe that makes the request from inside the keeper pod.

### Enrollment: the provisioning authority

A keeper serves only media that was installed for it. Before the first start,
the provisioning authority (you) writes two files into the keeper's registry
directory:

- `placement.json`: `{"catalog": <uuid>, "domains": {<uuid>: <domain>, ...}}`.
  It must equal the config's `catalog` and `domains` exactly. Example:
  [`placement.example.json`](../deploy/consensus/placement.example.json).
- `<keeper-uuid>.provision.json`: `keeper`, the canonical absolute `data`
  path, the keeper's `domain`, and `certificate_sha256`, the lowercase hex
  SHA-256 of the certificate file. Example:
  [`provision.example.json`](../deploy/consensus/provision.example.json).

```sh
shasum -a 256 /etc/logkeeper/tls/keeper.pem | cut -d' ' -f1   # or sha256sum
```

The keeper checks the provision at every start. Rotating a keeper certificate
therefore means rewriting `certificate_sha256` ([certificate
rotation](runbooks/certificate-rotation.md)).

### A keeper ID is bound to its media

`keeper initialize` draws a fresh media incarnation and records it in the
registry (`<uuid>.enrolled`) and on the media (`KEEPER`). Every keeper also
records, in `<uuid>.incarnations.json`, the incarnation it first saw each peer
under.

**Never reuse a keeper ID on new disks.** A keeper that lost its data has also
lost its votes and its log. If it came back under its old ID as an empty
voter, it could help a lagging voter erase committed entries.

- **The registry refuses it.** `keeper initialize` refuses to enroll an ID
  that the registry has already enrolled.
- **Peers refuse it too (commit `6d75fec`).** If the registry was also lost
  and the ID is reused anyway, peers still know the old incarnation and say so.
  The keeper marks itself reused, registers no replica it does not hold, and
  peers stop counting its votes. Its old streams then report no replica on it,
  and their leaders replace it after `repair_after_secs`.

Defend in depth anyway. Issue each installation a new UUID and certificate,
and retire the old UUID in your inventory. See [replace a failed
disk](runbooks/replace-disk.md).

## First bring-up

For each keeper, in any order:

1. **Choose identities.** Draw one UUID per keeper (`uuidgen | tr A-Z a-z`).
   Pick its domain, its IP address and three ports (application, control,
   bulk), plus a loopback admin port.
2. **Issue the certificate** with URI SAN `urn:logkeeper:keeper:<uuid>` and
   both serverAuth and clientAuth. Issue client certificates for RTDB
   (`urn:logkeeper:client:rtdb`) and the operator.
3. **Write the config.** Start from
   [`keeper.example.json`](../deploy/consensus/keeper.example.json). Every
   keeper gets the same `keepers`, `peers`, `bulk`, `domains`, `catalog`,
   `catalog_voters` and role lists. `keeper`, `listen`, `data`, `enrollment`
   and `tls` are its own. The tuning fields, with their defaults:

   | Field | Default | Meaning |
   | --- | --- | --- |
   | `max_streams` | 128 | Streams with an open group. Parked streams do not count |
   | `repair_after_secs` | 600 | How long a voter stays silent before its stream's leader replaces it |
   | `park_after_secs` | 600 | How long a stream stays idle before its voters park it |
   | `snapshot_send_bytes_per_second` | 67108864 | Keeper-wide snapshot send rate; 0 means unpaced |
   | `sync_mode` | `full` | `full` (`F_FULLFSYNC` on Apple platforms) or `fsync`; on Linux both flush the device cache. Never use `fsync` on macOS in production |
   | `async_append` | `true` | A leader replicates its own appends while its WAL write of them is in flight; it counts toward commit only once that write is durable. `false` syncs first, as before |
   | `admin` | none | `{"listen": "127.0.0.1:5741", "mtls": false, "cluster": {...}}`. `cluster` lists the other keepers' admin addresses for `keeper debug-bundle` |
   | `log_format` | `human` | `human` or `json` |

   Unknown top-level fields
   only produce a warning.
4. **Create the directories.** `install -d -o logkeeper -g logkeeper -m 0700
   /var/lib/logkeeper/media /var/lib/logkeeper/registry`, each on its own
   volume. Leave `data` itself absent or empty, because `initialize` creates
   it.
5. **Write the authority** files `placement.json` and
   `<uuid>.provision.json` into the registry.
6. **Install the media, explicitly and once:**

   ```sh
   sudo -u logkeeper logkeeper keeper initialize --config /etc/logkeeper/keeper.json
   ```

   It prints nothing and exits 0. It refuses non-empty media ("keeper
   initialization requires empty media") and an ID the registry has already
   enrolled. Never run it from an automatic start path that could fire on a
   wiped disk. In the Kubernetes manifests it runs only for keeper UUIDs listed
   in the `logkeeper-initialize` ConfigMap.
7. **Start the keeper** with `systemctl enable --now logkeeper-consensus`, or
   apply the StatefulSet.

Then, from each keeper host:

```sh
curl -fsS http://127.0.0.1:5741/live    # {"live":true,"wal_healthy":true,"stopping":false,...}
curl -fsS http://127.0.0.1:5741/ready   # {"ready":true,...,"liveness_populated":true,...}
curl -fsS http://127.0.0.1:5741/metrics | grep logkeeper_build_info
```

`/ready` stays 503 until the keeper has reached at least one peer, so start
all of them. With `catalog_voters`, the `catalog` keeper seeds the replicated
catalog at its first start. Until that seed is done, creates fail with
`Unavailable`.

**The first stream.** Before you give RTDB the config, run a disposable stream
through create, seal, append, head and read with the operator principal, and
then delete it. For example, adapt the README's first-write snippet, or run
the [rolling-upgrade test](../tests/rolling_upgrade.rs) against a local
cluster. `logkeeper admin` covers the administrative half:

```sh
logkeeper admin create --config operator.json --stream $UUID --quota-bytes 67108864
logkeeper admin status --config operator.json --stream $UUID   # configuration, leader, head, replicas
logkeeper admin problems --config operator.json                # every keeper's /problems, merged
```

Seal, append and read need a writer, which `logkeeper admin` is not.
`peer.unreachable` refusals in the log at startup are expected until all
keepers are up.

### Kubernetes

The [Kustomize bundle](../deploy/consensus/kubernetes/) is a staging template
for six keepers on six dedicated nodes, with two nodes per zone. Each keeper
has its own singleton StatefulSet and TLS Secret. Its two retained local PVs
bind to the same host and point to separate media and enrollment filesystems.
All six pods have required hostname anti-affinity. Zone selectors put two
keepers in each zone, and the three initial catalog voters occupy three
different zones. Pods run on the pod network. Every inventory lists keeper N
by its pod's name under the headless `logkeeper` Service,
`logkeeper-N-0.logkeeper.logkeeper.svc.cluster.local`, for the application,
control, bulk and admin ports, so a rescheduled pod with a new IP is found
again. The Service sets `publishNotReadyAddresses: true`, because a keeper
turns ready only once it reaches a peer, and peers must resolve it before
that. Each keeper listens on `0.0.0.0`. Rename the hosts in `keepers/*.json`
if you deploy into another namespace.

1. Prepare six dedicated staging nodes. Set the zone labels, mount their two filesystems,
   and verify that UID/GID `10001` can write to both mounts. Set the hostname,
   path and storage size for each PV in `volumes.yaml`. Keep registry storage
   and its recovery copies independent of keeper media.
2. Set each workload's zone selector. Keep `placement.json`, each provision document and
   the RTDB journal and operator configs in agreement. Allow application port
   `5441` from approved clients and keepers, control and bulk ports `5541` and
   `5641` between keepers, and admin port `5741` from approved operators,
   scrapers and keepers, with NetworkPolicies. The probe listener on loopback port `5742` serves only
   `/live` and `/ready`.
3. In the staging namespace, create six Secrets named `logkeeper-tls-0`
   through `logkeeper-tls-5`. Give each Secret keys `tls.crt`, `tls.key` and
   `ca.crt` for that keeper only. Give the leaf both client and server usages,
   the keeper's URI SAN, and its pod name
   (`logkeeper-N-0.logkeeper.logkeeper.svc.cluster.local`) as a DNS SAN so
   that the rollover guard can verify the admin server. Set the `certificate_sha256` of each
   provision document to the SHA-256 hash of its `tls.crt` file. Set the
   metrics principal in `admin.metrics_readers` if enabling metrics collection.
4. In the staging Kustomization, set an `images` mapping for
   `logkeeper-consensus` to the pinned registry image name and digest. List
   only the six new UUIDs in `logkeeper-initialize` for first bring-up.
   The init container selects its public config by keeper ordinal. It refuses
   to start on media with no `KEEPER` marker unless the UUID is explicitly
   authorized to initialize. Use the [disk replacement runbook](runbooks/replace-disk.md)
   for lost media.
5. Render the staged configuration and run `deploy/consensus/tests/validate.sh`
   with `kubeconform` available. Apply to the staging context and check all
   six workloads.

   ```sh
   kubectl --context "$STAGING_CONTEXT" apply -k deploy/consensus/kubernetes
   for keeper in logkeeper-0 logkeeper-1 logkeeper-2 logkeeper-3 logkeeper-4 logkeeper-5; do
     kubectl --context "$STAGING_CONTEXT" -n logkeeper rollout status "statefulset/$keeper" --timeout=15m || break
   done
   kubectl --context "$STAGING_CONTEXT" -n logkeeper get pods,poddisruptionbudgets
   ```

6. Empty `logkeeper-initialize` and reapply immediately after bring-up. It is
   a stable-name ConfigMap so clearing the bootstrap authorization leaves
   the pod templates alone. Keep the authorization empty during normal
   operation.

Use the [guarded rollover procedure](runbooks/rolling-upgrade.md#kubernetes)
for voluntary restarts. StatefulSets use `OnDelete` and the shared
PodDisruptionBudget permits a single voluntary disruption through the
Eviction API. The rollover guard checks the keeper's `/safe-to-stop` report
before submitting the eviction. Node failure and liveness-triggered restarts
can happen independently of these controls.

### systemd

[`logkeeper-consensus.service`](../deploy/consensus/logkeeper-consensus.service)
runs the keeper as `logkeeper` with no capabilities. Its filesystem is
read-only except the two volumes. It uses a `@system-service` syscall filter
and `MemoryDenyWriteExecute`. The stop timeout is 30 s. SIGTERM hands each led
stream to a caught-up voter within at most 3 s, then closes the groups and
flushes the WAL. A WAL round stalled past 20 s ends the process by itself.
Restarts are rate-limited to 5 in 10 minutes, so a failing disk does not loop
forever. The unit does not wait for `/safe-to-stop`: gate planned stops in
the runbook, not in `ExecStop`, so an emergency stop still works.

## RTDB side

RTDB Multi is opt-in. The default RTDB deployment uses a shared Kafka log.
A Multi node runs `rtdb node --multi` (built with the `multi` and `s3`
features). In production it reads the journal from environment variables
only:

| Variable | Value |
| --- | --- |
| `RTDB_JOURNAL_URL` | `logkeeper-consensus:///etc/rtdb/journal.json`, an absolute path to a Logkeeper `JournalConfig` file. Any other URL selects the old stream keeper |
| `RTDB_JOURNAL_SLOTS` | Number of credential slots (1 to 8). A node claims a free slot by locking `node-slot-{slot}.lock` in `RTDB_KEY_DIRECTORY` |
| `RTDB_JOURNAL_{slot}_CERTIFICATE`, `_PRIVATE_KEY`, `_CA_CERTIFICATE` | PEM *contents*, not paths, for principal `urn:logkeeper:client:rtdb` |
| `RTDB_PEERS`, `RTDB_DATABASES`, `RTDB_KEY_DIRECTORY`, `RTDB_BUCKET`, `AWS_REGION`, `RTDB_NODE_IP` | The rest of the Multi node, see RTDB's `dev/doc/rtdb-multi-consensus-keeper.md` |
| `RTDB_TIMED_ORIGINAL_TRUST_FILE` | Optional keeper trust for timed originals |

The `JournalConfig`
([`rtdb-journal.example.json`](../deploy/consensus/rtdb-journal.example.json))
has these fields. Unknown fields are refused.

| Field | Required | Meaning |
| --- | --- | --- |
| `keepers` | yes | Application addresses of every keeper (the keepers' `keepers` map) |
| `catalog` | yes | The catalog keeper's UUID |
| `catalog_voters` | with a replicated catalog | The same three or five initial voter UUIDs as the keepers |
| `placement` | one of `placement` and `voters` | Keepers eligible to vote, with their domains. Each new stream gets three in distinct domains. Use this in production |
| `voters` | | A fixed roster for every stream, which never moves. Only for tests |
| `draining` | no | Placement keepers to move streams off |
| `quota_bytes` | yes | Retained-byte quota of each stream RTDB creates |
| `max_record_bytes` | no, default 4 MiB | Largest record |
| `deadline_ms` | no, default 10000 | Per-operation deadline |
| `domain` | no | The RTDB node's own domain, for local reads and leader preference. Write one file per zone |

RTDB re-reads this file every 5 s and, for each database it writes, calls
`reconcile_placement`. That moves at most one voter per stream per tick, so
editing `draining` or `placement` in place is how streams move.

**Checkpoint flags.** The RTDB writer checkpoints and trims each stream when
its retained suffix reaches 131,072 records, on a 250 ms maintenance loop. It
has no byte trigger. So set `quota_bytes` to at least 2 x 131,072 x your
largest typical commit size, or RTDB gets `rtdb/journal-full`. The Multi YAML
key `multiCheckpoints` has two flags:

- `deferred`: builds the checkpoint off the commit path.
- `binary`: CBOR transaction state.

Both default to `false`. Enable them only after every RTDB node runs a release
that reads them.

**Versions.** RTDB pins Logkeeper to a commit already on Logkeeper `main`.
The Logkeeper side lands first.

**Recovery.** RTDB Multi normally acknowledges a keeper recovery and
records it in the journal before accepting transactions. Set
`multiJournal.holdWritesAfterRecovery: true` to wait for an operator instead.
The [two-voter-loss runbook](runbooks/lose-two-voters.md) covers the sequence.

## Monitoring

Scrape `/metrics` with a node-local agent on loopback, or remotely over mTLS,
as `job="logkeeper"`, and load the alert rules in
[`deploy/prometheus/logkeeper-alerts.yml`](../deploy/prometheus/logkeeper-alerts.yml)
and the dashboard in [`deploy/grafana/logkeeper.json`](../deploy/grafana/logkeeper.json).
The README's operations section lists every alert with its first response.
The rules cover at least:

| Signal | Metric or endpoint | Alert when |
| --- | --- | --- |
| Keeper down | `/live` | 503 or no answer for 30 s |
| Not caught up | `/ready` | 503 for more than 5 minutes after a start |
| WAL stall | `logkeeper_consensus_wal_round_duration_seconds`, `logkeeper_consensus_media_responsive` | p99 above half the 2.5 s slow-round gate, where the keeper hands off leadership; the watchdog ends the keeper at 20 s |
| Under-replication | `/problems` `under_replicated`, `logkeeper_consensus_keeper_liveness{state="dead"}` | Any for longer than `repair_after_secs` |
| Quorum risk | `/problems` `leaderless`, `parked_with_dead_voter` | Any |
| Ceilings | `/problems` `near_record_ceiling`, `near_quota_ceiling`, `near_suffix_ceiling` | Any. The writer is not trimming |
| Refusals | `logkeeper_consensus_refusals_total{reason}` | Sustained increase |
| Disk room | `logkeeper_consensus_accepting` | 0. The keeper refuses new streams |
| Quarantine | `logkeeper_consensus_streams{state="quarantined"}` | Above 0 |
| Certificate expiry | your PKI | Under 30 days |
| Offload lag | `logkeeper_offload_lag_seconds`, `logkeeper_offload_upload_failures_total` | Over 5 minutes; failures for 10 minutes |
| Offload backpressure | `logkeeper_offload_backpressured_appends_total` | Any increase: writers are refused |
| Damaged object | `logkeeper_offload_corrupt_objects_total` | Any increase |

Logs go to stderr, structured (`log_format`, `LOGKEEPER_LOG`).
Administrative actions are logged under `logkeeper::audit`, and critical
invariant violations under `logkeeper::critical`
(`logkeeper_consensus_critical_total`). For an incident, collect
`logkeeper keeper debug-bundle --config FILE [--admin ADDR]... [--data DIR]
[--out FILE]`: a tar of the redacted config and the admin pages. It reaches
the keepers in `admin.cluster` (or `--admin`) only over mTLS admin
listeners. With loopback listeners, run it on every host.

## Supported-version policy: N-1

The policy: a keeper release supports peers and clients of the previous
release (N-1), so a rolling upgrade never runs a mixed cluster that cannot
talk. A release that writes a new durable format keeps writing the N-1 format
until the cluster is finalized at N. That way, rolling back to N-1 stays
possible until finalization. Downgrades below N-1 and skipping a release are
not supported.

Each lane accepts the current and previous ALPN. A version mismatch
counts as reachable for repair. `logkeeper admin finalize-version` checks
that every active keeper supports the write-version gate before enabling
the current disk formats. Compaction relocation and durable park marks also
wait for finalization. The previous binary tested for this upgrade is
`44d3f2aadb`. Check the release notes before planning an upgrade from an
earlier media format.

The procedure is in the [rolling-upgrade runbook](runbooks/rolling-upgrade.md).
The [rolling-upgrade test](../tests/rolling_upgrade.rs) runs it in process.

### Immutable stream histories

After every active keeper advertises immutable-stream support, finalize cluster version 4.
The journal contract can then create a stream with `create_immutable`.
Its durable genesis selects the history mode for that stream ID.
Each writer residence holds a distinct session, and its seal binds the next epoch to that session and the exact committed head.
Append, trim, and timed reservations carry the resulting session fence.
A consumer following a committed head can request a page that covers that head and resume at the next position.

Replica repair and joint membership changes preserve the same stream ID and history.
When the original quorum is permanently lost, a recovery that accepts a cut uses a fresh stream ID.
Consumers such as RTDB can restore an application cut and authorize a successor for the stable database name through a separately available authority.
The application's archived cut sets the recovery point.
Same-stream recovery is available for legacy mutable streams.

## Offload to object storage

Each stream's leader continuously uploads the committed prefix of its log to
an S3-compatible store (or a directory) and records the durable, replicated
`offloaded_through` through Raft. Configure the same `offload` section on
every keeper (see the [offload runbook](runbooks/offload.md)); nothing is
uploaded before `finalize-version` reaches level 5.

| Setting | Default | What it costs |
| --- | --- | --- |
| `batch_bytes` | 16 MiB | Largest object, and the waiting bytes that trigger an upload |
| `batch_interval_ms` | 10 000 | Most time a committed record waits for upload. One PUT per active stream every 10 s is about 260 000 PUTs a month, about $1.30 per continuously written stream at S3 Standard prices; idle streams upload nothing |
| `max_lag_bytes` | 256 MiB | Waiting bytes per stream at which the leader refuses appends (`Unavailable`) |
| `backpressure` | `true` | `false` keeps accepting writes through an outage, so a quorum loss then keeps only what a survivor holds |
| `retain_local_bytes` | absent | Absent: keepers keep every record until the writer trims it, and the store is a backup. Set: keepers drop offloaded records older than the newest N bytes per stream; reads below that go to the store, and the dropped bytes no longer count against the stream's quota |
| `cache_bytes` | 64 MiB | Segments each keeper caches for reads below its local floor |

The leader uploads; uploads are idempotent across leader changes (objects are
keyed by lineage and LSN range and written at most once). An operator
recovery starts a new lineage, so a deposed configuration's later uploads are
never used. The README's offload section has the measured throughput impact.

## Backup and restore

What exists:

- **Continuous offload** (above) keeps every committed record in object
  storage within `batch_interval_ms`.
- **`admin export-stream`** takes an online export of a stream into a
  directory (the same segment objects plus a manifest); **`admin
  import-stream`** loads an export into a new stream; **`admin
  restore-stream`** rebuilds a stream whose voters are all lost from the
  store alone, into a new stream ID, and reports the records it kept.

- **Replication** is the durability mechanism. Every acknowledged record is
  on a quorum of the voters in distinct domains (two of three, three of
  five), and leader-driven repair restores the others.
- **`keeper repair-snapshot --config FILE --stream UUID --snapshot FILE`**
  restores the exact snapshot bytes that the local WAL's digest names, onto a
  stopped keeper whose WAL is intact. It is for a damaged snapshot file, not
  for disaster recovery.
- **`keeper recover-stream`** rebuilds a legacy mutable stream from its surviving voters
  after a quorum is lost (two of three, three or four of five), accepting
  possible loss of acknowledged records. With
  offload it also takes the store's committed run when that is longer, and
  reports the exact loss point.
- **RTDB checkpoints** in object storage hold each database's state up to its
  last checkpoint. The journal holds only the suffix after it.

What does not exist:

- A cluster snapshot.
- Restoring the replicated catalog after it loses two voters.
- Point-in-time restore of a journal.

**Do not restore keeper media or registries from filesystem backups.** A
restored media volume is older than its registry's WAL boundary, and the keeper
refuses it ("data volume that silently loses acknowledged writes"). Restoring
the registry too would bring back a keeper with forgotten votes, which is the
amnesia that the never-reuse rule exists to prevent. A lost keeper is replaced
with a new ID, never restored.

Recommendations:

1. Treat the journal as a replicated log, not a backup target. Run six
   keepers (two per zone) so repair has somewhere to go.
2. Back up what RTDB needs to rebuild: object-storage checkpoints with
   versioning and object lock. RTDB Multi's `rtdb admin export` returns a
   checkpoint ticket tied to its source custody. Verify a cold application
   restore with the original processes and journals absent before counting
   a checkpoint ticket as a portable backup.
   RTDB Multi's portable backup rehearsal uses an authenticated archive and independently available key custody to seed a fresh immutable stream.
3. Back up the operator artifacts: keeper configs, `placement.json`,
   provision files, the CA and client certificates, and the inventory of which
   UUIDs are in service and which are retired. Do not back up private keys of
   keepers you would never restore.
4. Rehearse `recover-stream` and disk replacement in a staging cluster.

## Missing features

These are needed for a complete production story and do not exist on `main`.
Most are items in the consensus design's review tables.

| Missing | Effect | Workaround |
| --- | --- | --- |
| Runtime inventory change (T19) | Adding a keeper restarts every keeper | Plan the count; restart one at a time |
| Catalog recovery after a majority is lost | Creation and staging stop until enough voters return | Bootstrap five voters in at least three zones and replace failed ones promptly |
| Per-stream authorization (T13) | Any writer may write any stream | One keeper cluster per trust domain |
| Disaster restore without original enrollment | An inaccessible old pair cannot produce retirement proofs. One survivor cannot safely repair the old quorum | Restore enough original participants, or rebuild a fresh isolated cell from a qualified application backup |
