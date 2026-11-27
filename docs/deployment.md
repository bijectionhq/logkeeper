# Deploying the consensus keeper

This guide is for operators who run Logkeeper's consensus keeper in production,
mainly as the journal of RTDB Multi. The [README](../README.md) documents the
APIs. This guide covers hosts, disks, identities, bring-up and day-two
operations. The [runbooks](runbooks/) hold the step-by-step procedures.

Every command, flag and config field here exists in the code on `main`. The
admin endpoints (`/live`, `/ready`, `/safe-to-stop`, `/problems`, `/status`,
`/metrics`), the offline `keeper inspect`, `verify`, `dump-segment` and
`debug-bundle` tools and structured logs are on `main`; the procedures assume
a keeper built with them. One group of features is still landing and marked
inline:

- **[upgrades]**: N-1 wire negotiation, the cluster write-version gate,
  `keeper salvage`, durable quarantine with `keeper clear-quarantine`, and
  `retired` keepers.

Until it reaches `main`, a marked step does not work, and each says what to
do instead. [Missing features](#missing-features)
lists what does not exist at all.

Packaging lives in [`deploy/consensus/`](../deploy/consensus/):

| File | What it is |
| --- | --- |
| `Dockerfile` | Multi-stage image, non-root (uid 10001), media and registry volumes, healthcheck on `/live` |
| `logkeeper-consensus.service` | Hardened systemd unit with a 30 s stop timeout |
| `kubernetes/` | Kustomize base: StatefulSet, pre-bound local volumes, PodDisruptionBudget, generated keeper configs |
| `keeper.example.json`, `placement.example.json`, `provision.example.json` | One keeper's config and its registry authority files |
| `rtdb-journal.example.json` | The RTDB side: a Logkeeper `JournalConfig` |
| `operator.example.json` | What `logkeeper admin` reads: the operator's credentials and every keeper's application and admin address |
| `tests/validate.sh` | Renders and validates the manifests |

`cargo test --features stream --test deploy_examples` checks that the example
configs parse the way the keeper and the client read them, and that they agree
with each other.

## What a keeper is

A keeper is one process, `logkeeper keeper --config FILE`, built with the
`stream` feature. It hosts one Raft group per stream (OpenRaft 0.10.1) on a
shared segmented WAL. It listens on three TCP ports, each with mutual TLS 1.3:

| Lane | Config map | Who connects | ALPN on `main` |
| --- | --- | --- | --- |
| Application | `keepers` (and `listen`) | Clients such as RTDB, and other keepers | `logkeeper-consensus/1` |
| Control | `peers` | Keepers only: votes, heartbeats, pings, parking, leader transfer | `logkeeper-consensus-control/8` |
| Bulk and replication | `bulk` | Keepers only: AppendEntries batches and snapshot files | `logkeeper-consensus-bulk/2`, `logkeeper-consensus-replication/3` |
| Admin | `admin.listen` | Probes, metrics scrapers, operators | Plain HTTP on loopback, or mTLS |

A keeper binds the `peers` and `bulk` addresses that its own inventory lists
for itself. Every address in the inventory is an `IP:port` (`SocketAddr`), and
DNS names are not accepted, so each keeper needs a stable IP address.

A stream has three voters in three distinct failure domains. It commits with
two. Each stream's leader:

- places, repairs and parks the stream;
- replaces a voter that has been silent for `repair_after_secs` (600 s by
  default) with a live keeper in a free domain, but only while two voters are
  live;
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
staged membership changes and answers location lookups. Existing streams keep
reading and writing while it is down. Creation (a new RTDB database) and
staged repair need it.

- **Catalog keeper (`catalog`)**: one keeper holds the catalog alone. If it is
  down, nothing can be created or repaired. If its disk is lost, the record of
  which streams exist is lost too. Use it only for development.
- **Replicated catalog (`catalog_voters`)**: the catalog is a consensus stream
  of its own on three keepers in distinct domains. It is never parked, and the
  normal leader-driven repair repairs it. Since placement certification
  (commit `59038f5`), a copy that restarts without hearing from its leader
  asks the catalog before it campaigns or serves reads. After a whole-cluster
  restart, streams therefore elect only once the catalog answers. Start the
  catalog voters first, or together with the rest. It survives losing one voter. Losing
  two stops creation and staging: existing streams keep serving, and recovery
  of the catalog itself does not exist yet ([missing features](#missing-features)).
  **Use `catalog_voters` in production.** List the same three sorted UUIDs on
  every keeper and in every client config. One of them must be the `catalog`
  keeper. That keeper seeds the replicated catalog once, at its first start
  with `catalog_voters`.

Migrating from a single catalog keeper is a full stop: stop every keeper, add
`catalog_voters` to every keeper and consumer config, then start them all. The
`catalog` keeper must be up for the first start. See the README section
"Keeper-hosted consensus streams".

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
size)`. With 3 voters per stream and N keepers, a keeper hosts on average
`3 x streams / N` streams.

RTDB's journals stay far below the ceiling in steady state. RTDB checkpoints to
object storage and trims each stream when its retained suffix reaches 32,768
records ([RTDB side](#rtdb-side)). A stream normally holds at most 32,768
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
  trims at 32,768 records costs about 10 MiB in steady state.
- **Disk per record** at 256-byte payloads is about 340 bytes per voter
  (2,107 MiB / 3 copies / 2.17 M records). Budget 1.4 times the payload size
  for small records.
- **Write CPU:** about 0.15 cores per 10,000 records/s per keeper on this
  machine, in 16-record batches. Single-record batches cost about ten times
  more per record. Cross-zone deployments add network time, not
  CPU.

A starting point for a production keeper serving up to 128 active RTDB
databases is 4 cores, 8 GiB of RAM, and a dedicated NVMe of
`streams x 3 / N x quota_bytes x 1.4` plus 1 GiB. The Kubernetes manifest
requests 2 cores and 4 GiB and caps memory at 8 GiB. Measure on your own
hardware before you commit to these numbers. The example runs unchanged on
Linux.

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

With `admin.mtls: true`, the admin listener also requires a client
certificate listed in `administrators`. There is no read-only metrics role, so
an mTLS scraper holds administrator rights. Prefer the loopback listener and a
node-local scraper.

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

   On `main`, unknown fields are refused at startup. With **[upgrades]** they
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

[`deploy/consensus/kubernetes/`](../deploy/consensus/kubernetes/) is a
Kustomize base. Render it with `kubectl kustomize`, and validate it with
`deploy/consensus/tests/validate.sh`. The design choices follow from the
keeper's rules:

- **Host network, pre-bound local volumes.** The inventory is `IP:port` and
  the keeper binds its own inventory addresses. So each pod runs on the host
  network, and its address is its node's IP. `volumes.yaml` pre-binds pod N's
  claims (`media-logkeeper-N`, `registry-logkeeper-N`) to local volumes on
  node N, which pins pod N to the node whose IP is in keeper N's config.
- **Stable keeper ID per pod.** The `install` init container takes the pod
  ordinal from the pod name. It copies `keepers/keeper-N.json` to the config
  path, and `placement.json` and `keeper-N.provision.json` into the registry
  volume. It installs media only if the media has no `KEEPER` file *and* the
  keeper's UUID is listed in the `logkeeper-initialize` ConfigMap. Otherwise
  it fails, which is the never-reuse rule.
- **Zones:** required anti-affinity on `topology.kubernetes.io/zone` and on
  `kubernetes.io/hostname`.
- **Probes:** a startup and liveness probe on `/live`, and readiness on
  `/ready`. Both use `curl` on loopback inside the pod, because a
  plain admin listener only binds loopback.
- **Rolling updates:** `podManagementPolicy: Parallel`, so the three pods can
  find each other at first start. `RollingUpdate` with `maxUnavailable: 1`
  and `minReadySeconds: 30` replaces one pod at a time and waits for `/ready`.
- **PodDisruptionBudget:** `maxUnavailable: 1`.
- **preStop:** waits up to 240 s for `/safe-to-stop`. SIGTERM then
  hands off leadership. `terminationGracePeriodSeconds: 300` covers both.
- **Certificates:** one Secret, `logkeeper-tls`, holds every keeper's
  `keeper-N.pem` and `keeper-N.key`, plus `ca.pem`. A plain StatefulSet cannot
  mount a different Secret per pod. Use the cert-manager CSI driver, or
  similar, to give each pod only its own key.

Create the Secret, set the node IPs, node names and certificate digests, and
set `logkeeper-initialize` to the three UUIDs for the first rollout. Then run:

```sh
kubectl apply -k deploy/consensus/kubernetes
kubectl -n logkeeper rollout status statefulset/logkeeper
```

Because the ConfigMap is generated with a hash suffix, empty the
`logkeeper-initialize` literal in `kustomization.yaml` and apply again once
all keepers are ready.

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
| `catalog_voters` | with a replicated catalog | The same three UUIDs as the keepers |
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
its retained suffix reaches 32,768 records, on a 250 ms maintenance loop. It
has no byte trigger. So set `quota_bytes` to at least 2 x 32,768 x your
largest typical commit size, or RTDB gets `rtdb/journal-full`. The Multi YAML
key `multiCheckpoints` has two flags:

- `deferred`: builds the checkpoint off the commit path.
- `binary`: CBOR transaction state.

Both default to `false`. Enable them only after every RTDB node runs a release
that reads them.

**Versions.** RTDB `main` pins Logkeeper `e24e4967`. At that commit, the
retained-record ceiling is 65,536, not 262,144, and RTDB's 32,768 threshold is
half of it. Logkeeper `main`'s keepers accept the 65,536-era client. Repin
RTDB only to a Logkeeper SHA already on `main`. The Logkeeper side lands
first.

**Recovery.** After `recover-stream`, RTDB's next seal gets
`JournalError::Recovered`, which RTDB reports as `rtdb/journal-recovered`.
RTDB at its current pin does not acknowledge it by itself. An operator
acknowledges with `logkeeper admin acknowledge-recovery --stream UUID`
(or `ConsensusJournal::acknowledge_recovery`; writer or administrator). The
[two-voter-loss runbook](runbooks/lose-two-voters.md) has the steps.

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

How this is enforced:

- **With [upgrades]:**
  - Each lane accepts ALPN N and N-1, and new frames go only to peers that
    advertise them.
  - A version mismatch counts as alive, so it never triggers repair.
  - New WAL and checkpoint formats wait for
    `ConsensusJournal::finalize_version`. That call is refused until every
    active keeper advertises the gate.
- **On `main` today:** none of that exists. Two builds interoperate only if
  every ALPN in `src/stream/consensus/mod.rs` is identical. Any ALPN bump
  between your running build and the new one means a full-cluster stop and
  start, not a rolling upgrade. Compare the `logkeeper_build_info` labels,
  or the constants in the source, before you upgrade.
- **Media formats** migrate forward on first start. For example,
  `logkeeper-raft-2` becomes `logkeeper-raft-3` (segments). Older binaries
  cannot reopen migrated media, so on `main` a rollback after a format
  migration is impossible. Take that into account before upgrading across a
  format change.

The procedure is in the [rolling-upgrade runbook](runbooks/rolling-upgrade.md).
The [rolling-upgrade test](../tests/rolling_upgrade.rs) runs it in process.

## Backup and restore

What exists:

- **Replication** is the durability mechanism. Every acknowledged record is
  on two of three voters in distinct domains, and leader-driven repair restores
  the third.
- **`keeper repair-snapshot --config FILE --stream UUID --snapshot FILE`**
  restores the exact snapshot bytes that the local WAL's digest names, onto a
  stopped keeper whose WAL is intact. It is for a damaged snapshot file, not
  for disaster recovery.
- **`keeper recover-stream`** rebuilds a stream from its last surviving voter
  after two are lost, accepting possible loss of acknowledged records.
- **RTDB checkpoints** in object storage hold each database's state up to its
  last checkpoint. The journal holds only the suffix after it.

What does not exist:

- Online backup or export of a keeper's streams.
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
   versioning and object lock, and RTDB's own `rtdb admin export`.
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
| DNS names in the inventory | Keepers need stable IPs; Kubernetes uses host networking | Static IPs, pinned nodes |
| Runtime inventory change (T19) | Adding a keeper restarts every keeper | Plan the count; restart one at a time |
| Durable decommission state (T20) | A leadership drain is durable (`logkeeper admin drain`), but moving replicas off a keeper lives only in the consumer's `draining` list | Edit RTDB's `JournalConfig` |
| Catalog recovery after two voters are lost (review item 12) | Creation and staging stop until a voter returns | Keep catalog voters in three zones; replace failed ones promptly |
| TLS reload without restart (T12) | Certificate rotation restarts each keeper | Rolling restart |
| Per-stream authorization (T13) | Any writer may write any stream | One keeper cluster per trust domain |
| Read-only metrics principal | mTLS scrapers are administrators or keepers | Loopback admin listener and a local agent |
| Online backup and export | See [backup](#backup-and-restore) | RTDB checkpoints |
| Catalog-bounded leases | A lost keeper that never stopped stays certified and, with the other lost keeper, can keep leading the old configuration. Restarting lost keepers are fenced by placement certification | Fence both lost keepers before `recover-stream` (`--lost` states it) |
