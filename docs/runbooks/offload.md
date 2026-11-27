# Offload, backup, export and restore through object storage

Use this runbook to turn on continuous offload, take an online backup or an
export of a stream, import it, restore a stream whose voters are all gone,
and handle an object-store outage or a damaged object. Background:
[deployment guide](../deployment.md#offload-to-object-storage) and the
module documentation of `src/stream/consensus/offload/mod.rs`.

## What offload guarantees

- The leader of each stream uploads the committed prefix in immutable
  segment objects, keyed by lineage and LSN range, and records the
  replicated `offloaded_through` through Raft. Every voter knows it.
- The uploaded records are a prefix of the committed log: every record in an
  object equals the committed record at its LSN.
- After losing a quorum, `recover-stream` keeps every record at or below
  `max(survivor head, end of the store's committed run)` and reports that
  loss point exactly. Records a writer was acknowledged above it are lost.
- With no voter left, `admin restore-stream` rebuilds the stream into a new
  stream ID from the store alone and reports the records it kept.

## 1. Turn on offload

1. Create a bucket (or prefix) for the cluster. Enable versioning and an
   object-lock or deletion policy that matches your backup retention; keepers
   never delete objects.
2. Add the same `offload` section to every keeper's configuration (keepers
   ignore unknown top-level fields, so it can roll out before the binary):

   ```json
   "offload": {
     "url": "s3://logkeeper-prod/cluster-a",
     "region": "eu-west-1",
     "batch_bytes": 16777216,
     "batch_interval_ms": 10000,
     "max_lag_bytes": 268435456,
     "backpressure": true
   }
   ```

   Credentials come from `access_key_id` and `secret_access_key` or the
   standard `AWS_*` environment variables. For MinIO, add
   `"endpoint": "http://127.0.0.1:9000", "allow_http": true`.
3. Restart keepers one at a time (rolling-upgrade runbook).
4. Finalize the cluster version once every keeper runs this release:
   `logkeeper admin finalize-version --config admin.json`. Nothing is
   uploaded and no new format is written before level 5 is finalized, so a
   rollback stays possible until then.
5. Check `logkeeper admin offload-status --config admin.json --stream UUID`:
   `offloaded_through` should follow the head within `batch_interval_ms`.
6. Optional: set `retain_local_bytes` to let keepers drop offloaded records
   beyond that many of the newest bytes per stream. Reads below the local
   floor are then served from the store (first read of an object costs one
   GET; the keeper caches `cache_bytes` of segments).

## 2. Online backup and export

Give the operator configuration the same `offload` section. Then:

```text
logkeeper admin export-stream --config admin.json --stream UUID --to /backups/stream-UUID-2026-11-27
```

The leader first uploads everything committed (a flush), then the command
copies the segment objects covering the logical floor to the head, verbatim,
into the directory, with `manifest.json` (floor, head, writer epoch, the
objects and their SHA-256). The writer keeps writing during the export; the
export holds the stream as of the flush.

## 3. Import or clone into a new stream

```text
logkeeper admin import-stream --config admin.json --from /backups/stream-UUID-2026-11-27 \
  --stream NEW_UUID --quota-bytes 1073741824 [--voters A,B,C]
```

The command verifies every object against the manifest, uploads the records
under the new stream's prefix, creates the stream and points it at them. The
new stream reports the exported floor and head, serves the history from the
store, and its first writer must seal above the exported epoch. Point the
writer (for example the RTDB database) at the new stream ID.

## 4. Restore a stream with no surviving voter

When every voter of a stream is lost (`recover-stream` needs one survivor):

```text
logkeeper admin restore-stream --config admin.json --from-stream OLD_UUID \
  --stream NEW_UUID --quota-bytes 1073741824 [--floor LSN] --acknowledge-data-loss
```

The store does not know the writer's trim floor: objects uploaded before a
trim still hold the trimmed records. Pass `--floor` (the writer's last trim
plus one, for RTDB its last checkpoint's position) to leave them out.

It reads the store's lineage records to find the authoritative objects
(a deposed configuration's later uploads under an older lineage are never
used), takes the longest committed run, and reports it as
`kept: records FLOOR..=HEAD`. Records acknowledged after the last upload are
lost; compare `HEAD` with what the writer last acknowledged (RTDB reports a
shortened journal). Then repoint the writer to `NEW_UUID`. The old stream
ID stays in the catalog, unserved.

## 5. Recover from one survivor with the store

Follow [lose-two-voters](lose-two-voters.md). With `offload` in the
survivor's configuration, `recover-stream` also reads the store; the report
ends with

```text
Loss point: records 1..=N are kept (survivor head S, survivor's
offloaded_through O, object store run ending at E, which replaced the
survivor's copy); acknowledged records above N are lost. Offload continues
under lineage L.
```

If the store's run is longer than the survivor's log (the survivor lagged),
the recovered stream serves the store's history and drops the survivor's
shorter copy. The command refuses when the store cannot be read: fix access
first, or remove `offload` from the survivor's configuration to recover from
the survivor alone (and accept the shorter loss point).

## 6. Object-store outage

Symptoms: `LogkeeperOffloadUploadsFailing`, then `LogkeeperOffloadLagging`,
then `LogkeeperOffloadBackpressure` once `max_lag_bytes` wait on a stream.

1. Writers are refused with `Unavailable` while backpressure holds; reads,
   failover and repair continue. Reads below a keeper's local floor fail
   with `Unavailable` while the store is down.
2. Restore the store's reachability or credentials. Uploads resume within
   30 s (backoff cap); the lag drains and writers resume without action.
3. To keep writing through a long outage instead, set `"backpressure": false`
   and restart keepers one at a time. Records then wait on the keepers' disks
   (bounded by the stream quota), and a quorum loss during the outage keeps
   only what the survivor holds.

## 7. Damaged object

Symptom: `LogkeeperOffloadCorruptObject`, or reads below the local floor
answered `Corrupted`.

1. Reads already skip a damaged object when another object of the same
   lineage covers the record (a retry or a new leader uploaded the range in
   another batching).
2. Restore the object from the bucket's version history, or from an export
   (`objects/` in the export directory holds the same bytes under the same
   lineage and range).
3. If neither exists but the keepers still hold the records (their local
   floor is at or below them), reads keep working from the keepers' copies.
   Raise `retain_local_bytes` so retention does not drop them; exports of
   that range fail until the object is replaced. Otherwise the records in
   that object are lost: restore from an older export or accept the gap.
