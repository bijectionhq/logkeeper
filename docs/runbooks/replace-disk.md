# Replace a failed disk

A keeper whose media is lost, wiped or replaced comes back as a **new keeper
with a new UUID**. Never run `keeper initialize` again under the old UUID:

- If the registry survived, it refuses (`File exists`, because `<uuid>.enrolled`
  is already there).
- If the registry was lost too, peers recognize the reused ID (commit
  `6d75fec`). The keeper registers no replicas and its votes do not count, so
  it serves nothing.

## 1. Confirm the loss and the survivors

On each other keeper:

```sh
probe problems | jq '.problems[] | {stream, reasons, dead_voters}'
# under_replicated streams naming the lost UUID in dead_voters; none leaderless
```

**Abort and go to [lose two voters](lose-two-voters.md)** if any stream shows
`leaderless`, or has two dead voters. Stop the failed keeper if it is still
running (`sudo systemctl disable --now $UNIT`). Keep its registry volume. It
proves the old UUID was consumed.

## 2. Let repair move the streams (6 or more keepers)

After `repair_after_secs` (600 s by default), each affected stream's leader
replaces the lost voter with a live, accepting keeper in a free domain. With
two keepers per zone, that is the lost keeper's sibling. Watch the repairs
progress:

```sh
curl -sS $ADMIN/metrics | grep -E 'logkeeper_consensus_repairs_(total|in_flight)'
probe problems | jq '.problem_count'        # falls to 0
```

Repairs run four at a time per leader, with per-stream backoff. **Abort** if
`repairs_total{outcome="failed"}` keeps rising for 30 minutes. Check the
target keepers' room (`logkeeper_consensus_accepting`).

With **3 keepers**, there is no free domain and repair cannot help. Every
affected stream stays on two voters until step 3 adds a keeper in the lost
domain.

## 3. Add the replacement as a new keeper

Follow [add a keeper](add-drain-remove-keeper.md#add-a-keeper) with a **new
UUID** in the lost keeper's domain. The old UUID stays in the inventory, so
the new keeper needs its own addresses. Reuse the host and IP with new ports,
for example 5442, 5542 and 5642.

- **With 3 keepers:** each survivor's restart in step 3 of that procedure
  leaves the streams it hosts with one live voter until it is ready again.
  Those streams are unavailable for the length of each restart (bounded by
  `/ready`, typically seconds). Schedule it, or add the new keeper during a
  quiet period.
- **With 6 keepers:** step 2 has already restored three voters everywhere,
  so the restarts are ordinary.

Once the new keeper is ready, repair uses it for any stream still missing a
voter (3-keeper case), after `repair_after_secs`.

## 4. Retire the old UUID

- Remove it from `placement` in every RTDB `JournalConfig`.
- Mark it `retired` in every keeper config and placement registry.
- Record it as retired, and destroy its key.
- Wipe and reuse the old registry volume only for a new UUID.

Done when `/problems` on every keeper shows no stream naming the old UUID.
