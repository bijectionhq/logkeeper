# Rolling upgrade

The procedure restarts one keeper at a time onto a new binary: wait until it
is safe to stop, stop (which drains its leaders), upgrade, start, wait until
ready, and move on to the next keeper. Once the whole cluster runs the new
binary and has soaked, finalize the version. Every stream keeps two of its
three voters throughout. The [rolling-upgrade
test](../../tests/rolling_upgrade.rs) runs this sequence in process under
write load.

**What to expect.** The test uses four keepers with a replicated catalog, and
four streams that each append a record every few milliseconds. Before the
drain and shutdown paths paused writes for their hand-off (`55e94a5`, ten
runs, 40 restarts), the worst append stall during a restart was 2.35 s and the
mean 0.66 s, because 16 of 40 hand-offs found no follower matched under
constant writes and waited out a lease and an election. With the pause,
a ten-run sample on Logkeeper `0c44279` (Apple M1 Pro, load average 3 to 7,
2026-11-27):
- this test, 40 restarts with a drain: worst append stall 0.064 s, mean
  0.025 s; `/safe-to-stop` answered at once and a stop took at most 0.11 s;
  a keeper was ready again at most 0.61 s after it started; every
  acknowledged record was there afterwards (4,534 to 5,134 per run);
- the [hand-off test](../../tests/leader_handoff.rs), 80 restarts by plain
  SIGTERM with no drain: every restart handed off, worst stall 0.043 s, mean
  0.030 s.

The [compatibility tests](../../tests/upgrade_compatibility.rs) run this
procedure across real binaries: four keepers move from the previous release
to this one, catalog keepers first, under writes, then
`logkeeper admin finalize-version` finalizes.

## Before you start

1. **Check compatibility.** Use the previous release supported by the target
   binary. This release was tested against Logkeeper `44d3f2aadb`. Check the
   current and previous ALPNs in the target source and compare them with
   `logkeeper_build_info` on a running keeper.

2. **Upgrade catalog keepers first when the protocol grows.** A new
   application request, such as `Request::Staging` from commit `59038f5`, is
   refused by older catalog keepers. A restarted copy that cannot certify
   its placement does not campaign. So upgrade the `catalog` keeper and the
   `catalog_voters` before the other keepers. The release notes or the README
   say when a release adds a request.

3. **Check media format changes.** Read the target release's storage and
   upgrade notes. During a supported N−1 rolling upgrade, the write-version
   gate keeps the media compatible with the previous binary until step 11.

4. **Check that the cluster is healthy.** On every keeper:

   ```sh
   probe ready         # 200, "ready":true
   probe problems      # 200, "problem_count":0, or only problems you understand
   ```

   Abort if any keeper is not ready, or if any stream is `leaderless` or
   `under_replicated`.

5. **Stage the binary** on every host without replacing the running one:

   ```sh
   install -m 0555 logkeeper-NEW /usr/local/bin/logkeeper.next
   /usr/local/bin/logkeeper.next --help | head -1   # Usage: logkeeper ...
   ```

## For each keeper, one at a time

6. **Wait until it is safe to stop:**

   ```sh
   until probe safe-to-stop | grep -qx 200; do sleep 5; done
   # {"safe":true,"keeper":"...","liveness_populated":true,"hosted_streams":42,"blocking":[]}
   ```

   `503` lists `blocking` entries of `{stream, voter, reason}`: another voter
   of a stream hosted here is unreachable or silent. **Abort** if it stays
   `503` for more than 5 minutes. Fix the other keeper first.

   A previous binary may predate the admin listener. In that case check the
   other voters of each hosted stream with `lk admin status --stream UUID
   --config operator.json`, and proceed only when both are reachable and
   report healthy. Start the new binary with the admin listener enabled. Add
   the `admin` section to the keeper's configuration together with the new
   binary, not before: a previous binary that predates the admin listener
   refuses its configuration with `unknown field admin`. A rollback to such
   a binary must remove the section again. From this release on, a keeper
   ignores an unknown top-level field with a warning, so later releases can
   add settings ahead of their binary.

7. **Drain leaders, stop, upgrade, start:**

   ```sh
   lk admin drain --config operator.json --keeper $KEEPER --wait-secs 120
   # keeper ...: leads 12 streams    (one line a second on stderr)
   # mode: draining
   # led: 0
   # drained: true
   sudo systemctl stop $UNIT              # SIGTERM: anything still led hands off within 3 s, WAL flushed
   systemctl show -p Result,ExecMainStatus $UNIT   # Result=success
   sudo install -m 0555 /usr/local/bin/logkeeper /usr/local/bin/logkeeper.prev
   sudo mv /usr/local/bin/logkeeper.next /usr/local/bin/logkeeper
   lk keeper verify --config $CONFIG      # optional, offline: exit 0, "ok"
   sudo systemctl start $UNIT
   ```

   `lk admin drain` marks the keeper draining in its data directory, so the
   mark survives the restart: the keeper hands every stream it leads to a
   caught-up voter, retrying each second, starts no election of its own,
   takes no handed-off leadership, and reports that it accepts no new
   streams. The command waits until the keeper leads nothing, at most
   `--wait-secs`, and exits non-zero if it still leads some. That is not a
   reason to abort: under constant writes a hand-off can wait for a
   follower to match, and SIGTERM hands off whatever is left, waiting at most
   3 s. Streams it could not hand off elect a new leader within an election
   timeout (450 to 900 ms) after their lease expires. Without the admin
   listener, skip the drain; SIGTERM does it alone. **Abort** and
   investigate the disk if the stop takes longer than 30 s (`Result=timeout`)
   or the unit exits with failure.

8. **Wait until it is ready:**

   ```sh
   until probe ready | grep -qx 200; do sleep 5; done
   # {"ready":true,"wal_healthy":true,"wal_replayed":true,"liveness_populated":true,
   #  "quarantined_streams":[],"unmatched_streams":[],...}
   ```

   Ready means: the WAL has been replayed, a peer has been reached, and every
   hosted replica is parked or matched by its leader. **Abort** the rollout
   (do not continue to the next keeper) if any of these happens:
   - `/live` returns 503;
   - `quarantined_streams` is not empty;
   - the keeper is not ready within 10 minutes;
   - `/problems` on another keeper shows `leaderless`.

   Then let it lead again; the drain mark stays until you clear it:

   ```sh
   lk admin undrain --config operator.json --keeper $KEEPER   # mode: serving
   ```

   To roll this keeper back: stop it, restore `logkeeper.prev`, and start it
   again. Rollback requires that the media still use a format the previous
   binary supports (see step 3). The operator mode lives in
   `operator-mode.json` in the data directory, which a release without
   operator mode ignores: a rolled-back keeper that was draining or
   decommissioning serves, campaigns and takes new placements again, and
   nothing reports it. Repair does not move its replicas while it runs the
   old binary. It resumes draining or decommissioning when upgraded again,
   until you clear the mark with `lk admin undrain`. So before rolling back
   a keeper in the middle of a decommission, expect the decommission to
   pause, and check `lk admin drain-status` after the next upgrade. When the outgoing binary predates `admin drain`,
   use its graceful shutdown in step 7.

9. **Soak** for at least `minReadySeconds` (30 s), check `probe problems` on
   all keepers, then continue with the next keeper at step 6.

## After every keeper is upgraded

10. **Soak the whole cluster** for an agreed period, for example 24 h, at
   normal load. Until you finalize, rollback is the same procedure with the
   previous binary.

11. **Finalize.** Once every active keeper supports the write-version gate
    and the cluster has soaked, enable the new durable formats:

    ```sh
    lk admin finalize-version --config operator.json
    # cluster_version: 3
    ```

    It is refused with `Unsupported` while a keeper in the inventory,
    draining or retired ones still listed in `keepers` included, runs a
    binary without the gate, and with `Unavailable` while one does not
    answer; retry the latter. Once finalized, keepers write the formats the
    previous binary cannot read (`LKRWAL05` checkpoints, compaction's
    `Relocate` frames, durable park marks), and a previous binary refuses
    the media at startup.

    Schedule finalization after the rollback window has ended.

## Kubernetes

Stage the digest in the Kustomization for both `keeper` and `install` and
apply it to the staging context. The StatefulSets use `OnDelete`, so
applying a template leaves running pods in place. Serialize voluntary
maintenance across all keepers, including node drains. The operator running
this procedure needs `get` on pods, StatefulSets and PodDisruptionBudgets,
`create` on `pods/exec` and `pods/eviction`, and permission to apply the staged
template. Keep direct pod deletion out of routine operator permissions.

```sh
kubectl --context "$STAGING_CONTEXT" apply -k deploy/consensus/kubernetes
python3 deploy/consensus/kubernetes/roll-keeper.py \
  --context "$STAGING_CONTEXT" --namespace logkeeper logkeeper-0 --evict
```

Omit `--evict` to check without replacing a pod. With `--evict`, the guard
queries the selected keeper's mTLS `/safe-to-stop` endpoint immediately
before requesting eviction of that exact pod UID. An unsafe report, probe
failure or rejected eviction stops the command. The Eviction API observes
the shared PodDisruptionBudget. After the replacement reaches `Ready` at the
expected controller revision, verify cluster health and the workload's live
image digest before proceeding to the next keeper. Follow the mixed-version
checks and finalization steps above. Use the same once-per-keeper checks for
planned node maintenance, and apply the preflight at the point of eviction.

If a replacement fails to become ready, stop the rollout. Inspect the
replacement and the event log. To roll back while the on-disk version still
allows it, restore the previous pinned digest, apply the templates and follow
the guarded procedure for healthy keepers that changed. If the target cannot
serve preflight, handle that keeper as an incident and check the remaining
stream quorums before any direct recovery action.
