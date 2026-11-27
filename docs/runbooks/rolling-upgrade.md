# Rolling upgrade

The procedure restarts one keeper at a time onto a new binary: wait until it
is safe to stop, stop (which drains its leaders), upgrade, start, wait until
ready, and move on to the next keeper. Once the whole cluster runs the new
binary and has soaked, finalize the version. Every stream keeps two of its
three voters throughout. The [rolling-upgrade
test](../../tests/rolling_upgrade.rs) runs this sequence in process under
write load.

**What to expect.** The test was run ten times (40 restarts) on one loaded
Mac, at Logkeeper `55e94a5` with asynchronous leader append. It uses four
keepers with a replicated catalog, and four streams that each append a record
every few milliseconds. Results:
- No acknowledged record was lost (79,079 checked).
- The worst append stall during a restart was 2.35 s, and the mean 0.66 s.
- A keeper was ready again at most 2.3 s after it started.

The drain and shutdown paths now pause writes briefly while a target voter
catches up. The mixed-binary qualification also runs a complete rolling
restart with writes in flight.

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
   report healthy. Start the new binary with the admin listener enabled.

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
   binary supports (see step 3). A release without operator mode ignores
   the drain mark. The keeper resumes draining when upgraded again,
   until you clear the mark. When the outgoing binary predates `admin drain`,
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
    # cluster_version: 2
    ```

    Schedule finalization after the rollback window has ended.

## Kubernetes

The StatefulSet carries out steps 6 to 9 by itself:
- The `preStop` hook waits for `/safe-to-stop`, for at most 240 s.
- SIGTERM hands off leadership.
- The next pod is replaced only after `/ready` has held for
  `minReadySeconds`.

Stage the rollout with `partition`, so you can stop it between pods:

```sh
kubectl -n logkeeper patch statefulset logkeeper --type merge \
  -p '{"spec":{"updateStrategy":{"rollingUpdate":{"partition":2}}}}'
kubectl -n logkeeper set image statefulset/logkeeper keeper=IMAGE:NEW install=IMAGE:NEW
kubectl -n logkeeper rollout status statefulset/logkeeper   # only logkeeper-2 is replaced
# check probes and /problems, then partition 1, then 0
```

**Abort** by setting `partition` back to 3 (which freezes the rollout) and
restoring the previous image on the replaced pods. If a preStop hook gave up
after 240 s, the pod logs show `safe-to-stop still refused after 240 s`. Treat
that as an abort signal for the remaining pods.
