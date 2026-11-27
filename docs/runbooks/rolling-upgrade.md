# Rolling upgrade

The procedure restarts one keeper at a time onto a new binary: wait until it
is safe to stop, stop (which drains its leaders), upgrade, start, wait until
ready, and move on to the next keeper. Once the whole cluster runs the new
binary and has soaked, finalize the version. Every stream keeps two of its
three voters throughout. The [rolling-upgrade
test](../../tests/rolling_upgrade.rs) runs this sequence in process under
write load.

**What to expect.** The test was run ten times (40 restarts) on one loaded
Mac. It uses four keepers with a replicated catalog, and four streams that
each append a record every few milliseconds. Results:
- No acknowledged record was lost (32,481 checked).
- The worst append stall during a restart was 2.4 s, and the mean 0.8 s.
- A keeper was ready again at most 1.8 s after it started.

In 24 of the 40 restarts, the stopping keeper handed its leaders off and
writes paused for under 0.3 s. In the other 16, a leader was not handed off:
the hand-off only targets a follower that has matched the leader's last
entry, and under constant writes there often is none. Its streams then waited
out the 1.8 s lease plus an election. Budget about 2.5 s of write
unavailability per keeper restart, on the streams that keeper leads.

## Before you start

1. **Check compatibility.** With **[upgrades]**, the new release must be
   exactly one release ahead of every running keeper (N-1). On `main`
   without it, the two builds must have identical ALPNs. Compare
   `logkeeper_build_info` on a running keeper **[ops]**:

   ```sh
   curl -sS $ADMIN/metrics | grep '^logkeeper_build_info'
   # logkeeper_build_info{version="0.2.0",keeper="...",domain="zone-a",control_alpn="logkeeper-consensus-control/8",replication_alpn="logkeeper-consensus-replication/3",bulk_alpn="logkeeper-consensus-bulk/2"} 1
   ```

   Then check the constants in the new release's
   `src/stream/consensus/mod.rs`:

   ```sh
   git -C logkeeper show NEW_SHA:src/stream/consensus/mod.rs | grep '_ALPN: &\[u8\]'
   ```

   If any ALPN differs on `main` without **[upgrades]**, this is not a rolling
   upgrade. Stop every keeper, upgrade them all, and start them all.

2. **Check media format changes.** Read the release notes or the README's
   "Keeper storage and upgrade" section for a media format change, such as a
   new `FORMAT` in `storage/media.rs`. A keeper migrates its media on first
   start, and the old binary cannot reopen migrated media. With
   **[upgrades]**, new formats wait for finalization, so rollback stays
   possible until step 7.

3. **Check that the cluster is healthy.** On every keeper:

   ```sh
   probe ready         # 200, "ready":true
   probe problems      # 200, "problem_count":0, or only problems you understand
   ```

   Abort if any keeper is not ready, or if any stream is `leaderless` or
   `under_replicated`.

4. **Stage the binary** on every host without replacing the running one:

   ```sh
   install -m 0555 logkeeper-NEW /usr/local/bin/logkeeper.next
   /usr/local/bin/logkeeper.next --help | head -1   # Usage: logkeeper ...
   ```

## For each keeper, one at a time

5. **Wait until it is safe to stop:**

   ```sh
   until probe safe-to-stop | grep -qx 200; do sleep 5; done
   # {"safe":true,"keeper":"...","liveness_populated":true,"hosted_streams":42,"blocking":[]}
   ```

   `503` lists `blocking` entries of `{stream, voter, reason}`: another voter
   of a stream hosted here is unreachable or silent. **Abort** if it stays
   `503` for more than 5 minutes. Fix the other keeper first.

   Without **[ops]**: confirm from the other keepers' logs that no keeper
   reports `peer.unreachable` for the others, and wait 60 s after the
   previous keeper became ready.

6. **Drain leaders, stop, upgrade, start:**

   ```sh
   sudo systemctl stop $UNIT              # SIGTERM: leaders hand off within 3 s, WAL flushed
   systemctl show -p Result,ExecMainStatus $UNIT   # Result=success
   sudo install -m 0555 /usr/local/bin/logkeeper /usr/local/bin/logkeeper.prev
   sudo mv /usr/local/bin/logkeeper.next /usr/local/bin/logkeeper
   lk keeper verify --config $CONFIG      # [ops] optional, offline: exit 0, "ok"
   sudo systemctl start $UNIT
   ```

   There is no separate "drain leaders" command. The keeper hands every
   stream it leads to a caught-up voter as part of SIGTERM, waiting at most
   3 s. Streams it could not hand off elect a new leader within an election
   timeout (450 to 900 ms) after their lease expires. **Abort** and
   investigate the disk if the stop takes longer than 30 s (`Result=timeout`)
   or the unit exits with failure.

7. **Wait until it is ready:**

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

   To roll this keeper back: stop it, restore `logkeeper.prev`, and start it
   again. That works only if the new binary did not migrate the media (see
   step 2).

8. **Soak** for at least `minReadySeconds` (30 s), check `probe problems` on
   all keepers, then continue with the next keeper at step 5.

## After every keeper is upgraded

9. **Soak the whole cluster** for an agreed period, for example 24 h, at
   normal load. Until you finalize, rollback is the same procedure with the
   previous binary.

10. **Finalize [upgrades]:** this allows the new durable formats. It is
    refused unless every active keeper advertises the write-version gate.
    There is no CLI for it. Call it from a Rust program with an administrator
    principal:

    ```rust,ignore
    let finalized = journal.finalize_version(TARGET).await?;   // ConsensusJournal
    assert_eq!(finalized, TARGET);
    ```

    After finalizing, rolling back below this release is no longer
    supported.

## Kubernetes

The StatefulSet carries out steps 5 to 8 by itself:
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
