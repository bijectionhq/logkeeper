# Add, drain or remove a keeper

The keeper inventory (`keepers`, `peers`, `bulk`, `domains`) is static. It is
read at startup and must equal `placement.json` in each keeper's registry.
Changing it means restarting every keeper, one at a time. Draining is done by
the consumer: RTDB moves streams off keepers listed in `draining` in its
`JournalConfig`. There is no durable drain state on the keepers (T20).

## Add a keeper

1. **Choose identities.** Draw a new UUID and pick the keeper's domain, a
   stable IP and three ports. Every address in the inventory must be
   distinct. Issue its certificate with URI SAN `urn:logkeeper:keeper:<uuid>`
   (serverAuth and clientAuth).

2. **Update the inventory everywhere.** Add the new UUID to `keepers`,
   `peers`, `bulk` and `domains` in every keeper's config. Add it to
   `domains` in every registry's `placement.json`. Check that each pair
   matches:

   ```sh
   jq -S '{catalog, domains}' $CONFIG > /tmp/a.json
   jq -S . /var/lib/logkeeper/registry/placement.json > /tmp/b.json
   diff /tmp/a.json /tmp/b.json && echo match   # match
   ```

   A mismatch makes the keeper refuse to start, with "inventory does not
   match its trusted placement authority".

3. **Restart the existing keepers** one at a time with the [rolling-upgrade
   procedure](rolling-upgrade.md), steps 5 to 8, keeping the same binary. The
   new keeper is not running yet, so liveness reports it as dead and
   placement and repair never choose it. Its UUID is not a voter of any
   stream, so `/safe-to-stop` is not blocked by it.

4. **Provision and start the new keeper.** Write `placement.json` and
   `<uuid>.provision.json` into its registry, then:

   ```sh
   lk keeper initialize --config $CONFIG    # no output, exit 0
   sudo systemctl enable --now $UNIT
   until probe ready | grep -qx 200; do sleep 5; done
   ```

   On Kubernetes:
   - Add a fourth `keepers/keeper-3.*` set and the PVs for node 3.
   - Set `replicas: 4`.
   - List the new UUID in `logkeeper-initialize`.
   - Apply, then empty `logkeeper-initialize` again.

5. **Make it eligible for new streams.** Add the UUID to `placement`, with
   its domain, in every RTDB `JournalConfig` file, and to `keepers`. RTDB
   re-reads the files every 5 s. New streams are placed by rendezvous ranking, skipping keepers loaded more than a quarter above the average. Existing
   streams do not rebalance onto it by themselves; drain a busier keeper if
   you want to move them.

Abort criteria: the new keeper is not ready within 10 minutes, or any
existing keeper fails step 3. Undo by removing the UUID from the RTDB
`placement` first, then from the keeper inventory with another rolling
restart.

## Drain a keeper

Only streams whose RTDB writer is running move. RTDB reconciles a database's
stream only while it writes that database, at most one voter per stream every
5 s. Fixed `voters` rosters never move.

1. Make sure the remaining eligible keepers have room: three domains, each
   with an accepting keeper other than the drained one
   (`logkeeper_consensus_accepting 1` **[ops]**).

2. Add the UUID to `draining` in every RTDB `JournalConfig` file, keeping it
   in `placement`. Rewrite each file in place, atomically:

   ```sh
   jq '.draining += ["UUID"] | .draining |= unique' journal.json > journal.json.new
   mv journal.json.new journal.json
   ```

   RTDB logs `Multi journal placement moved stream <id> to revision <n>` for
   each move. `Multi journal placement deferred: ...` is retried on the next
   tick.

3. **Wait until no stream names the keeper.** On the drained keeper
   **[ops]**:

   ```sh
   curl -sS $ADMIN/metrics | grep 'logkeeper_consensus_streams{state="hosted"}'
   # logkeeper_consensus_streams{state="hosted"} 0
   ```

   Removed copies retire themselves, so `hosted` reaches 0 once every move
   has committed and retirement has run. Without **[ops]**, check each
   stream with `lk admin status --config operator.json --stream UUID`.

   Streams that RTDB does not write (databases with no running writer) do
   not move. Wake their writers or accept that they stay. If the keeper is a
   catalog voter, the catalog stream does not move with `draining`. It moves
   when its leader repairs it, after the keeper has been stopped for
   `repair_after_secs`.

Abort criteria: `hosted` stops decreasing for 10 minutes while RTDB logs
`deferred`. Remove the UUID from `draining` to cancel.

## Remove a keeper

1. Drain it (above) until `hosted` is 0, except for the catalog stream if it
   is a catalog voter.
2. Stop it: `probe safe-to-stop` should return 200, then run `sudo systemctl
   disable --now $UNIT`.
3. If it was a catalog voter, wait `repair_after_secs` (600 s by default) for
   the catalog leader to replace it. Check that `/problems` on the other
   keepers shows no `under_replicated` catalog stream (ID
   `ffffffff-ffff-ffff-ffff-ffffffffffff`).
4. Remove the UUID from `placement` and `draining` in every RTDB
   `JournalConfig`.
5. **Keep the UUID in the keeper inventory** on `main`. Removing it from
   `keepers` or `domains` changes placement validation for streams whose
   history names it (T11). With **[upgrades]**, move it to `retired` in every
   keeper config instead.
6. Record the UUID as retired in your inventory and never issue it again.
   Destroy its private key.
