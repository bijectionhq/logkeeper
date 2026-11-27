# Add, drain or remove a keeper

The keeper inventory (`keepers`, `peers`, `bulk`, `domains`) is static. It is
read at startup and must equal `placement.json` in each keeper's registry.
Changing it means restarting every keeper, one at a time.

Use `lk admin drain` for maintenance when replicas should stay in place.
For permanent removal, use `lk admin decommission` to move the replicas too.
Both modes survive restart and block new replica registration on the keeper.

## Add a keeper

1. **Choose identities.** Draw a new UUID and pick the keeper's domain, a
   stable IP or DNS name and three ports. Every address in the inventory
   must be distinct. Issue its certificate with URI SAN `urn:logkeeper:keeper:<uuid>`
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
   procedure](rolling-upgrade.md), steps 6 to 9, keeping the same binary. The
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
   - Add a singleton keeper StatefulSet and matching config, dedicated TLS
     Secret, and two retained local PVs. Give the new keeper a new ordinal
     and pin it to the node and zone in its inventory.
   - List the new UUID in `logkeeper-initialize`, apply and wait for readiness,
     then clear `logkeeper-initialize` and apply again.
   - Use the [guarded rollover procedure](rolling-upgrade.md#kubernetes) for
     existing keepers that need to reload their inventory.

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

```sh
lk admin drain --config operator.json --keeper "$KEEPER"
# mode: draining
# drained: true
```

The keeper hands off leadership and stops campaigning. Its replicas still
vote. Run `lk admin undrain --config operator.json --keeper "$KEEPER"` when
the maintenance is done.

## Decommission and remove a keeper

1. Ensure the remaining keepers have enough room and three failure domains.
   Replicate a single-keeper catalog before decommissioning its host. A
   replicated catalog moves through the same quorum repair as other streams.
2. Move replicas and wait for their retirement:

   ```sh
   lk admin decommission --config operator.json --keeper "$KEEPER"
   # mode: decommissioning
   # led: 0
   # hosted: 0
   # safe_to_delete: true
   ```

   This includes parked streams. If the command times out, use
   `lk admin drain-status --config operator.json --keeper "$KEEPER"` to check
   progress. Check the cluster's problems and spare capacity if the number
   of hosted replicas stops decreasing. Keep the keeper running until its
   report says `safe_to_delete: true`. Use `undrain` to cancel further moves.
3. Stop the keeper and remove it from RTDB placement. Mark its UUID retired
   in the keepers' configs and placement registries so historical placements
   still validate. Preserve the addresses and configured catalog seed until
   the remaining keepers have been restarted with a consistent inventory.
4. Record the UUID as retired and never issue it again. Retire its private
   key and delete the stopped keeper's data only after the safe-to-delete
   check.
