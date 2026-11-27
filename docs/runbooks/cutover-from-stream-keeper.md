# Cutover from the stream keeper to the consensus keeper

RTDB Multi chooses its journal backend per process, through one URL:

- `RTDB_JOURNAL_URL=logkeeper+tls://...` selects the old stream keeper;
- `RTDB_JOURNAL_URL=logkeeper-consensus:///etc/rtdb/journal.json` selects
  the consensus keeper.

The two backends hold different journals. Changing the URL of a node that
serves existing databases does not move their journals: the databases'
streams do not exist on the consensus keepers. **Neither Logkeeper nor RTDB
has an in-place journal migration.** So the cutover runs a second Multi cell
on the consensus keepers, moves databases into it, and keeps the old keepers
and their journals untouched until the switch is qualified. Rollback means
going back to the old cell.

## Phase 0: qualify the consensus keepers (no production traffic)

1. Bring up the keepers ([first bring-up](../deployment.md#first-bring-up)),
   with `catalog_voters` and at least six keepers if you want automatic
   repair.
2. Run the RTDB process qualification against them from an RTDB checkout. It
   covers RTDB commits, a voter killed and restarted, RTDB killed and
   reopened, and every keeper restarted, and it rechecks every acknowledged
   commit:

   ```sh
   python3 rust/bench/v1_consensus_keepers.py --rtdb target/release/rtdb \
     --logkeeper /path/to/logkeeper OUTPUT_DIR
   ```

   It runs in dev mode on loopback keepers, which it starts itself. Run it
   with the exact Logkeeper and RTDB builds you will deploy. The pin rule
   applies: RTDB pins only Logkeeper SHAs on `main`.
3. In staging, on the production topology, run the [rolling
   upgrade](rolling-upgrade.md), [replace a failed disk](replace-disk.md) and
   [lose two voters](lose-two-voters.md) procedures under load.

**Gate:** every phase passes, with zero lost acknowledged commits.

## Phase 1: a new cell on consensus keepers

1. Deploy a second set of RTDB Multi nodes with
   `RTDB_JOURNAL_URL=logkeeper-consensus:///etc/rtdb/journal.json` and
   `RTDB_JOURNAL_{slot}_*` credentials for `urn:logkeeper:client:rtdb`. Give
   it its own `RTDB_KEY_DIRECTORY` and node set, and the same object-store
   bucket layout (`RTDB_BUCKET`).
2. Create **new** databases in the new cell only. Existing databases stay on
   the old cell.
3. Soak with production-like traffic for an agreed period (for example a
   week). Watch `/problems`, refusals and WAL round latency on the keepers,
   and RTDB's commit latency and `rtdb/journal-*` faults.

**Abort** on any lost acknowledged commit, any `rtdb/journal-shortened`, or a
stream stuck `leaderless`. Rollback: stop creating databases in the new cell.
Moving the databases already created there back to the old cell is the
Phase 2 procedure in reverse.

## Phase 2: move existing databases

Run only after qualifying an application export and import that work across
independent RTDB Multi cells. A managed `rtdb admin export NAME BASIS_HEX
PIN_UUID` returns a ticket whose restore can require the original source
deployment, catalog, and checkpoint custody. Copying that ticket alone to
the new cell is insufficient. Rehearse the chosen transfer on a copy of
each database class. The destination must create fresh journal streams
with fresh identities. Per database:

1. Quiesce writes to the database in the old cell, then take its final
   checkpoint, so the old journal suffix after it is empty.
2. Import into the new cell from the qualified application artifacts. Verify
   data, transaction IDs and receipt semantics against the closed source cut.
3. Switch the database's clients to the new cell.
4. **Keep the old database and its journal** on the old stream keepers,
   read-only, until Phase 3. Do not delete or trim them.

**Abort** a move if verification fails. The old database is untouched, so
switch its clients back.

## Phase 3: qualify the switch, then retire the old keepers

Wait until every database has run on the new cell for the agreed soak, with
no journal faults. Then:

1. Delete the old databases in the old cell. This also deletes their journal
   streams on the stream keeper.
2. Stop the old RTDB cell.
3. Stop and decommission the old stream keepers.

**Rollback plan, at any point before Phase 3 step 1:**
- Point clients back at the old cell, whose databases and journals were never
  modified after their final checkpoint.
- Any writes accepted by the new cell since the move must be carried back by
  the reverse move (export from the new cell, restore into the old one), or
  accepted as lost.

So keep the soak short per database, and move databases in small batches.

## What is missing

- In-place migration of a database journal between backends.
- A qualified cold backup and restore for managed RTDB Multi across separate
  catalogs. Treat this as a release gate for existing databases.
