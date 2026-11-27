# Lose two of three voters (or three of five)

This runbook is written for three-voter streams. A five-voter stream
follows the same steps once it loses three or more voters; the differences
are in [five-voter streams](#five-voter-streams) at the end.

This procedure applies to legacy mutable streams.
For an immutable stream, restore its original quorum or install a verified application cut under a fresh stream ID.
If the application exposes a stable name, publish the successor only after it has fenced the previous incarnation at every serving endpoint.

A stream needs two voters to commit and to change membership. After it loses
two, leader-driven repair holds, and only an operator can make the survivor's
copy the stream's only history. **This can lose acknowledged records:** a
committed record reached two voters, which may have been the two you lost. If
either lost keeper can come back with its data, bring it back instead and
stop here.

`recover-stream` needs two live, accepting keepers outside the stream's lost
configuration, in domains distinct from each other and from the survivor's,
to become the new voters. A 3-keeper cluster has none. Add keepers first (see
[add a keeper](add-drain-remove-keeper.md#add-a-keeper)), or wait for a lost
keeper to return.

## 1. Identify the streams and the survivor

On the surviving keeper:

```sh
probe problems | jq -r '.problems[] | select(.reasons | index("leaderless")) | .stream'
```

Then, for each such stream, `lk admin status --config operator.json --stream
UUID` shows its configuration and which voters answer. Run it also for each
stream RTDB reports as unavailable (RTDB returns `Unavailable` on seal and
append).

Inventory every stream on the two lost keepers before retiring either
identity. Retirement is permanent and applies to all streams, including the
catalog if the keeper stores a catalog replica. Prefer restoring the existing
quorum while that is possible. Use the current Logkeeper operator binary
throughout this procedure. Older operator binaries predate retirement proofs.

**Check whether the cluster enforces liveness leases.** Each keeper's
`/metrics` shows it (`logkeeper_consensus_lease_enforced 1`). Once the
cluster has finalized leases (cluster level 6), a lost keeper that still
runs, cut off from the survivor and the catalog, is deposed by time:
`recover-stream` commits the recovery in the catalog, which fences the
stream for both lost keepers, and waits out their leases before the
recovered configuration serves. Retiring the lost identities (step 4) and
naming them then become optional; nothing in this runbook needs a lost host.
Each lost keeper must have held a lease (`logkeeper_consensus_lease_epoch`
above 0 on it before the loss); the command refuses until you name with
`--lost` any that never did, which is your statement that it is down.

**Check that the cluster finalized level 6 before you trust the loss
point.** At level 6 every keeper writes each stream's commit index to its
WAL, and the recovery keeps exactly the survivor's committed prefix. It
drops any record the survivor wrote as leader but never knew committed. The
lost keepers may have committed and acknowledged other records at those
LSNs. The loss point it prints is then exact: every record at or below it is
the one the stream committed. Below level 6 the recovery keeps the
survivor's whole log, and the loss point is only its last snapshot. Records
above that may differ from what writers were acknowledged. Finalizing after
the loss does not help: the survivor learned its commits before the loss,
so finalize level 6 as part of every upgrade. A keeper notes its commit
index without an fsync of its own and writes it within about 500 ms, so a
survivor that crashed may count those last commits in the loss.

## 2. Stop the survivor

`recover-stream` runs on the stopped keeper, under its media lock. Stopping
the keeper also stops every other stream it hosts, and those lose one voter
for the duration. Check first, on the other keepers, that no other stream
would drop below two live voters.

```sh
sudo systemctl stop $UNIT
```

## 3. Dry run

```sh
lk keeper recover-stream --config $CONFIG --stream STREAM_UUID
```

Expected: exit 1 with `refused without --acknowledge-data-loss. This would
make this keeper's copy of stream <id> through head <n> the only history:
records only <lost-1> and <lost-2> held are lost, and writers lose every
record they were acknowledged above <loss point>. The voters would become [...] at
revision <r>, term <t>, ... To proceed, permanently retire both lost keepers
and add --acknowledge-data-loss --lost <lost-1>,<lost-2> and a --fence-proof
for each`. With leases enforced the message instead says the catalog
fences the stream for both and that `--lost` and the proofs are optional.

**Abort** on any other refusal:

| Message | Meaning |
| --- | --- |
| `refused: N other voter(s) ... answer with a healthy replica` | The stream still has a quorum, possibly through a slow keeper you took for lost. Restart this keeper instead |
| `refused: name both lost voters with --lost x,y` | `--lost` is missing or names other keepers |
| `refused: supply two independently signed keeper retirement proofs` | Generate one proof on each lost keeper's original enrolled media |
| `immutable histories require their original quorum or a successor with a fresh stream ID` | Restore the original quorum or create a successor with a verified application cut |
| `refused: the cluster has not finalized liveness leases ... name them with --lost x,y` | Leases are advisory: fence both lost keepers, then name them |
| `refused: [...] never held a liveness lease ...` | Time cannot depose those keepers: confirm each is down or fenced, then name it with `--lost` and run again |
| `refused: --lost may name only the lost voters ...` | `--lost` names another keeper |
| `this keeper is not a voter of the stream's latest configuration` | Run it on the right survivor |
| `the replicated catalog requires its original quorum or disaster restore` | Follow [catalog and joint quorum loss](#catalog-and-joint-quorum-loss) |
| `the catalog records a pending move or a different source configuration` | Reconcile against the current membership with its original quorum. The local survivor may have missed a configuration change |
| `replacements must be two live, accepting keepers ...` | Add keepers, or name them with `--with` |
| `the selected snapshot is ahead of the log; start and stop this keeper first` | Do exactly that, then retry |
| `refused: this keeper never recorded that the stream committed an entry ...` | Leases are finalized but this survivor never wrote a commit of the stream, so it would keep nothing. With two survivors, recover from the other one. Otherwise restore from the object store (`docs/runbooks/offload.md`) |

For a joint configuration, follow [catalog and joint quorum loss](#catalog-and-joint-quorum-loss).

## 4. Retire the lost keeper identities and recover

Confirm each lost keeper's UUID and check that retiring the pair leaves the
latest catalog configuration with quorum. On each lost keeper's original
host, or with exclusive control of its original media and trusted registry,
stop the service and use that keeper's configuration and credentials:

```sh
sudo systemctl stop "$UNIT"
lk keeper fence-recovery --config "$CONFIG" \
  --acknowledge-keeper-retirement LOST_UUID > LOST_UUID.fence.json
```

The command takes the same exclusive media lock as the service and durably
retires the enrollment before returning the signed proof. Repeat the command
if output was interrupted. Transfer both proof files to the survivor. They
contain public certificates and signatures. The survivor checks each proof's
certificate against the cluster CA and matches its keeper UUID, catalog UUID,
and recorded media incarnation. The certificates must still be valid.

If either original enrollment cannot be locked or attested, including after
permanent loss of its media or key, this workflow stops. An unreachable
host, stopped service, or powered-off VM alone supplies insufficient evidence.
Leave the affected streams offline until you can restore their original
quorums or rebuild under a fresh, isolated cluster identity.

```sh
lk keeper recover-stream --config $CONFIG --stream STREAM_UUID --acknowledge-data-loss \
  --lost LOST1_UUID,LOST2_UUID --fence-proof LOST1_UUID.fence.json \
  --fence-proof LOST2_UUID.fence.json [--with KEEPER_UUID,KEEPER_UUID]
```

With leases enforced, the retirement above is optional defence in depth,
and so is `--lost`:

```sh
lk keeper recover-stream --config $CONFIG --stream STREAM_UUID --acknowledge-data-loss \
  [--lost LOST_UUID[,LOST_UUID]] [--with KEEPER_UUID,KEEPER_UUID]
```

`--lost` then declares the named keepers dead, which bumps their epochs and
ends their leases for every stream they host. Without it the catalog still
fences this stream for both lost keepers. The command waits a lease plus the
drift margin (33 s by default) after the catalog commits, before it writes.

With leases enforced, `--lost` is optional: it declares the named keepers
dead, which bumps their epochs and ends their leases for every stream they
host, not just this one. Without it the catalog still fences this stream for
both lost keepers. Use it when you know a lost keeper's media is gone or
untrustworthy. Without leases, name both (step 1).

The command commits the recovery in the catalog, then waits a lease plus
the drift margin (33 s by default) before it writes, so the recovered
configuration cannot serve while a lost keeper's lease lasts.

Expected:

```text
stream <id> recovered from this keeper at head <n>: voters <a> <b> <c>, revision <r>, term <t>,
recovery fence at epoch <e>. Lost voters <x> and <y> must retire their copies or stay retired;
the catalog fences the stream for 2 keeper(s), and this command waited 33000 ms for their leases
to end. Start this keeper, then acknowledge the recovery so writers can seal again. Loss point:
record <n>; acknowledged records above it are lost.
```

Record the loss point in the incident. At level 6 the head is the loss
point. Below level 6 the report ends instead with `Loss point: record <s>,
the last point this keeper knows committed: ... may have been overwritten by
the lost voters ...`. Here `<s>` is the survivor's last snapshot, and the
records between `<s>` and the head are unverified. With offload the report
also prints the store's part. When the store holds a longer committed run,
it replaces the survivor's copy.

A second run prints `was already recovered`. Repeat for each affected stream
(batch recovery does not exist yet), then start the keeper:

```sh
sudo systemctl start $UNIT
until probe ready | grep -qx 200; do sleep 5; done
```

## 5. Acknowledge and resume RTDB

The stream is sealed under a recovery fence. Every `seal` returns
`JournalError::Recovered { head }`, which RTDB reports as the fault
`rtdb/journal-recovered`. The RTDB build with atomic recovery markers and
finalized keeper cluster version 3 commits its marker at the next LSN
together with clearing the fence. Keep writers held during a mixed RTDB
rollout. A legacy RTDB writer can clear the fence without that marker.

At finalized cluster version 10 the recovery records the catalog's record
in the stream, and clearing its fence writes one typed recovery entry at
`head + 1`: the epoch, the loss point, the source (survivor or object
store), the time, and RTDB's marker inside it. Both RTDB's acknowledgement
and the administrator's below write it, so the stream always records the
recovery, and no client append can forge it. `head` stays the last record
kept.

With `multiJournal.holdWritesAfterRecovery: true`, an operator can
explicitly clear the fence with an administrator principal. Record that
decision in the incident, since this path bypasses the RTDB marker:

```sh
lk admin acknowledge-recovery --config operator.json --stream UUID
# stream: UUID
# head: 1234
```

From a program, `ConsensusJournal::acknowledge_recovery(stream)` does the same.

Automatic recovery leaves the fence intact if it cannot write its marker,
including when the surviving checkpoint requires an immediate key-rotation
record or the stream has no capacity for the marker. Diagnose the blocked
case before exercising the operator override.

RTDB's writer then seals above the fence. It reports
`rtdb/journal-shortened` with the lost range if the head is below what it had
acknowledged. Record the stream, the head and the lost range with the
incident.

## 6. Replace the retired keepers

Keep the retirement marker in the trusted registry. The safety of the proof
depends on exclusive ownership of the enrolled identity and a registry that
never rolls back. Discard any copied credentials for those identities. To
add capacity, use freshly provisioned keeper UUIDs and keys, then update
inventory as described in [add and remove a keeper](add-drain-remove-keeper.md).

## Lost keepers that never stopped

A lost keeper that never stopped, cut off from the survivor but still
holding a quorum of the old configuration with the other lost keeper, is
deposed by its lease once the cluster enforces leases: it cannot renew while
cut off from the catalog, and if it reaches the catalog it learns that the
stream is fenced for it. Either way it stops leading and serving before the
recovered configuration serves; the recovery's wait guarantees that order.
When it reconnects it retires its copy. Without enforced leases only its
retirement (step 4) closes that gap. A keeper on new media under its old ID
gets a new epoch from the catalog and takes copies only through staging.

## Catalog and joint quorum loss

The catalog is the placement authority for every stream. If it loses quorum,
freeze destructive recovery and catalog changes. Identify its latest
catalog membership from the available keepers' local inspection reports,
including any joint voter sets, and bring enough original participants back
on their intact, enrolled media. A replica with a damaged snapshot may use
`keeper repair-snapshot` with the exact snapshot named by its intact WAL.
Once a catalog quorum is serving, check catalog-backed status against the
expected recoverable streams before continuing.

For a stream in a joint configuration, use `keeper inspect --config FILE
--stream UUID --json` on stopped original voters to identify both sets.
Restore intact original participants sufficient for a majority of each set,
restart them, and allow Raft to finalize membership. Check the resulting
uniform configuration before planning further repairs. A single surviving
WAL cannot establish which joint transition an unavailable quorum committed.

If either required quorum is irretrievable, preserve the original media and
registries. Rebuild from application-level backups using a separate catalog,
fresh keeper identities, credentials and enrollment, and isolated endpoints.
Validate the restored application state and cut clients over only after the
old cluster is fenced from clients and writers. Record the unavailable
suffix against the latest application checkpoint or export.

## Five-voter streams

A five-voter stream keeps writing after losing two voters, so nothing here
applies until it loses a third. Repair replaces lost voters one at a time
while three are live. After three or four are lost:

- **Survivors.** With one survivor, run the steps above on it. With two,
  run `recover-stream` on the survivor that **knows the later commit**,
  then the one whose last log entry is later, then the lower keeper ID.
  Stop only that one. Keep the other running so the command can ask it for
  both. On the other survivor the command refuses with `refused: surviving
  voter <x> knows the later commit or holds the more advanced log ...; stop
  it and recover from it instead`: restart it, stop `<x>` and run there.
  The other survivor keeps its seat in the recovered configuration and
  catches up. Whatever it holds past the recovered history is replaced, and
  it never knew any of that committed.
- **`--lost`** names every voter that answers with no healthy replica:
  three with two survivors, four with one, each retired with
  `keeper fence-recovery` and passed with its own `--fence-proof`.
- **Replacements.** One per lost voter, outside the lost configuration,
  spread with the survivors (free domains first, at most two voters per
  domain). Without `--with` the command chooses them; it refuses when too
  few live, accepting keepers exist, so keep at least three or four spare
  keepers in the cluster beyond each stream's five voters.
- **Refusal** `refused: N other voter(s) ... answer with a healthy replica`
  appears when two other voters are healthy: with the survivor they form a
  quorum of five, so restart this keeper instead.
