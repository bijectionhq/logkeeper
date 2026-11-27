# Lose two of three voters

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

On the surviving keeper **[ops]**:

```sh
probe problems | jq -r '.problems[] | select(.reasons | index("leaderless")) | .stream'
```

Without **[ops]**, use `ConsensusJournal::configuration` and `keeper_status`
for each stream RTDB reports as unavailable (RTDB returns `Unavailable` on
seal and append).

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
make this keeper's copy of stream <id> (head <n>) the only history: records
only <lost-1> and <lost-2> held are lost. The voters would become [...] at
revision <r>, term <t>, ...`.

**Abort** on any other refusal:

| Message | Meaning |
| --- | --- |
| `refused: N other voter(s) ... answer with a healthy replica` | The stream still has a quorum. Restart this keeper instead |
| `this keeper is not a voter of the stream's latest configuration` | Run it on the right survivor |
| `the replicated catalog cannot be recovered this way` | Catalog recovery does not exist |
| `replacements must be two live, accepting keepers ...` | Add keepers, or name them with `--with` |
| `the selected snapshot is ahead of the log; start and stop this keeper first` | Do exactly that, then retry |

A joint configuration is also refused. That case does not exist as a
recovery path yet (review item 14).

## 4. Recover

```sh
lk keeper recover-stream --config $CONFIG --stream STREAM_UUID --acknowledge-data-loss \
  [--with KEEPER_UUID,KEEPER_UUID]
```

Expected:

```text
stream <id> recovered from this keeper at head <n>: voters <a> <b> <c>, revision <r>, term <t>,
recovery fence at epoch <e>. Lost voters <x> and <y> must retire their copies before they rejoin.
Start this keeper, then acknowledge the recovery so writers can seal again.
```

A second run prints `was already recovered`. Repeat for each affected stream
(batch recovery does not exist yet), then start the keeper:

```sh
sudo systemctl start $UNIT
until probe ready | grep -qx 200; do sleep 5; done
```

## 5. Acknowledge and resume RTDB

The stream is sealed under a recovery fence. Every `seal` returns
`JournalError::Recovered { head }`, which RTDB reports as the fault
`rtdb/journal-recovered`. At its current pin, RTDB does not acknowledge by
itself. A writer or administrator principal calls:

```rust,ignore
let head = journal.acknowledge_recovery(stream).await?;   // ConsensusJournal
```

RTDB's writer then seals above the fence. It reports
`rtdb/journal-shortened` with the lost range if the head is below what it had
acknowledged. Record the stream, the head and the lost range with the
incident.

## 6. The lost keepers

If a lost keeper returns with its data, its copies retire on the first
contact with a recovered voter. **Start lost keepers one at a time**, or wipe
them and replace them as new keepers. If both return together, they can form
a quorum of the old configuration until one of them contacts a recovered
voter, and a client holding a cached route could read the lost history in
that window. Durable fencing of lost keepers (review item 13) is not built
yet.
