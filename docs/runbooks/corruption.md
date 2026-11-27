# Corruption

The keeper detects damage at three levels:

| Damage | What the keeper does | Where you see it |
| --- | --- | --- |
| One stream's snapshot, index pages or extents | Quarantines that replica: it keeps protecting the stream's objects and stops serving it | Log line `logkeeper quarantined stream ...`; `/ready` `quarantined_streams`; `/problems` `quarantined`; `logkeeper_consensus_streams{state="quarantined"}` **[ops]** |
| WAL frames, segments, the boundary or the keeper identity | Refuses to start ("missing or foreign installed keeper media", a boundary or chain mismatch), or the WAL thread fails and `/live` turns 503 | `journalctl -u $UNIT`; `/live` |
| A stalled disk (WAL round over 20 s) | The watchdog ends the process | Exit in `journalctl`; systemd stops restarting after 5 failures in 10 minutes |

On `main`, snapshot quarantine survives restarts. With **[upgrades]**, every
checksum failure quarantines durably in `<registry>/<uuid>.quarantine.json`
and returns a typed `Corrupted` error. The replica then reports itself
unhealthy, so its stream's leader replaces it after `repair_after_secs`.

**First rule:** a corrupted replica is not needed while its stream's other two
voters are healthy. Check that before doing anything else. If they are not
healthy, protect the survivor's copy and go to [lose two
voters](lose-two-voters.md) only as a last resort.

## 1. Stop and verify (offline) [ops]

```sh
sudo systemctl stop $UNIT
lk keeper verify --config $CONFIG; echo "exit=$?"
```

The output covers:
- both boundary slots;
- the checkpoint digest and its references;
- every segment header and frame CRC;
- record decoding;
- the running SHA-256 chain against the checkpoint and the trusted boundary.

A torn but unpublished tail after a crash is reported separately and does
not fail. `exit=0` means the media is intact, so restart the keeper. A failure
prints `keeper media verification failed`, plus the failing segment, frame or
slot. Keep the full output with the incident. For detail, run:

```sh
lk keeper inspect --config $CONFIG --stream STREAM_UUID --json   # one stream's vote, log range, fence, quarantine reason
lk keeper dump-segment --config $CONFIG --segment ID --limit 50  # frame offsets, lengths, CRC status
```

These tools are read-only and take the media lock, so they refuse while the
keeper runs.

## 2a. One stream quarantined, media otherwise intact

Choose one of the following:

- **Let repair replace it** (preferred). Leave the keeper running. With
  **[upgrades]**, the quarantined replica reports unhealthy, and the leader
  replaces it with a voter on another keeper after `repair_after_secs`. That
  needs a free domain with an accepting keeper, so six keepers or more. Then
  clear the marker, so the keeper stops protecting the old copy's objects:

  ```sh
  sudo systemctl stop $UNIT
  lk keeper clear-quarantine --config $CONFIG --stream STREAM_UUID
  # cleared quarantine marker for stream <id>
  sudo systemctl start $UNIT
  ```

  The removed copy then retires itself.
- **Restore the snapshot bytes** if you hold the exact file that the WAL's
  digest names (rare: the keeper has no backup tool):

  ```sh
  lk keeper repair-snapshot --config $CONFIG --stream STREAM_UUID --snapshot BACKUP_FILE
  ```

**Never clear a quarantine on a replica that is still a voter**, unless you
have repaired its data. Clearing only removes the marker. It does not fix
bytes.

## 2b. Damaged WAL span: salvage [upgrades]

```sh
lk keeper salvage --config $CONFIG
# salvaged=true damaged_segments=1 quarantined=3 preserved=118
sudo systemctl start $UNIT
```

`salvaged=false` means it found no damage and left the media untouched.
Salvage walks past damaged segments and durably quarantines every stream
with slices in them. It writes a fresh checkpoint and boundary so that the
intact streams boot and serve. Then follow 2a for each quarantined stream.

**Abort, and treat the keeper as a lost disk ([replace a failed
disk](replace-disk.md)),** if any of these holds:
- `salvage` fails;
- `preserved` is 0;
- the boundary or the identity is damaged;
- the device reports I/O errors (`dmesg`, SMART).

Without **[upgrades]**: there is no salvage. A keeper whose WAL fails
verification cannot boot. Replace it as a lost disk with a new UUID.

## 3. After any corruption

- Check the device: `smartctl -a`, `dmesg`, and the filesystem.
- If the disk is suspect, replace the keeper even if salvage worked.
- Record the `verify` output, `inspect` for each affected stream, and the
  keeper log.
