# Typed recovery entry follow-ups (lk-marker-followups)

## Landed on Logkeeper main

| SHA | Task |
|---|---|
| 47105230 | 4. Rolling-upgrade test: look for LKRWAL06 after finalizing |
| 9c8e52fe | 1. A stream at its quota still takes the recovery entry |
| 3911ee18 | 2. Entry decision in decisions.rs with Verus laws and controls |
| 52cb25fe | 3. `keeper inspect` shows the recorded recovery |

### 4. `rolling_restart_one_at_a_time_under_load`
Reproduced on clean main: `a finalized keeper wrote an N checkpoint: Elapsed`. The upgrade itself
worked: all four keepers restarted under load, every acked record read back, finalize succeeded.
The cause was the test's expectation. Since 07635deb (commit index in the WAL), a cluster finalized
at level >= 6 writes LKRWAL06 checkpoints, never LKRWAL05, and the test waited for LKRWAL05.
This is **not an upgrade incompatibility**. Now the test waits for LKRWAL06, and N-1 still refuses
that media with a message. All 5 `upgrade_compatibility` tests pass.

### 1. Quota exemption
`write_recovery_entry` appends within a fixed headroom: `RECOVERY_HEADROOM_BYTES` = 64 KiB and
`RECOVERY_HEADROOM_RECORDS` = 16, past the quota and past `MAX_RETAINED_RECORDS`. Only the
recovery entry uses this headroom, and there is one entry per recovery because the recorded fence
clears when the entry is written. `MAX_RECORD` still applies. Ordinary appends, batches, timed
records and the opaque marker used below level 10 all keep the plain limits.

The over-quota state stays valid everywhere:
- `restore_records`
- the LKRIDX and legacy image readers (`MAX_RETAINED_WITH_HEADROOM`; `MAX_PAGES` is now +2)
- the ingress snapshot transfer bound

This amends the unreleased level 10 in place. A keeper built from 356963d5 up to 9c8e52fe still
refuses the entry on a full stream, so the two builds would diverge only on that edge.

Test: `a_stream_at_its_quota_still_clears_its_recovery_fence`.
- Setup: the stream is filled to its quota, then recovered and acknowledged with a marker.
- The retry returns the same LSN.
- The next ordinary append is `Full`.
- The stream survives a snapshot and a restart while over quota.
- After a trim, appends work again.
- Without the fix, the test fails with `Full`.

### 2. Verus
New pure functions in `decisions.rs`, all called from production:
- `recovery_entry_step`: Write, Retry, Trimmed or Conflict.
- `retained_kind`: only `Command::RecoveryEntry` produces the Recovery kind. Every place in
  `state.rs` that sets a kind goes through it.
- `client_may_seal_as`: used by the ingress seal guard and by `SealSession`.
- `retains_record`: the quota and record check, with the headroom applying only to the entry.

There are 5 laws and 6 negative controls. `run.py consensus_admission`: the baseline verifies 177
functions, and all 98 controls fail exactly as declared. `min_verified_functions` is now 177, and
the area README is updated.

One thing to know: the headroom values are stated in `retains_record`'s ensures, not in `limits()`.
Adding them to `limits()` made the existing `accept-term-regression` control hit an rlimit instead
of its declared failure.

The verify-verus tab (~/code/lk-verify-verus) has uncommitted edits to `decisions.rs`, `area.json`
and `laws.rs`, so it will need a rebase. My code sits after `seal_step`, not at the end of the file,
to reduce conflicts.

### 3. `keeper inspect`
Each stream now has a `recovery` object (JSON) and a `recovery:` line (text) with:
- fence epoch and head, and `entry_at`;
- configuration epoch, loss point and the exact flag;
- source (`survivor` or `object_store`) and time;
- `entry_written`: false while the fence waits; true when the entry is read back from the last
  retained typed entry.

The quota test checks both states on the stopped survivor. README and the lose-two-voters runbook
are updated.

## Test counts (rebased on 09807083 + upstream through 84d76768)
- `cargo test --locked --workspace --quiet`: 246 passed, 0 failed.
- `cargo test --locked --workspace --all-features --quiet`: 472 passed, 2 failed. Both failures
  were already on main and are not mine:
  - `network::versions::tests::every_wire_variant_is_classified_by_the_version_that_introduced_it`
  - `network::versions::tests::requests_reach_only_peers_that_know_them`

  Both fail because `Request::CheckpointCustody` (tag 50, added by Codex in 05c4579e) has no sample
  in `network/versions/tests.rs`. This is Codex's area and is left for them.

## Coordination
Level 11 / bit 1<<13 is already taken on main by Codex (`CLUSTER_VERSION_CHECKPOINT_CUSTODY`),
but the claims table listed 11 as next free. I added it to AGENTS-COORDINATION.md. Next free is now
12 / 1<<14.

## Open
- The versions test fixture for `Request::CheckpointCustody` (Codex).
- Import of a stream that is over quota into a new stream with the same quota is untested.
