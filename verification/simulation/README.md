# Stream journal simulation

Run the test in the Logkeeper worktree with the same seed count as CI.

```sh
LOGKEEPER_SIM_SEEDS=10000 \
  ~/code/codesign-agents/guarded-cargo.py logkeeper test --locked --workspace --all-features -- --show-output
```

The default run exercises seeds 0 through 43. Set `LOGKEEPER_SIM_FIRST_SEED`
and `LOGKEEPER_SIM_SEEDS` to replay a range. The test prints the fault counts
and includes the seed in a failing history or recovery assertion.

Each run has one stream, three original keepers, one optional replacement and
two writer identities plus an observer. Each seed picks a fault profile by
its remainder modulo 11. In order, the profiles cover request loss, reply
loss, duplication, delay, partition, crash before write, loss of an unsynced
write, a torn write, crash after sync, disk loss and replacement, and normal
delivery. Packet delivery and response delays are independently jittered
in every profile. The loss profiles discard packets and the duplication
profile delivers a second copy after the original response. A replacement
run starts with exactly two copies and destroys one of those disks. It
interrupts the sweep after the first survivor installs, checks that this
survivor refuses a stale route, reopens both survivors, and resumes the same
sweep. It checks both repaired copies and the learner before using the new
ensemble. A competing seal runs in a subset of the other schedules.

The writer runs on a current-thread Tokio executor with paused time. The
simulated network hands requests to the keeper's shipped WAL engine. A
pre-sync crash retains a seed-selected byte prefix of the unsynced round or
loses the entire round. The surviving keeper files are then opened by the
shipped replay code. The test inspects both the exact journal history and the
number of physical copies of acknowledged bytes, including coverage of the
published head at the reply. Async socket handling, file metadata crash
points, and arbitrary combinations of faults are outside this bounded run.

Run the controls in the worktree. The runner builds an isolated test executable
and enables one mutation per invocation of the named test.

```sh
python3 verification/simulation/controls.py
```

Each control changes one guard in a test build and requires the named
assertion to fail. Logs are under `verification/simulation/.results/`.
The [keeper I/O controls](../verus/stream_keeper/runtime-controls.py) cover
the shared WAL's group rounds, CRC, checkpoint and deployment authorization.
The [proof link](../link/README.md#stream-journal) and the Verus harnesses
cover the projections and the primitive guards.

## Consensus keeper fault-injection harness

`src/stream/consensus/simulation/` drives seven real in-process OpenRaft 0.10.1
consensus `Engine`s (in distinct failure domains, supporting both single and
replicated `catalog_voters`) through `ConsensusJournal` and `Client`, injecting
seeded faults over the `Network`/`Rpc`, `Disk`, `Space` and `Engine` seams.

### Running

```sh
# Default CI run (6 seeds, large-batch fault test, and autonomous amnesia detector)
cargo test --locked --features stream --lib stream::consensus::simulation -- --nocapture

# Replay and shrink a single seed
LOGKEEPER_CONSENSUS_SEED=1 LOGKEEPER_CONSENSUS_ALLOW_WIPE=1 LOGKEEPER_CONSENSUS_SHRINK=1 \
  cargo test --locked --features stream --lib consensus_fault_harness_replay_seed -- --ignored --nocapture

# Extended soak run
LOGKEEPER_CONSENSUS_FIRST_SEED=0 LOGKEEPER_CONSENSUS_SEEDS=50 \
  cargo test --locked --features stream --lib consensus_fault_harness_soak -- --ignored --nocapture
```

### Faults and operations mixed by seed

- **Operations:** `create`, `seal` (writer handoffs and stale-epoch probes),
  `append`, `append_batch` (small linearizability-checked batches plus a
  dedicated 256/300-record large-batch test crossing snapshot intervals),
  `read` (immediate and long-poll), `head`, `trim`, `delete`, `replace`,
  `prefer_leader`, idle `park` (`park_after_secs = 2`) and wake, offline
  `recover-stream` + `acknowledge_recovery`, and replicated catalog outages.
- **Faults:** symmetric and asymmetric per-lane partitions (`control`,
  `replication`, `bulk`, `application`), probabilistic drops, delays, reply
  drops (creating ambiguous `Unavailable` outcomes), peer duplicates, graceful
  stop/restart, abrupt crash/restart, WAL before/after-sync and torn-frame
  crash cuts (`ReplicaFault` / `interrupt_next`), slow WAL rounds
  (`Disk::set_wal_delay`), disk-full leadership shedding (`Space::set_available`),
  and keeper wipe-and-reinitialize under its old ID (`LOGKEEPER_CONSENSUS_ALLOW_WIPE=1`).

### Checked invariants

1. **Linearizability:** Every non-recovered stream history (and the
   pre-recovery prefix of recovered streams, up to the 63-call bitmask bound of
   `journal_contract::conformance::history::linearizable`) must admit a valid
   sequential linearization under real-time precedence, where `Unavailable`
   mutations may either take effect or not.
2. **Durability:** An acknowledged append never disappears or changes bytes
   unless an operator recovery explicitly acknowledged data loss for that
   stream. Every record returned by `read` or present on disk must match an
   actually proposed payload for that LSN.
3. **Monotonic heads:** Across any strict real-time ordering (`B.invocation >
   A.response`) within the same recovery era, linearizable heads (`head`,
   `seal`, `append`, `append_batch`) never regress.
4. **Writer fencing:** No `append`, `append_batch` or `trim` invoked after a
   completed `seal(E)` by owner `O` may succeed under a lower epoch or under
   epoch `E` by a different principal. After an operator recovery, no
   pre-recovery epoch may ever be accepted, and ordinary seals are refused with
   `Recovered` until `acknowledge_recovery` clears the recovery fence.
5. **Ambiguous batch atomicity:** A single keeper batch (`<= 256` records,
   `<= 4 MiB`) that returned `Unavailable` must either commit atomically in
   full or not at all; multi-chunk `ConsensusJournal::append_batch` calls may
   commit only a whole-batch prefix.
6. **Delete permanence:** Once `delete` returns `Ok(())`, no later non-delete
   operation on that stream may succeed.
7. **Cross-voter convergence:** After all faults heal and stopped keepers
   restart, all three voters of each stream's finalized configuration must be
   healthy and converge to identical `(deleted, floor, head, records)` state
   directly in their `StateMachine`s.
