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
