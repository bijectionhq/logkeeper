# TLA+ Protocol Model for Logkeeper Consensus Additions

This directory contains finite-state TLA+ specifications of Logkeeper's protocol
additions on top of OpenRaft 0.10.1 (`src/stream/consensus/`) and a runner script
that downloads a pinned TLC (`tla2tools.jar` v1.7.4, SHA-256 verified) and checks
all safety and liveness configurations exhaustively.

## Modules

### `LogkeeperProtocol.tla`

Models one consensus stream hosted on `Keepers` (3–5 keepers) running OpenRaft
0.10.1 plus Logkeeper's keeper-layer protocol additions:

- **Raft core (OpenRaft 0.10.1):** terms, standard Raft votes with OpenRaft's
  `committed` bit (`Vote { term, votedFor, committed }`), restart self-vote
  demotion (`decisions::demotes_vote` in `decisions.rs` / `storage/mod.rs`),
  pre-vote (`enable_pre_vote`), leader leases, quorum-loss step-down, log
  matching, local snapshots (`snapIdx`), and joint consensus membership changes.
- **Parking & unparking (`keeper/park.rs`, `keeper/liveness.rs`, `keeper/ingress.rs`):**
  leader-initiated `Park { vote, last }` skipping dead followers
  (`settled_except(&dead)`), parked followers answering empty heartbeats `Busy`
  and repeated `Park` with `true` while reopening on entries, votes, pre-votes,
  and client requests, and the holder-driven wake sweep (`wake_for_dead`) for
  parked streams naming exactly one dead keeper.
- **Liveness, repair, staged replacement, stale learners, and retirement
  (`keeper/repair.rs`, `keeper/replacement.rs`, `keeper/replicas.rs`, `ownership.rs`):**
  keeper liveness table (`deadView`), `StageOwned`, `StageReplica` with exact
  `Ownership` high-water / generation checks (`ownership.rs:129-148`), aborted
  replacements, stale learner removal (`RemoveNodes`), `InstallReplica`, joint
  and finalized membership transitions, `Change::Observe`, and `retire_removed` /
  `Change::Detach` (preserving the durable vote across detach).
- **Keeper wipe-and-reinitialize (`WipeAndReinit`):** wipes disk state under
  the same keeper ID and allows auto-registration on first peer RPC for genesis
  voters (`keeper.rs:685`), calibrating the model against the confirmed Raft
  amnesia bug (commit `98f32fe`).
- **Operator recovery (`keeper/recovery.rs`, `decisions.rs`, `keeper/replicas.rs`,
  `keeper/ingress.rs`, `client/reading.rs`):** offline `recover-stream` on a
  stopped survivor (`decisions::allows_recovery`), `StageRecovered`
  (`Change::Recover`), atomic `Record::Recover` at `T' = max + RecoveryGap`,
  `decisions::votes(..., recovering)`, recovery fence & `AcknowledgeRecovery`,
  `decisions::excludes_sender`, returning 1 or 2 lost voters, and client `ReadAt`
  observations (`serves_applied_pages`).

### `CatalogStream.tla`

Models the replicated catalog stream (`keeper/catalog_stream.rs`) on 3 catalog
voters:

- Raft leader election, log replication, commit, and voter stop/restart with
  vote demotion.
- Migration seeding from the legacy single-keeper catalog (`Checkpoint(legacy)`
  + `Seeded` marker; claims are refused before `Seeded`).
- First-claim-wins `Claim(stream, genesis)` at `head + 1` under the fixed
  internal fence, with read barrier, fold catch-up, conflict handling, and
  competing claims across leadership changes.
- Compaction (`Checkpoint` followed, only if uncommitted-conflict-free, by
  `Trim(through: at - 1)`) and replica fold reconstruction from the trim floor.

## Configurations and Bounds

| Config | Module | Keepers / Bounds | Properties | Expected |
| --- | --- | --- | --- | --- |
| `RaftParkSafety.cfg` | `LogkeeperProtocol` | 3 keepers, `MaxTerm=2`, `MaxLogLen=3`, `MaxAppends=1`, `AllowPark=TRUE`, `AllowStop=TRUE` | `ElectionSafety`, `CommittedEntriesPreserved`, `RetiredNeverVotes`, `LogMatching` | PASS |
| `RepairReplaceSafety.cfg` | `LogkeeperProtocol` | 4 keepers, `MaxTerm=1`, `MaxLogLen=6`, `AllowReplace/Retire/AbortedReplace/StaleLearner=TRUE` | `ElectionSafety`, `CommittedEntriesPreserved`, `RetiredNeverVotes`, `LogMatching` | PASS |
| `CatalogSafety.cfg` | `CatalogStream` | 3 voters, 2 streams (1 legacy), 2 geneses, `MaxTerm=2`, `MaxLogLen=6`, `MaxClaims=2`, `MaxCompacts=1` | `AtMostOneGenesisPerStream`, `ElectionSafety`, `LegacyEntryPreserved`, `CompactionPreservesFold` | PASS |
| `ParkedRepairLiveness.cfg` | `LogkeeperProtocol` | 4 keepers (`InitParkedDead`), `MaxTerm=2`, `MaxLogLen=7` | `ElectionSafety`, `RetiredNeverVotes`, `ParkedDeadVoterEventuallyRepaired` | PASS |
| `RecoverySingleReturnNoSnap.cfg` | `LogkeeperProtocol` | 5 keepers (`InitPreRecovery`), `MaxReturningLost=1`, `AllowSnapshot=FALSE` | `Safety` (incl. `NoMixedHistory`) | PASS |
| `RecoverySingleReturnLiveness.cfg` | `LogkeeperProtocol` | 5 keepers (`InitPostRecovery`), `MaxReturningLost=1` | `LostVotersEventuallyRetire` | PASS |
| `AmnesiaWipe.cfg` | `LogkeeperProtocol` | 3 keepers, `MaxTerm=2`, `MaxLogLen=4`, `AllowWipe=TRUE` | `CommittedEntriesPreserved` | CE (calibration, commit `98f32fe`) |
| `AbortedReplaceLiveness.cfg` | `LogkeeperProtocol` | 4 keepers (`InitAbortedReplace`), `MaxTerm=2`, `MaxLogLen=5` | `ParkedDeadVoterEventuallyRepaired` | CE (`Ownership::high` repair deadlock) |
| `RecoverySingleReturnSnap.cfg` | `LogkeeperProtocol` | 5 keepers (`InitPreRecovery`), `MaxReturningLost=1`, `AllowSnapshot=TRUE` | `Safety` (`NoMixedHistory`) | CE (snapshotted lost voter serves lost suffix) |
| `RecoveryBothReturn.cfg` | `LogkeeperProtocol` | 5 keepers (`InitPreRecovery`), `MaxReturningLost=2`, `AllowSnapshot=FALSE` | `NoMixedHistory` | CE (returning pair forms old quorum) |
| `RecoveryBothReturnLiveness.cfg` | `LogkeeperProtocol` | 5 keepers (`InitPostRecovery`), `MaxReturningLost=2`, survivor down | `LostVotersEventuallyRetire` | CE (permanent split-brain quorum) |

## Abstraction Gaps Relative to the Rust Code

1. **Direct RPCs instead of an unbounded message bag:** Elections (`StartCampaign`,
   `HandleVote`, `BecomeLeader`) and replication (`ReplicateOrHeartbeat`) model
   asynchronous interleavings, partial quorums, stale leaders, and crashes without
   keeping all historical RPCs in a bag. Arbitrary reordered/duplicated stale
   `AppendEntries` from two terms ago are abstracted out (guarded by Raft vote
   monotonicity).
2. **Inline commit application:** `AdvanceCommit` and `ReplicateOrHeartbeat`
   advance `appliedIdx` to `commitIdx` in the same step. Persistent snapshots
   (`snapIdx`) remain independent via `TakeSnapshot`, capturing the exact
   difference between volatile `appliedIdx` and persisted snapshots across
   restarts.
3. **Coarse-grained timers and liveness:** Real timeouts (`repair_after_secs`,
   `park_after_secs`, `STALE_LEARNER`, `quorum_loss_probe_interval`, exponential
   backoff, `LEADER_HOLD_DOWN`) are abstracted to non-deterministic boolean events
   (`DetectDead`, `HeardTimeout`, `ExpireLease`, `ParkStream`).
4. **Reachable scenario prefixes for liveness and recovery:** `InitParkedDead`,
   `InitAbortedReplace`, `InitPreRecovery`, and `InitPostRecovery` start from
   short, reachable cuts of the full state graph so TLC checks temporal properties
   and 5-keeper recovery exhaustively in seconds.
5. **Unmodeled subsystems:** Multiplexed framing and ingress admission budgets
   (already checked locally in Verus `verification/verus/consensus_admission`),
   WAL segment compaction and crash cuts within a single WAL round, disk-full
   leadership shedding (`E5`), preferred-domain leadership handoff (`F2`),
   multi-part catalog checkpoints (`parts > 1`), timed originals, and
   `max_streams` eviction / unopened-stream `genesis.voters` sweep.

## How to Run

Requires Java 17+ (`JAVA_BIN` or `java` on `PATH`; `check.sh` also checks
standard `mise` / Homebrew / macOS JDK locations).

```sh
# Run the full suite (~2.5 minutes total):
./verification/tla/check.sh

# Run the fast subset (skips the 3 longest configs; ~25 seconds):
./verification/tla/check.sh fast
```

Logs are written to `verification/tla/.results/` (gitignored). `fetch-tla.sh`
downloads `tla2tools.jar` v1.7.4 into `verification/tla/.tools/` (gitignored) and
verifies its SHA-256 digest before every run.
