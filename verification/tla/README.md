# TLA+ model of the consensus keeper's protocol additions

Two finite-state TLA+ specifications cover what Logkeeper adds on top of
OpenRaft 0.10.1 in `src/stream/consensus/`. `check.sh` checks every
configuration with a pinned TLC and exits non-zero when any outcome differs
from the one it expects, so CI can call it.

```sh
./verification/tla/check.sh        # every configuration
./verification/tla/check.sh fast   # skips the five deep safety configurations
TLC_WORKERS=4 ./verification/tla/check.sh   # bound TLC's worker threads
```

`check.sh` needs Java 17 or later (`JAVA_BIN`, `java` on `PATH`, or the
usual mise, Homebrew and macOS JDK locations). `fetch-tla.sh` downloads
`tla2tools.jar` v1.7.4 into `.tools/` and checks its SHA-256 before every
run; the jar is never committed. Logs go to `.results/`, and each run's TLC
state lives in a temporary metadata directory that is deleted afterwards, so
no state directory is committed (`.gitignore` covers `.tools/`, `.results/`,
`states/` and jars).

## Modules

### `LogkeeperProtocol.tla`

One stream on three to five keepers:

- **Raft core:** terms and OpenRaft votes with the committed bit, restart
  vote demotion (`decisions::demotes_vote`), pre-vote, leader leases,
  quorum-loss step-down, log matching, local snapshots, joint consensus, and
  a candidate or leader adopting a newer term from an answer
  (`LearnHigherTerm`).
- **Parking** (`keeper/park.rs`, `keeper/liveness.rs`, `keeper/ingress.rs`):
  parking past a dead follower, `Busy` heartbeats, reopening, and the wake
  sweep.
- **Repair and replacement** (`keeper/repair.rs`, `keeper/replacement.rs`,
  `keeper/replicas.rs`, `ownership.rs`): the liveness view, `StageOwned`,
  `StageReplica` with the exact ownership high-water and generation rules,
  including `decisions::restages_replacement`, aborted moves, stale
  learners, installation, joint and final configurations, observation, and
  retirement on a certified proof (`Change::Detach` keeps the vote).
- **Media reuse** (`keeper/incarnation.rs`): a keeper wiped and initialized
  again under its ID marks itself reused and never registers a replica from
  peer traffic (6d75fec).
- **Operator recovery** (`keeper/recovery.rs`): `allows_recovery`, recovery
  copies, `Record::Recover` at a term `RecoveryGap` above the survivor's, the
  recovery fence and its acknowledgement, the mandatory catalog stage, sender
  exclusion, and one or two lost voters returning.
- **Placement certification** (`keeper/certify.rs`): which copies may
  campaign or serve reads, the catalog's latest staged move, and fencing by
  `decisions::fences_copy`.
- **Readers** (`ClientRead`): a `ReadAt` from any certified voter of its
  applied membership.

### `CatalogStream.tla`

The replicated catalog (`keeper/catalog_stream.rs`) on three voters: Raft,
seeding from the single-keeper catalog, first-claim-wins claims under the
internal fence, and compaction by checkpoint and trim.

## Properties

| Property | Meaning |
| --- | --- |
| `ElectionSafety` | At most one leader per term. |
| `CommittedEntriesPreserved` | Every leader holds every committed record of an earlier term, except those a recovery acknowledged lost. |
| `LogMatching` | Two logs that agree on an entry's index and term agree on the prefix. |
| `RetiredNeverVotes` | A retired copy never grants a vote. |
| `NoMixedHistory` | After a recovery no reader sees both the lost suffix and post-recovery records, or two values at one LSN. |
| `LostStayBelowRecoveryTerm` | A lost voter's copy never learns a term of the recovered history (Lean `RecoveryFence.lost_replicas_stay_below_the_recovery_term`). |
| `ParkedDeadVoterEventuallyRepaired` | A parked stream with one dead voter and a live spare is repaired. |
| `LostVotersEventuallyRetire` | Returning lost voters retire. |
| `AtMostOneGenesisPerStream` and the catalog invariants | The catalog assigns one genesis per stream and keeps its fold across compaction. |

`Safety` is `ElectionSafety`, `CommittedEntriesPreserved`,
`RetiredNeverVotes`, `NoMixedHistory` and `LostStayBelowRecoveryTerm`.

## Configurations

Every configuration passes on the fixed protocol. The counterexamples below
were found by the first version of the model; each configuration that failed
then passes now, and none is kept as an expected failure.

| Config | Bounds | Checks | Result |
| --- | --- | --- | --- |
| `RaftParkSafety` | 3 keepers, `MaxTerm=2`, parking, a crash | `ElectionSafety`, `CommittedEntriesPreserved`, `RetiredNeverVotes`, `LogMatching` | pass |
| `RepairReplaceSafety` | 4 keepers, `MaxTerm=1`, replacement, aborts, stale learners, retirement | same | pass |
| `AbortedJointRestageSafety` | 4 keepers from `InitAbortedJoint`, `MaxTerm=3` | same | pass (CE-2 safety) |
| `AmnesiaWipe` | 3 keepers, `MaxTerm=2`, wipe and reinitialize | `ElectionSafety`, `CommittedEntriesPreserved`, `LogMatching` | pass (CE-1) |
| `ParkedRepairLiveness` | 4 keepers from `InitParkedDead` | `ParkedDeadVoterEventuallyRepaired` | pass |
| `AbortedReplaceLiveness` | 4 keepers from `InitAbortedReplace`, `MaxLogLen=8` | `ParkedDeadVoterEventuallyRepaired` | pass (CE-2) |
| `RecoverySingleReturnNoSnap` | 5 keepers from `InitPreRecovery`, one lost voter returns | `Safety` | pass |
| `RecoverySingleReturnSnap` | as above, with snapshots | `Safety` | pass (CE-3) |
| `RecoveryBothReturn` | as above, both lost voters return | `Safety` | pass (CE-4) |
| `RecoverySingleReturnLiveness` | 5 keepers from `InitPostRecovery` | `LostVotersEventuallyRetire` | pass |
| `RecoveryBothReturnLiveness` | as above, both return, survivor stopped | `LostVotersEventuallyRetire` | pass (CE-4) |
| `CatalogSafety` | 3 voters, 2 streams, `MaxTerm=2` | catalog invariants | pass |

## Counterexamples and their fixes

### CE-1: a wiped keeper under its old ID erased a committed entry

The calibration case. A keeper that lost its data and registry volumes and
was initialized under its old ID registered an empty voter from the first
peer frame, granted a vote with an empty log, and let a laggard erase a
committed record. Fixed on main by 6d75fec: peers report the incarnation
they first saw, the keeper marks itself reused, and `decisions::registers`
refuses every registration from peer traffic. The model now carries
`reused`, and `AmnesiaWipe` passes.

### CE-2: an aborted move wedged repair onto the same keeper

A move `[a, b, c] -> [a, b, d]` that aborted after `StageReplica` left `d`
at the next revision. Repair of a dead voter onto `d` from the same source
was refused as stale forever. `decisions::restages_replacement` restages
such a copy when the new stage is another ordinary move from the same source
revision and configuration.

The concern was that the staged copy may have voted under the aborted
move's uncommitted joint configuration, and that restaging it would lose
that vote. It does not: the WAL keeps one durable vote per stream
(`storage/wal.rs`, `Record::Ownership` clears only the log and snapshot), so
a restage keeps it. The restage drops the copy's log, which is safe because
`StageReplica` reaches ownership only with the authority's committed proof
that names the new stage at that source with no joint configuration. The
state machine accepts a joint configuration only for the applied stage, so
the aborted joint entry can never commit, and every configuration a future
leader can use needs a majority of the source configuration.
`AbortedJointRestageSafety` starts from a cut where `d` installed the
aborted move, the joint entry is on the old leader and `d` only, and `d`
voted under it; TLC explores the restage and every election after it.

### CE-3: a single returning lost voter served the lost suffix

A lost voter that restarted with a snapshot covering the lost suffix
answered `ReadAt` from its applied state, which needs no barrier. The rule:
a copy serves applied pages only once this keeper process certified its
placement (`decisions::serves_reads`). A lone lost voter hears no leader of
its configuration and the catalog fences it, so it never serves.

### CE-4: two returning lost voters formed a permanent split brain

The two lost voters are a quorum of the configuration the recovery left.
Returning together, they elected a leader, served the lost suffix, and once
the survivor was replaced, never met a recovered voter, never retired, and
repaired the dead survivor onto a spare. The README recorded this as a
residual risk; it is now closed for lost voters that restart.

#### Design: placement certification

- **Durable record.** Every replacement already records its stage in the
  catalog before `StageOwned`. A recovery now records its stage in the
  catalog before the survivor's durable round, after staging the
  replacements, and refuses without it. The catalog's latest staged move is
  the durable recovery epoch: a recovery is the only stage whose target
  keeps one voter of its source.
- **Who must ask.** A copy is certified, in memory, per copy generation, by
  an append from a leader whose vote does not lose to its own, by a
  bootstrap that registers it empty, or by the catalog. An uncertified copy
  sends no vote or pre-vote and serves no read. Granting votes stays
  unrestricted: with no certified candidate in a stale configuration, the
  grants elect no one there.
- **The catalog's answer.** `Request::Staging(stream)` returns the latest
  staged move, read on the replicated catalog's leader.
  `decisions::fences_copy` fences a copy whose effective configuration is
  neither side of an ordinary move, nor its joint configuration, and every
  configuration but the target of a recovery. A copy older than an ordinary
  move missed a committed configuration and could not win an election
  anyway, so fencing it costs no liveness. A fenced copy retires on the
  highest certified placement proof any keeper gives.
- **Normal path.** Leaders, and followers that hear leaders, certify through
  appends; parking keeps certification. Only a copy that opened without
  hearing a leader, which means after a restart, asks the catalog.
- **Catalog outage.** It holds back only uncertified copies. A stream whose
  three voters all restart while the catalog is down elects once the
  catalog answers; the replicated catalog stream certifies itself.

In the model, `CatalogCheck` certifies or fences a copy, `StartCampaign` and
`ClientRead` need `certified`, and `RetireRemoved` also retires a fenced
copy. `RecoveryBothReturn` and `RecoveryBothReturnLiveness` pass.

#### What it does not close

A lost voter that never stopped. The model's recovery requires the lost
voters to be down; the keeper's recovery counts a voter that does not answer
its status request as lost. A pair of lost voters that kept running,
partitioned from the survivor and in contact with each other, stays
certified and keeps leading the old configuration until it reaches a
recovered voter. Closing that needs certification that expires unless the
catalog renews it, so every stream would stop once the catalog had been
unreachable for the lease. That cost is the owner's decision; until then the
runbook requires confirming on each host that both lost keepers are down or
fenced.

### The snapshot leak

The survivor refused votes, pre-votes and appends from an excluded lost
voter but answered its snapshot chunks, and a refused hand-off, with its own
vote at the recovery term. Every frame that carries the sender's vote now
goes through `decisions::excludes_sender`. `LearnHigherTerm` models the
answers, and `LostStayBelowRecoveryTerm` checks that no lost voter learns
the recovered term.

## Fidelity review

Changes made to the first version of the model when it was checked against
the code:

- `WipeAndReinit` let a wiped genesis voter register on the first peer
  frame, which 6d75fec forbids. The model now tracks `reused`.
- `ReplicateOrHeartbeat` stands for appends and snapshot chunks together and
  applied sender exclusion to both, while the code excluded only appends, so
  the abstraction hid the snapshot leak. Since the fix it is faithful, and
  `LearnHigherTerm` models what an unexcluded answer teaches.
- `LogkeeperProtocol` had no catalog; `catalogStage` now records each move's
  and each recovery's stage.
- `AbortedReplaceLiveness` had `MaxLogLen=5`, too short for the learner,
  joint and final entries of a repair after a restage; it is 8.

Abstractions that remain:

1. **Direct RPCs instead of a message bag.** Reordered or duplicated stale
   messages from earlier terms are not modeled; Raft's vote order rejects
   them.
2. **Inline application.** Commit and apply happen together, while snapshots
   persist on their own, so a restart resets applied state to the snapshot.
3. **Coarse timers.** Repair, park, stale-learner, lease and backoff timers
   are nondeterministic events.
4. **Reachable cuts.** `InitParkedDead`, `InitAbortedReplace`,
   `InitAbortedJoint`, `InitPreRecovery` and `InitPostRecovery` start from
   short reachable prefixes so liveness and five-keeper recovery stay
   exhaustive.
5. **One recovery, no partitions.** The lost voters are down when the
   recovery runs, the catalog is always available, and a recovery is not
   retried from another survivor.
6. **Not modeled.** The vote-time check against other keepers' finalized
   configurations (`Request::LocalConfiguration`, 5788723): the model
   checks safety with certification alone, so it holds without that check.
   Multiplexed admission (Verus), WAL rotation and torn
   rounds, disk-full shedding, preferred-domain hand-off, multi-part catalog
   checkpoints, timed originals and `max_streams` eviction.
