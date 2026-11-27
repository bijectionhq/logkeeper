# TLA+ model of the consensus keeper's protocol additions

Two finite-state TLA+ specifications cover what Logkeeper adds on top of
OpenRaft 0.10.1 in `src/stream/consensus/`, and a third models the endgame's
configuration authority with epoch leases. `check.sh` checks every
configuration with a pinned TLC and exits non-zero when any outcome differs
from the one it expects, so CI can call it.

```sh
./verification/tla/check.sh        # every configuration
./verification/tla/check.sh fast   # skips the deep safety configurations
./verification/tla/check.sh additions   # only the focused models below
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

### `EpochLeases.tla`

The endgame design (`logkeeper-consensus-design.md`, "Endgame: a
configuration authority with epoch leases"): one stream, a compact Raft in
the style of `LogkeeperProtocol` (direct RPCs, full-log replication, commit
by inspection), and what the authority adds:

- **Time.** A global real-time tick and a local tick per clock. Every
  interval a keeper measures (a lease since its grant, the wait-out since the
  recovery) is an anchor `[le, d]`: `le` is the local time elapsed and
  `d = local - real` elapsed. Ticks keep `|d| <= D` for every live anchor,
  which is what bounded clock-rate drift gives over an interval no longer
  than a lease plus the wait-out. No two clocks are synchronized.
- **Leases.** One catalog record per keeper `{epoch, fenced_streams}`. A
  renewal is granted only to the current incarnation and says whether the
  stream is fenced for that keeper. The holder treats it as valid while its
  clock measured less than `L - M` since the grant.
- **Gating.** Campaign, become leader, append, replicate, commit and read
  need a valid lease of the current epoch that does not fence the stream,
  and a finished wait-out. Votes and follower appends are not gated.
- **Recovery** is one catalog transaction: new membership, the stream added
  to the `fenced_streams` of every old voter outside it (`FenceRule =
  "AllOld"`) or, as the spec words it, only of the keepers `--lost` names
  (`"NamedOnly"`), epoch bumps for named keepers declared dead, and the
  survivors' recovery round. `--lost` and "declared dead" are chosen
  nondeterministically: absent, partial or wrong. The recovered members then
  wait out `L + M` on their own clocks. The recovery term is only
  `RecoveryGap = 1` above the survivor's, so nothing relies on the `2^32` gap.
- **Two survivors (RF 5).** With `OnlyWriterRecovers`, as in the code, only
  the more advanced survivor gets the recovery round; the other keeps running
  with its log, term and lease. With `ExcludeLostIds` it refuses the lost
  voters from the recovery on (`Request::LocalProgressFencing`), and every
  copy that holds the recovery entry does too, in both directions: a
  candidate counts no fenced voter's vote and a leader replicates to none.
  With `SurvivorFence` the catalog also fences the stream for it until it
  finalized the recovered configuration (`Change::RecoverFrom`): its lease
  then gates it only while its recovery entry is not committed.
- **Environment.** Every keeper and the catalog sit on one of two sides; a
  bounded number of arbitrary re-partitions; a permanent catalog outage; a
  second incarnation of one keeper ID (new media) that registers under a
  bumped epoch while the first keeps running or stops.

Abstractions, each of which only adds behaviors, so a safety result carries
over:

1. A renewal's anchor starts when the catalog grants it, not when the holder
   sent it, which lengthens leases. A reply delivered late is simulated by a
   later grant: fences and epoch bumps are permanent, so a late reply that
   carries a fence permits nothing, and one that does not is dominated by a
   grant at the time the catalog answered.
2. `LeasedProcs` lists the keepers whose leases are modeled; every other
   keeper is treated as always holding a valid, unfenced lease. The
   recovery configurations model the lost voters' leases; the reuse and
   outage configurations model every keeper's.
3. One wait-out clock stands for every recovered member's: the one that
   finishes first, after which every member may act.
4. The survivors, the replacements and the catalog stay on one side when the
   network re-partitions (up to relabeling the sides, the other keepers
   choose freely); in the recovery configurations re-partitions happen after
   the recovery commits.

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

Every `LogkeeperProtocol` and `CatalogStream` configuration passes on the
fixed protocol. The counterexamples below were found by the first version of
the model; each configuration that failed then passes now, and none is kept
as an expected failure. The `EpochLeases` configurations, including their
expected failures, are listed in their own section below.

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

## Epoch leases (`EpochLeases.tla`)

### Properties

| Property | Meaning |
| --- | --- |
| `NoMixedHistory` | Once a reader has seen the recovered history, no reader sees a history the recovery did not keep, and every recovered read is a prefix of one log. Reads of the lost suffix before the recovered configuration serves are the acknowledged loss. |
| `CommittedEntriesPreserved` | Every gated leader holds every record of its world committed in an earlier term; a recovered leader also holds every pre-recovery commit the survivors kept. Old-world commits the survivors never held, including the lost voters' commits during the wait-out, are the acknowledged loss. |
| `ElectionSafety` | At most one leader per term within each world (the old configuration and the recovered one may reuse terms when the recovery gap is small; no record crosses between them). |
| `NewWorldLogMatching` | Log matching among logs that extend the recovery round. |
| `LossAboveReportedHead` | Every lost commit lies above the head the recovery reports. |
| `LeadershipLapses` | Once the catalog is down for good, eventually no keeper leads, ever again. |

### Configurations

Bounds common to the recovery configurations: keepers `s` (survivor), `a`
and `b` (lost), `r1` and `r2` (replacements); `L = 2`, `M = 1`, `D = 1`;
`RecoveryGap = 1`; lost voters start at term 2 and may reach 3, above the
recovery term 2; one re-partition after the commit; two appends. State
counts are from TLC 2.19 on 10 workers of the development Mac.

| Config | Setup | Checks | Result |
| --- | --- | --- | --- |
| `AuthorityRecovery` | both lost voters keep running, partitioned from the survivor and the catalog; `--lost` and "declared dead" free | `NoMixedHistory`, `CommittedEntriesPreserved`, `ElectionSafety`, `NewWorldLogMatching` | pass, 4,585,689 states, 4 min 47 s |
| `AuthorityOutageSafety` | as above, plus a permanent catalog outage at any time | same | pass, 9,171,378 states, 14 min on 4 workers |
| `AuthorityNoWaitOut` | control: no wait-out | same | `NoMixedHistory` violated |
| `AuthorityDriftBeyondBound` | control: `D = 2 > M = 1` | same | `NoMixedHistory` violated |
| `AuthorityNamedOnlyFence` | control: `--lost` narrows the fence, as the spec words it | same | `NoMixedHistory` violated (finding 2) |
| `AuthorityLossPoint` | control: from a cut where the survivor led and wrote a record it never committed | `LossAboveReportedHead` | violated (finding 5) |
| `AuthorityOutageLapse` | three keepers, every lease modeled, the catalog goes down for good, under fairness of time and step-down | `LeadershipLapses` | pass, 40,284 states, 10 s |
| `AuthorityOutageNoLease` | control: leases not modeled | `LeadershipLapses` | violated |
| `AuthorityReusedId` | keeper `k3` reincarnates on new media under a bumped epoch while the first incarnation runs or stops; 6d75fec kept | `CommittedEntriesPreserved`, `ElectionSafety` | pass, 1,011,168 states, 1 min 37 s |
| `AuthorityReusedIdEpochOnly` | control: the epoch bump without 6d75fec | same | `CommittedEntriesPreserved` violated (finding 3) |
| `AuthorityRF5` | RF 5 as the code recovers: survivors `s`, `t`, only the writer gets the recovery round and `t` keeps running with its lease; lost `a`, `b` running, `c` down (`StoppedAtStart`, a smaller cut than the earlier 8-keeper one); three replacements; `ExcludeLostIds`, `SurvivorFence`; `MaxNewTerms = 1` | as `AuthorityRecovery`, plus `FinalizedStaysRecovered` | not run to the end: no violation in 6,887,801 distinct states (stopped for memory). Its safety follows from `AuthorityRF5Exclusion`, whose unmodeled lease for `t` only adds behaviors |
| `AuthorityRF5Exclusion` | as `AuthorityRF5`, but `t`'s lease is not modeled (always valid and unfenced), so only the identity exclusion protects it | same | pass, 20,548,926 distinct states, depth 33, 36 min 44 s on 6 workers |
| `AuthorityRF5ExclusionControl` | control: as `AuthorityRF5Exclusion` without the exclusion | same | `NoMixedHistory` violated: 8,286,893 distinct states, 8 min 11 s on 6 workers, a 20-state trace (finding 4) |

`check.sh` runs all but the RF 5 configurations, which take too long for it: the controls and the liveness and
reuse configurations in `fast` mode, and `AuthorityRecovery` and
`AuthorityOutageSafety` with the deep configurations.

### Findings

1. **The lease design closes CE-4 for lost voters that keep running, with no
   term gap and no trust in `--lost`.** `AuthorityRecovery` lets both lost
   voters run through the recovery at terms above the recovery term,
   re-partitions the network once at any time after the commit (including
   healing the lost pair toward the survivor or the catalog), and chooses
   `--lost` and "declared dead" freely. A lost leader may overwrite the
   survivor's recovery round before the wait-out ends; the survivor then
   simply continues the old history, and no reader mixes histories. The Lean
   module `EpochLease` proves the same for any number of steps.
2. **`--lost` must not narrow the fence** (the code already fences every
   voter the recovery leaves). The spec says `--lost` "narrows
   fencing to named keepers". With a partial or wrong `--lost`, an unnamed
   lost voter that reaches the catalog renews an unfenced lease after the
   commit and, with the fenced voter's vote (votes are not gated), leads the
   old configuration next to the recovered one (`AuthorityNamedOnlyFence`).
   The recovery must fence every old voter outside the new membership;
   `--lost` can only add epoch bumps for keepers declared dead.
3. **The epoch bump does not replace 6d75fec.** Votes are not gated, so a new
   incarnation under a reused ID that may register from peer traffic votes
   with an empty log, and a laggard erases a committed record
   (`AuthorityReusedIdEpochOnly`, CE-1 again). With 6d75fec's refusal kept,
   `AuthorityReusedId` passes with the first incarnation still running. The
   reused-ID rule is load-bearing, not only defense in depth.
4. **With RF 5 and two survivors, the second survivor must refuse the lost
   voters from the recovery on, or be fenced by the catalog.** In the code
   only the more advanced survivor writes the recovery round; the other keeps
   running through the wait-out (`OnlyWriterRecovers`). Without protection,
   `AuthorityRF5ExclusionControl` finds this trace: after the recovery
   commits, the lost leader `a`, still on its lease, replicates its old
   history, with the lost record committed, to survivor `t`; the writer `s`
   leads the recovered configuration with the replacements, commits and
   serves the recovered history; `t` then serves the old one. The earlier
   argued trace (`t` leading the old configuration with the lost voters'
   votes and overwriting `s` at a higher term) has the same root. Two
   protections close it, and the code has both from level 9
   (`CLUSTER_VERSION_EXCLUSION`): the second survivor refuses the lost voters
   in both directions from the moment the recovery reads its progress
   (`ExcludeLostIds`, `Request::LocalProgressFencing`), and the catalog
   fences its copy until it finalized the recovered configuration
   (`SurvivorFence`, `Change::RecoverFrom`). `FinalizedStaysRecovered` also
   checks that no copy that finalized the recovery is overwritten. In the
   implementation the overwrite also trips OpenRaft's commit-index assertion
   when the writer catches the survivor up; a cluster test reproduced it
   before the fix (`keeper/tests/authority.rs`,
   `a_lost_leader_of_five_never_overwrites_the_recovered_history`). With one
   survivor (RF 3) nothing else holds the recovered history, so the overwrite
   is harmless, which is what the Lean proof covers.
5. **The reported loss point can hide a loss.** A recovery keeps the survivor's whole log,
   including records it never knew committed, and reports its head. If the
   survivor led and wrote records it never committed, and the lost voters
   then committed other records at the same LSNs, those acknowledged LSNs lie
   at or below the reported head and hold other records, so a writer that
   compares the head with what it was acknowledged sees no loss.
   `AuthorityLossPoint` finds the trace; the Rust tests
   `the_reported_head_never_covers_a_survivors_uncommitted_records` and
   `recovery_keeps_committed_store_records_over_a_survivors_uncommitted_ones`
   reproduce it on real keepers, the second with the offload store holding
   the committed records, which the restore then ignores because the
   survivor's head is at least the store's end. The fix the Lean module
   `OffloadPrefix` proves exact: restore only known-committed records, the
   larger of the store's committed run and the survivor's commit index, and
   report that as the loss point.

### Cross-check against the implementation (main at `3f15f877`)

The authority landed in `c1544919`, `e6d29472`, `2ba84f47` and `972f6a83`.
It matches the model on the points the model depends on: the recovery
transaction fences every voter it leaves, by configuration revision
(`decisions::copy_fenced`), whatever `--lost` names, which now only bumps
epochs (finding 2 does not apply to the code); a lease runs from the
holder's send time for the lease less the margin on its monotonic clock
(`lease_valid`); the recovery waits a lease plus the margin after the
catalog committed, before the survivor writes its round
(`recovery_wait`); campaign, lead, append, snapshot and reads are gated
(`holds_authority`); 6d75fec stays; and a recovery's offload lineage is its
configuration revision, the one recovery record `OneRecoveryRecord` checks.
Where the code is weaker than the model:

- **Lease length is per catalog keeper.** A grant carries the granting
  catalog keeper's configured `lease_millis` and margin, which the holder
  uses, but the liveness record does not keep it, and the recovery waits the
  answering catalog leader's own lease plus margin, at least the recovery
  host's. After a configuration change that shortens the lease, a lost
  keeper may still hold a longer lease granted by an earlier catalog leader
  when the recovered configuration starts serving. The model has one `L`.
  The catalog should record the longest lease it granted each keeper (or
  refuse to shorten below outstanding grants) and wait that.
- **`lease_valid` treats `now < sent` as valid.** With one monotonic clock
  this cannot happen, but the model's rule is strictly "less than `L - M`
  elapsed"; returning invalid there costs nothing.
- **Loss point** (finding 5) on main, with and without offload.

## Focused models (`check.sh additions`)

Small models of single mechanisms, each with a passing configuration and
controls that drop one rule and must fail on the named invariant
(`check.sh` matches the invariant's name, not only TLC's exit code). They run
first and in seconds; `./verification/tla/check.sh additions` runs only them.

### `Relocation.tla`: compaction relocation and checkpoints

One slice of a stream whose extent compaction copies from segment `source`
to `destination` (`Wal::relocate_segment`, `Record::Relocate`,
`Objects::relocate`), one index page, the WAL checkpoint, the stream's
selected snapshot, a park and wake, and one crash with restart. A segment is
reaped once nothing pins it. Modeled pins: the live slice; the checkpoint's
selected and pending cut (an old segment outlives the checkpoint that names
it); the move hold, which keeps `source` while the selected snapshot may
still name it, until a snapshot built after the move is selected
(`hold`/`last_move`/`release_moved`); and the durable park mark
(`snapshot::Pin::persist`), which names the pinned segments and the held
moves. Replay ignores `Record::Relocate`, so a crash puts the slice back at
the checkpoint's cut.

| Config | Rule dropped | Result |
| --- | --- | --- |
| `Relocation` | none | `RootsReadable`, `ParkCanReopenAfterRestart` and `ReclaimsSource` (the source is eventually reaped) pass |
| `RelocationNoCheckpointPin` | the checkpoint does not pin its cut | `RootsReadable` violated |
| `RelocationReusePages` | a rebuild after a move reuses the selected pages | `RootsReadable` violated |
| `RelocationLateWatermark` | the build reads the move watermark at selection, not before its pages | `RootsReadable` violated |
| `RelocationNoParkPins` | the park mark names nothing | `RootsReadable` violated |
| `RelocationParkRace` | the swap and the move hold are two steps (`AtomicMoveHold = FALSE`) | `ParkCanReopenAfterRestart` violated |

**Finding R-1 (fixed).** `RelocationParkRace` is how the code was:
`Objects::relocate` pointed the slice at its copy and released the table
lock, and the WAL thread registered the move hold afterwards. A park that
took its pin in between named only `destination` (the pin reads the slice's
current segment, and no hold was registered yet), the checkpoint moved on,
and after a restart the restored mark kept the copy parked while `source`,
which the selected snapshot still names, was reaped: the copy could not
reopen. The Rust test
`storage::tests::a_park_mark_keeps_the_selected_snapshot_during_relocation`
reproduces it with the `ReplicaFault::AfterRelocationSwap` pause.
`Objects::relocate` now registers the hold under the same lock as the swap.

### `AsyncAppend.tla`: async leader append and the durable commit index

Three voters, a fixed leader and three records (53b9a6d, 07635deb). The
leader queues an append on its WAL and replicates it from the in-memory
overlay before its own write lands (`Queue`, `Send`); each copy becomes
durable separately (`Flush`). Commit counts only durable copies, the
leader's on `io_completed` (`Choose`). A follower learns the commit index
only up to its durable log, and every copy applies only durable records.
`save_committed` notes the index and the WAL writes `Record::Committed` in a
later round once the log holds the exact ID (`Note`, `Mark`). A crash at any
point drops the overlay, the noted index and applied state, and keeps the
durable marker. With two voters down a recovery may start from a down copy;
it keeps only that copy's durable commit (fc4855ed).

| Config | Bounds or rule dropped | Result |
| --- | --- | --- |
| `AsyncAppend` | two crashes at any point | `ChosenHasDurableQuorum`, `AppliedHasLocalBytes`, `MarkerHasLocalCommittedBytes`, `RecoveryKeepsOnlyCommitted` pass, 1,299,627 states, 69 s on 3 workers |
| `AsyncAppendLiveness` | one crash, under fairness | `RequestsSettle` (every request is answered, or a recovery ran) and `MarkersCatchUp` pass, 541,513 states, 5 min 34 s on 3 workers |
| `AsyncAppendCountOverlay` | the leader counts its overlay toward commit | `ChosenHasDurableQuorum` violated |
| `AsyncAppendRecoverTip` | the recovery keeps the writer's durable tip | `RecoveryKeepsOnlyCommitted` violated: the leader's durable but uncommitted record survives |
| `AsyncAppendNoIdleFlush` | no idle flush of the noted index (`COMMITTED_FLUSH`) | `MarkersCatchUp` violated |

Abstractions: one leader for the whole run (elections are
`LogkeeperProtocol`'s), record positions instead of log IDs, so a
truncation is not modeled, and one `Record::Committed` round per step (a
torn round lands the marker with its records or not at all).

### `OffloadRetention.tla`: reads below the local floor

Two keepers, three records, uploads to the store, retention that drops
local copies once the run is offloaded, trims, one leader change and a store
outage (3f15f877). A read below a keeper's local floor and above its applied
trim floor is served from the store only by the leader, after a read barrier
that waits until the trim committed at the barrier is applied, and after it
checks the floor again; any other keeper, or a failed barrier, answers
`Unavailable`. The barrier is abstracted to "the keeper is the leader when
it starts and when it completes": a deposed leader's barrier fails on the
quorum.

| Config | Rule dropped | Result |
| --- | --- | --- |
| `OffloadRetention` | none | `RetentionCovered`, `RemoteReadHadBarrier`, `NoPostTrimRemoteRead` (never a record trimmed before the read was invoked), `RemoteRechecksFloor`, `RemoteReturnsExactBytes`, `RemoteRequestSettles` pass, 11,545 states |
| `OffloadRetentionNoBarrier` | any keeper serves from the store, as before 3f15f877 | `NoPostTrimRemoteRead` violated |
| `OffloadRetentionNoRecheck` | no floor check after the barrier | `NoPostTrimRemoteRead` violated |

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
