# Asynchronous stream journal refinement

Every keeper effect in the 10,000-seed simulator corpus replays against Study 119.
For a fixed ensemble, an I/O automaton of the writer and keeper proves that every
action is a step or stutter, and that Study 119's contract holds in every reachable state.
[Study 119](Logkeeper/StreamJournal.lean) · [Automaton](Logkeeper/StreamIO.lean) ·
[Replay](Logkeeper/StreamTrace.lean)

## The two counterexamples

**An empty Append publishes an inherited head. Kept; Study 119 extended.** Seal must
return a head that a quorum has published, so that a later `head` or read from any keeper
covers it. After a takeover the new epoch may own no record at all, so the only way to
publish the adopted head without adding a consumer-visible record is an empty Append.
Raft's alternative, a no-op entry, would put a record into a stream whose records belong to
the consumer. The behaviour is therefore necessary. Study 119's retained-record retry
becomes a `publish` step: a synced voter raises its head to a certified cut within its
tail. Its soundness rests only on the cut being certified, which `keeper_head_was_advertised`
already used, so the five contract proofs needed no change. The former rule is kept as the
`RetainedRetry` control; `inherited_publication_witness` reaches a keeper with no epoch-2
record, shows the old rule fails, and takes the new step.
[Keeper rules](../../src/stream/keeper/rules.rs) · [Witness](Logkeeper/StreamAsync.lean)

**An incomplete Sync exposes a partial history. Removed; the keeper stages it.** The
partial image mixed the keeper's voted history with records of a newer seed under the old
`synced` epoch, and a later Seal ranked that mixture as if it were a vote. It is safe, but
only by a new argument about mixtures that the Paxos core cannot express. Clearing
`synced` instead would lose a chosen record (a keeper in a commit quorum would rank below
a stale keeper). The simpler result is the one view change Viewstamped Replication already
makes atomic: the keeper stages an incomplete Sync's records and floor, and its view,
including every Seal and Check reply, changes only when a complete Sync installs them. A
new promise discards the staging. Staged records live in the WAL and in the retained and staged ranges of the
shared checkpoint index, so a long transfer survives rotation and reopen. Study 119's model
was already staged, so it is unchanged. `incomplete_sync_with_changed_tail_has_no_reference_step`
is now the negative control, and the replay rejects the former effect.
[Keeper state](../../src/stream/keeper/state.rs) · [WAL](../../src/stream/keeper/wal.rs)

Matching the shipped rules exactly also extended Study 119 in four smaller ways, each
already in the code: Append carries several records, a Sync carries a floor that can skip
a trimmed prefix and installs a certified head on completion, a synced keeper can install
a floor over a prefix it never received, and Delete can tombstone a stream a keeper never
created. The unused `SameCommitted` guard on Sync was dropped: the keeper preserves its
committed prefix by starting at `head + 1`, and the complete Sync's head is certified.

## The I/O automaton

`StreamIO` composes three Study 119 keepers, a network that can lose, duplicate, delay and
reorder whole packets, and one writer per epoch. A ghost writer records each epoch's round,
its issued history and the certified cuts. Reply packets carry the durable fact their
effect established: a Seal reply its saved snapshot, a complete Sync or Append reply its
vote.

| Action | Shipped await point or effect |
| --- | --- |
| `send` | The fixed-ensemble automaton enqueues Seal, Sync, floor installation, Append and publication, Trim, observations, and Delete. `Sendable` checks the request at durable issuance. `WireSendable` also covers Append bytes that are still pending at wire dispatch. |
| `deliver` | One keeper round for one request: decide, make the effect durable, reply. The packet stays in flight, so it can be delivered again. `Admitted` is the keeper's rule; `effect` its durable change. |
| `refuse`, `drop`, `restart` | A refusal, request or reply loss, and a keeper reopen. None changes durable state. |
| `collectSeal`, `choose` | Receive a Seal reply before the election, then select from two (`Round.winner`, linked to `outranks`). The epoch's issued history becomes the winner's history. |
| `collectVote`, `certify` | A lane receives a durable vote; `decision::acknowledged` certifies a cut covered by two lanes. |
| `issue` | Freeze a covering pending prefix at its first possible durable acceptance. |

A crashed or cancelled writer simply takes no further action; its packets stay in flight.

| Theorem | Statement |
| --- | --- |
| `deliver_refines` | A delivered request that the keeper admits and the writer could send is a Study 119 step or stutter. |
| `step_mono`, `reachable_mono` | Reference steps and reachability survive a growing ghost writer. |
| `sendable_persists`, `reply_evidence` | An in-flight request stays sendable across every keeper step; a reply witnesses its durable fact. |
| `next_inv`, `reachable_inv` | Thirteen invariants hold in every reachable state, including reply provenance, saved snapshots before election, seed-prefix staging and certified cuts chosen by two durable votes. |
| `every_action_refines` | Every action is a Study 119 step or stutter at each keeper, and the ghost writer only grows. |
| `run_refines` | Adjacent states of any run supply Study 119's `KeeperTrace`, the premise of its head theorems. |
| `certified_cuts_agree`, `committed_contiguous` | Certified cuts are prefixes of one another; committed records are contiguous and irrevocable below any floor. |
| `seal_covers_acknowledged` | A seal's adopted history contains every append acknowledged at a lower epoch. |
| `read_exact` | A page from any keeper is exactly the committed slice it asks for, including records another keeper trimmed. |
| `acknowledged_survives_one_disk_loss` | An acknowledged append has a durable vote on a keeper other than any one lost keeper. |

`execution` turns every reachable state into a Study 119 `Execution`, so each of its
contract theorems applies. [`automaton_witness`](Logkeeper/StreamIOWitness.lean) is a
reachable 36-action run: two keepers sync at epoch 1, one accepts a record, epoch 2 elects
both, completes Sync on one, stages and then completes on the other, certifies the
inherited record and publishes head 1 on a keeper that holds no epoch-2 record. The 15
automaton reports and the witness use only `propext`, `Classical.choice` and `Quot.sound`.

Each automaton guard has a control. `run_stream_io_controls.py` weakens it and requires
the first error in the named proof.

| Weakened guard | Failing proof |
| --- | --- |
| Stage from another identity; stage after complete Sync; Sync without seed agreement; Append anywhere; Append of an unissued payload; publish while unsynced; publish an uncertified head; Trim above the head | `deliver_refines` |
| Seal at epoch zero | `reply_evidence` |
| Collect a Seal reply after election; choose an unsaved report; elect an epoch twice; certify on one lane | `next_inv` |

## Trace correspondence

The simulator records every delivered request with the keeper's durable image before and
after it, including staged records, and every WAL reopen. The Lean replay checks each row
against Study 119's step for that request: its keeper-side admission and its exact effect
on the view, the staged history, and the epoch runs. Reopen must restore the durable image,
and refusals and observations must not change it.

| Corpus | Effects |
| --- | ---: |
| 10,000 seeds | 991,916 |
| Stutters (observations, retries, reopens and other refusals) | 598,123 |
| Create · Seal · Delete | 30,909 · 62,727 · 30,000 |
| Staged Sync · complete Sync · floor installation | 4,373 · 62,727 · 52 |
| Append · publication · Trim | 82,004 · 82,872 · 29,948 |
| Disk loss · survivor installation · learner installation | 909 · 1,818 · 909 |
| WrongEnsemble | 4,545 |

The runner mutates real rows into 47 controls. These
include the former visible incomplete Sync, a Seal that reports staged records, a Seal or
complete Sync that keeps staging, a stale promise or another identity on each request, an
unsynced or learner append or trim, gaps, wrong record epochs, uncertified publication, a
read beyond the head, a reopen that loses state, and learner promotion before both
survivors install the destination ensemble.

```sh
python3 verification/lean/run_stream_traces.py
python3 verification/lean/run_stream_io_controls.py
```

## Writer decisions

A keeper persists a proposal ID with each seal promise and verifies it on
an equal-epoch retry. A writer instance and a sweep plan each generate a UUID and
reuse it for their own retries. They require the returned view to echo it. Two
proposals cannot both elect at one epoch on this roster because their promise quorums
intersect. The model represents the pair of authenticated identity and proposal ID as
one proposer. This projection uses distinct generated IDs and compliant senders. [Seal admission](../../src/stream/keeper/rules.rs) ·
[Writer](../../src/stream/writer/mod.rs) · [Sweeper](../../src/stream/keeper/sweep.rs)

`issued_origins` tracks the originating epoch of each position in every issued
history. `same_epoch_agrees` uses it to show equality through a position with
the same record epoch. The recovery-start decision checks the predecessor above
the transfer floor. At the floor the keeper discards the preceding positions and the
ghost image takes that prefix from the seed. The link runner connects the checked
predecessor to `Agrees` and the fallback comparison to exact record equality.
A lagging keeper whose floor has advanced past the seed first installs that seed
and then installs the issued floor. A committed retry checks retained bytes with
`Recover` before publishing, so an arbitrary caller payload never serves as an
Append probe. [Writer proofs](Logkeeper/StreamWriter.lean) ·
[Recovery](../../src/stream/writer/recovery.rs) · [Append lanes](../../src/stream/writer/append.rs)

`StreamHead` uses quorum-accepted cuts from the automaton. A physical event
can choose several successive positions. Its logical cuts let a head result fall
between individual records of that batch. An opening choice persists on its
quorum. Intersection with the fresh sampling quorum bounds the choice by a sampled
tail, including across an intervening takeover. A published head proves the chosen
upper bound. The observer can confirm its pinned index in a later round.
`inherited_head_witness` samples the two ready keepers of the 36-action
automaton witness and returns the inherited cut. The proofs use three keepers,
arbitrary payloads and natural-number event indices. Verus checks the numeric
decisions over Rust's representable integers. [Head cuts](Logkeeper/StreamHead.lean) ·
[Head rounds](../../src/stream/writer/head.rs) · [Verus links](../link/README.md#stream-journal)

## Replacement and WAL

The authority projection follows one permanent disk loss, both survivor repairs, two
independent installs, and learner promotion. Neither route can form a fresh Seal quorum
during a split. Once promoted, a further single disk loss leaves two copies of the
transferred history. In the I/O projection, two successful empty Append deliveries at
the adopted tail supply the survivor votes. With those durable images preserved across
installation, they form the next roster's certificate. `RepairHistory` composes any
number of such transfers with fixed-roster steps. The fresh head proof applies after the
last transfer and covers the original acknowledged cut. A Rust test transfers 8,193
records across two successive replacements, appends between them, and checks old and
current routes.
[Replacement projection](Logkeeper/StreamReplacement.lean) · [Study 119](../119-stream-journal/README.md)

The WAL projection treats complete decoded entries as stream-local images. It proves
that a torn newest frame leaves complete entries intact and the continuation marker
carries only per-stream pending fragments. Recovery uses the old WAL until the
keeper-wide index is published above durable extent packs. The link runner projects the
ordered file sync, rename, directory sync and retirement calls from the rotation code.
Every prefix of that publication sequence is reachable in Lean. At the rename boundary,
either index recovers the same image and newer WAL. A reachable two-stream run appends
during checkpointing and reopens before publication and after retirement.
[WAL projection](Logkeeper/StreamWAL.lean)

## Completed exchanges

`StreamRpc.Exchange` indexes a send, the keeper decision for that request and
the reply receive on the same three-keeper timeline. For `head`, queue drain
precedes the round, each slot carries its keeper's exact Check or Append sample,
and the writer supplies two publication completions. The observer can use a
later confirmation round. The two completion theorems derive the logical
linearization cut from those exchanges. The writer batches queued callers before opening a round. The lane serial
marks when its Append is issued, and the observation channel belongs to that
Append. The observer uses the proposer driver for its own Check rounds.

For Trim, both counted exchanges return floors strictly above the request. The
model uses the local publication wait when the writer knows the cut and the
keepers' durable head checks when the local snapshot is behind. For Delete, two
distinct exchanges establish tombstones that exclude any later live quorum on
the same ensemble. The Rust quorum collector takes one future per ensemble
slot. Broadcast keeps the third future running after the first two replies.

For Read, committed prefixes of the same keeper extend over time. A later
chunk therefore supplies the exact continuation within the first head. The
fallback selector carries only complete pages and selects a Trimmed floor from
an observed reply above the original request. For a positive count, an empty
page samples a head below the requested start. The writer ends a long poll at
the call deadline and takes an immediate sample if the timer fires. Fallback
uses the remaining time and page continuation requests have no wait.

For recovery, the retained runs describe the epoch at each covered position,
including after clipping a prefix or suffix. A Recover that still observes
the promised epoch either sees the earlier Seal's unchanged history or the
elected seed installed by a complete Sync. Committed catch-up fetches return
the exact assigned slice from a previously accepted slot. The send theorem
covers every modeled request constructor when supplied local dispatch evidence.
An Append uses its exact contiguous run and a cut certified from distinct
durable lane votes. Freezing a covering prefix transfers the pending request's
send evidence to the issued history. A definitive capacity refusal is a
stutter in the durable projection.

These results quantify over three keepers, one stream, arbitrary payloads,
and natural-number positions and event indices. Present wire epochs map to
one plus their value to leave model epoch zero for the absent promise. The
new Trim witness extends the reachable 36-action inherited publication run
with a send and durable delivery. The clock lemmas use elapsed time independently
of the event indices. The runtime controls cover dropped read continuations,
late poll replies, and counting the same keeper twice for Trim or Delete.
[Exchange proofs](Logkeeper/StreamRpc.lean) · [Read proofs](Logkeeper/StreamRead.lean) ·
[Recovery proofs](Logkeeper/StreamRecovery.lean)

## Wire dispatch and durable issuance

The wire Append carries an exact slice of the issued history followed by
the assigned suffix. Its advertised head must already lie in the issued
history. Issuing a prefix preserves this combined view, including the
bytes beyond the prefix that other lanes may still need. An admitted
new Append gives an issue, an ordinary send of the same packet, and a
durable delivery of that packet. This proof computes the covering prefix
from the LSN and the payload count.

In the 27-action capacity witness, three keepers definitively refuse a
two-record pending batch. The new assignment at its first LSN has
different bytes. Both sends satisfy `WireSendable`. Treating both as
ordinary `Sendable` sends is impossible because issued history only
grows. A native refinement must therefore record wire dispatch while
the suffix is pending and enter the durable automaton at the issuance
boundary. The witness uses one epoch, three keepers, and natural-number
payloads. The transition proofs quantify over arbitrary payloads and
positions. [Wire dispatch](Logkeeper/StreamIO.lean) ·
[Capacity witness](Logkeeper/StreamIOWitness.lean)

Replace uses the authority model's `ReplaceSendable` predicate. It permits
the learner send only after both survivor installs and covers idempotent
retries after promotion. A five-step witness reaches a phase where all
three sends are permitted. [Authority model](Logkeeper/StreamReplacement.lean)

## Proposer transitions

The proposer dispatches Read, observer Head, election and recovery Sync,
Create, Trim, Delete, and sweep. The driver executes Send and Sleep effects
and returns ticketed transport outcomes and timer expiries. Request futures
own their keeper and ticket. Create and Delete dispatch all three futures
as tasks, so completion can leave the last already-issued request running.
Recovery fallback can cancel outstanding waits while preserving possible
effects of requests that have reached a keeper.

The lane state assigns append positions, decides what each lane needs,
updates acceptance and publication, and completes new append calls after
publication. The async adapter still owns the lane tasks, mutation lock,
Append observation channels and head caller batching.

- [Proposer step](../../src/stream/proposer/mod.rs)
- [Effect interpreter](../../src/stream/proposer/driver.rs)
- [Append state](../../src/stream/proposer/append.rs)
- [Election and Sync](../../src/stream/proposer/recovery.rs)
- [Replacement](../../src/stream/proposer/sweep.rs)

`StreamProposer.Schedule` checks one slot of the interpreter's order. A
matching outcome consumes its send, and a stale outcome leaves the slot
unchanged. A four-event witness issues, cancels, reissues, and receives in
one slot. The proof uses arbitrary natural-number tickets. The Rust allocation
and matching functions are verified over all `u64` inputs. The Lean link
checks their result specifications within that width. Separate mutations
reuse an issued ticket and accept an outcome with a different ticket.
[Slot schedule](Logkeeper/StreamProposer.lean)

## Boundaries

- **Proposer refinement.** The ticket theorem establishes local ordering.
  Proving every shipped send `Sendable` still requires an induction relating
  the actual lane assignments, selected recovery runs and transferred bytes
  to `StreamIO`'s issued history. `Dispatch` remains a premise of
  `dispatch_sendable`. The Append transition supplies a `WireSendable`
  projection once those assignments and bytes are related. Replace
  uses the separate authority model, so it still needs a bridge from
  the sweep's native state and replies to that model's phases.
- **Completion provenance.** A matched ticket identifies the operation
  and slot. The Lean completion theorems need the exact keeper decision and
  delivery index, including the first read chunk, each continuation and each
  sampled or publishing lane. The driver and typed replies do not supply a
  checked mapping of transport outcomes to these `StreamRpc.Exchange`
  witnesses. The active writer's watch-channel observations and its local
  publication gate also need that mapping.
- **Keeper decisions.** Verus and the link runner cover proposal equality, per-run
  bounds, record charge, Sync head bounds, the projected Replace decision, valid
  ensembles, and installation's ensemble and learner fields. Full refinement of
  `decide` and `apply` still needs the wire request projection, retained bytes and
  run lookup, quota accumulation and the native retained and staged transitions.
  [Keeper decisions](../../src/stream/keeper/rules.rs)
- **Replacement and authority.** The repeatable transfer theorem starts from two
  projected publication deliveries and preserved survivor states. It assumes that
  the next roster supplies a reachable automaton state. The raw Seal, Recover, Sync
  and Replace RPC projections, learner activation in that state, concurrent moves,
  and a fresh head round that overlaps a switch remain open.
  [Sweeper](../../src/stream/keeper/sweep.rs)
- **WAL and transport.** Reopen rows check the durable image for every recorded reopen.
  The frame and extent links start from decoded length and offset fields and computed
  CRC values. They rely on the `crc32fast` implementation and successful filesystem
  calls obeying the file and directory durability boundary. Full frame serialization,
  byte-level CRC implementation, and the contents of the file writes are open.
  A `Batch` envelope
  is transport framing that the keeper splits into single requests before deciding.
- **Payload bytes.** The replay checks positions and record epochs. The conformance
  history checker compares payload bytes.

The trace checker projects recorded keeper effects and reopens to the same
durable state. The first-accept control reaches one durable acceptance and
checks that a read cannot expose it before a takeover adopting an empty
history.
