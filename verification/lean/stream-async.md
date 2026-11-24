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
| `send` | Every request a writer dispatches: Seal in `Recovery::choose`, Sync chunks and completion in `Recovery::sync`, floor installation, lane Append and publication, Trim, Check, Read, Recover, Delete. The guard `Sendable` is what the writer guarantees. |
| `deliver` | One keeper round for one request: decide, make the effect durable, reply. The packet stays in flight, so it can be delivered again. `Admitted` is the keeper's rule; `effect` its durable change. |
| `refuse`, `drop`, `restart` | A refusal, request or reply loss, and a keeper reopen. None changes durable state. |
| `collectSeal`, `choose` | Receive a Seal reply before the election, then select from two (`Round.winner`, linked to `outranks`). The epoch's issued history becomes the winner's history. |
| `collectVote`, `certify` | A lane receives a durable vote; `decision::acknowledged` certifies a cut covered by two lanes. |
| `issue` | `Active::append` assigns the next positions to a payload. |

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

## Boundaries

- **Writer send refinement.** The linked decisions prove when a verified predecessor
  establishes Sync agreement, when a fallback epoch identifies the seed record and
  how an assigned append range bounds the published head. The projection of compressed
  epoch runs, the binding of asynchronous Recover responses to their snapshots and
  the construction of the exact assigned byte slice from the lanes' maps remain
  code premises. `Sendable` also requires the published cut to be certified. The
  link for `acknowledged` supplies quorum certification given correctly bound
  lane slots. Pending assignments are separate from the issued history.
  `issue` freezes an assigned prefix at its first possible durable acceptance.
  `discard` clears the pending suffix after three current capacity refusals
  when the unanswered-append bound is covered by the issued prefix. A
  three-keeper witness discards two assigned records and reassigns their first
  position. The automaton takes the capacity outcome and lane completion as
  inputs. Study 119 checks the bounded quota and duplicate cases, and the
  Rust control delays a timed-out request across trim.
- **Keeper decisions.** Verus and the link runner cover proposal equality, per-run
  bounds, record charge, Sync head bounds, the projected Replace decision, valid
  ensembles, and installation's ensemble and learner fields. Full refinement of
  `decide` and `apply` still needs the wire request projection, retained bytes and
  run lookup, quota accumulation and the native retained and staged transitions.
  [Keeper decisions](../../src/stream/keeper/rules.rs)
- **Head round projection.** The cut proof consumes the queue-open event, per-keeper
  send and durable-sample events, and the exact keeper view at each sample. Verus and
  the link cover serial freshness, epoch eligibility, the maximum sample and the quorum
  count. Rust tests cover queued batching, later callers, stale-writer fallback and index
  pinning. The async projection from Tokio queue and lane events to `Samples` and the
  binding of raw reply tails to their durable send events remain open.
- **Reads.** `read_exact` covers the keeper slice and `assemble_read_chunk` proves
  that an exact following chunk bounded by the first head extends the page. The
  async projection of subsequent replies to exact slices of that keeper remains open,
  as do abandoned partial pages on fallback, observed floor precedence, and the
  long-poll deadline and wake-up.
- **Trim and Delete quorums.** Keeper effects and quorum intersection for durable
  tombstones on one roster are proved. A Trim through a locally known head waits for
  publication, and every successful Trim reply must have floor above the requested
  cut. For Delete the writer broadcasts to three distinct keepers and counts two
  durable tombstone replies. The async projection of the Trim publication wait and
  both operations' reply collection into quorum evidence remains open.
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

## Await sites

These sites identify the action or completion boundary an I/O automaton needs
to represent. Wrapper futures share the action of the delegated future.

| Path | Await sites and effects |
| --- | --- |
| Stream entry points | [Placement delegates to Create](../../src/stream/writer/mod.rs#L103), [Create locks the stream](../../src/stream/writer/mod.rs#L275) and [collects a quorum](../../src/stream/writer/mod.rs#L285), [Seal delegates to the election](../../src/stream/writer/mod.rs#L290), [Append waits for its active lane result](../../src/stream/writer/mod.rs#L303) or probes authority on [a local conflict or trim](../../src/stream/writer/mod.rs#L305) or [a missing active epoch](../../src/stream/writer/mod.rs#L309), and the [Read](../../src/stream/writer/mod.rs#L321), [Head](../../src/stream/writer/mod.rs#L325) and [Trim](../../src/stream/writer/mod.rs#L329) wrappers delegate to their respective state. |
| Mutation coordination | [Acquire election lock](../../src/stream/writer/mod.rs#L115), [complete same-epoch head check](../../src/stream/writer/mod.rs#L127), [choose the recovery history](../../src/stream/writer/mod.rs#L136), [await ready lanes](../../src/stream/writer/mod.rs#L141), [await adopted head publication](../../src/stream/writer/mod.rs#L143), [acquire trim lock](../../src/stream/writer/mod.rs#L162), [probe trim authority](../../src/stream/writer/mod.rs#L165), [await known head coverage](../../src/stream/writer/mod.rs#L169), [receive Trim reply](../../src/stream/writer/mod.rs#L185) and [finish Trim quorum](../../src/stream/writer/mod.rs#L192), then the independent Delete path [acquires its lock](../../src/stream/writer/mod.rs#L335) and [finishes its broadcast quorum](../../src/stream/writer/mod.rs#L345). |
| RPC and quorum collection | [Receive an authority reply](../../src/stream/writer/mod.rs#L227), [receive an RPC or timeout](../../src/stream/writer/mod.rs#L361), [receive a broadcast lane reply](../../src/stream/writer/mod.rs#L379), [join the spawned lane](../../src/stream/writer/mod.rs#L387), [finish broadcast quorum](../../src/stream/writer/mod.rs#L389), [receive empty Append publication](../../src/stream/writer/mod.rs#L411) and [collect the next quorum reply](../../src/stream/writer/mod.rs#L425). |
| Election and recovery | [Receive a Seal reply](../../src/stream/writer/recovery.rs#L32) and [select from the quorum](../../src/stream/writer/recovery.rs#L36). Each lane [seals its target](../../src/stream/writer/recovery.rs#L73), may [install a newer floor](../../src/stream/writer/recovery.rs#L82), and otherwise [fetches a record](../../src/stream/writer/recovery.rs#L103), [installs a chunk](../../src/stream/writer/recovery.rs#L120) and [completes Sync](../../src/stream/writer/recovery.rs#L123). |
| Recovery RPCs | [Fetch from the selected keeper](../../src/stream/writer/recovery.rs#L139), or [seal a fallback](../../src/stream/writer/recovery.rs#L145), [fetch its record](../../src/stream/writer/recovery.rs#L149) and [choose an eligible reply](../../src/stream/writer/recovery.rs#L152). The wrappers await [floor installation](../../src/stream/writer/recovery.rs#L172), [Recover](../../src/stream/writer/recovery.rs#L196), [Seal](../../src/stream/writer/recovery.rs#L221) and [Sync](../../src/stream/writer/recovery.rs#L265). |
| Append progress | Wake [ready](../../src/stream/writer/append.rs#L129), [published](../../src/stream/writer/append.rs#L164) and [competing payload](../../src/stream/writer/append.rs#L235) waiters on lane changes. Receive [the chosen position](../../src/stream/writer/append.rs#L240), then [await head publication](../../src/stream/writer/append.rs#L243), or [retry a committed position](../../src/stream/writer/append.rs#L247) and [check its reply quorum](../../src/stream/writer/append.rs#L269). [Wake a head round that needs to cover a sample](../../src/stream/writer/append.rs#L313). |
| Append lanes | [Sync a lane](../../src/stream/writer/append.rs#L324), [install a floor](../../src/stream/writer/append.rs#L328), [fetch committed bytes](../../src/stream/writer/append.rs#L334), [complete an Append call](../../src/stream/writer/append.rs#L337) or [complete publication](../../src/stream/writer/append.rs#L343). The fetcher [collects the next Recover reply](../../src/stream/writer/append.rs#L376) and sender [receives an Append reply](../../src/stream/writer/append.rs#L403). The lane [wakes on new work](../../src/stream/writer/append.rs#L539) and [returns the work result to the lane state](../../src/stream/writer/append.rs#L550). |
| Head caller and round | [Yield to batch callers](../../src/stream/writer/head.rs#L22), [complete a check](../../src/stream/writer/head.rs#L25), [complete fallback observation](../../src/stream/writer/head.rs#L29) and [return the result to a caller](../../src/stream/writer/head.rs#L40). The check delegates to [writer](../../src/stream/writer/head.rs#L45) or [observer](../../src/stream/writer/head.rs#L47) sampling. |
| Head sampling | The writer [yields after opening](../../src/stream/writer/head.rs#L54), awaits [a fresh lane observation](../../src/stream/writer/head.rs#L58) or [Check](../../src/stream/writer/head.rs#L66), [collects samples](../../src/stream/writer/head.rs#L84), [covers the selected tail](../../src/stream/writer/head.rs#L90) and [confirms publication](../../src/stream/writer/head.rs#L91). The observer [completes a round](../../src/stream/writer/head.rs#L109), [retries after a delay](../../src/stream/writer/head.rs#L113) and [collects the next Check](../../src/stream/writer/head.rs#L125). The shared Check wrapper [awaits the wire reply](../../src/stream/writer/head.rs#L176). |
| Reads | [Try one keeper](../../src/stream/writer/read.rs#L23), [sample the first chunk](../../src/stream/writer/read.rs#L69) and [fetch subsequent chunks](../../src/stream/writer/read.rs#L97). The keeper [enqueues the request](../../src/stream/keeper/mod.rs#L115), [waits for the WAL worker's result](../../src/stream/keeper/mod.rs#L117) and [wakes or times out a long poll](../../src/stream/keeper/mod.rs#L121). |
| Replacement coordination | [Complete a sweep plan](../../src/stream/keeper/sweep.rs#L38), [seal both survivors](../../src/stream/keeper/sweep.rs#L59), [copy to the other survivor](../../src/stream/keeper/sweep.rs#L87), [complete Sync on the source](../../src/stream/keeper/sweep.rs#L99), [publish on both survivors](../../src/stream/keeper/sweep.rs#L103), [create the learner](../../src/stream/keeper/sweep.rs#L116), [seal the learner](../../src/stream/keeper/sweep.rs#L117), [copy to the learner](../../src/stream/keeper/sweep.rs#L130), [install both survivors](../../src/stream/keeper/sweep.rs#L131) and [promote the learner](../../src/stream/keeper/sweep.rs#L135). |
| Replacement RPCs | [Recover a chunk](../../src/stream/keeper/sweep.rs#L163), [install it](../../src/stream/keeper/sweep.rs#L207) or [complete an empty copy](../../src/stream/keeper/sweep.rs#L223). [Seal the old roster](../../src/stream/keeper/sweep.rs#L237) and [retry the new roster](../../src/stream/keeper/sweep.rs#L240) on a split installation. [Await Replace](../../src/stream/keeper/sweep.rs#L271), [await Sync](../../src/stream/keeper/sweep.rs#L301), [await publication](../../src/stream/keeper/sweep.rs#L322), [check the expected reply](../../src/stream/keeper/sweep.rs#L332) and [receive the transport reply](../../src/stream/keeper/sweep.rs#L348). |


The storage change preserves the automaton's durable image. Physical WAL
rollover can split an entry across segments, and the shared checkpoint worker
publishes the complete boundary before removing covered files. Rust
regressions exercise cross-segment recovery and the pre-publication and
post-publication crash states. The trace checker still projects each keeper
effect and reopen to the same state. An isolated append continues to require
quorum acceptance before publication. The first-accept control reaches a
single local acceptance and checks that a read cannot expose it before a
takeover that adopts an empty history.
