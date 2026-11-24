# Asynchronous stream journal refinement

Two reachable keeper effects cannot be a step or stutter of Study 119 under
its linked keeper projection. Both use the current promise and preserve the
committed payloads. The disagreement concerns when the keeper exposes its head
and tail. [Study 119](Logkeeper/StreamJournal.lean) · [Lean proofs](Logkeeper/StreamAsync.lean)

1. **Publication after takeover.** A keeper holds an epoch-1 record at LSN 1
   with head 0. The next writer seals and completes Sync at epoch 2 while
   retaining that record and its epoch. The writer's empty Append publishes
   head 1. Study 119 can raise a keeper's head on an append or retained retry.
   The former would extend the history and the latter would require a retained
   epoch-2 record. The Lean witness constructs the prior state from `initial`
   and proves both step and stutter impossible. A companion witness projects
   a publication with a retained record from the current epoch.
   [Recovery](../../src/stream/writer/recovery.rs) · [Keeper effect](../../src/stream/keeper/state.rs)
2. **Incomplete Sync.** The keeper applies a recovery chunk and exposes its
   new tail while retaining its last completed `synced` epoch. Study 119 keeps
   the incomplete image in `staging` and derives its visible tail from the
   last accept. A later Seal can report the concrete intermediate tail for
   recovery ranking. Lean proves that a change to the tail at the same synced
   epoch cannot project while the promise is ahead of `synced`.
   [Keeper effect](../../src/stream/keeper/state.rs) · [Seal and Check rules](../../src/stream/keeper/rules.rs)

The 10,000-seed simulator corpus has one stream, three initial keepers,
one optional replacement identity, two writer identities and an observer.
It includes at most one disk loss per run. The inherited-publication Lean
witness uses two modeled epochs, one record and a six-step path to its prior
state. The impossibility lemmas allow arbitrary payloads and history lengths.
The checked axioms are `propext`, `Classical.choice` and `Quot.sound`.
[Simulation bounds](../simulation/README.md) · [Lean proofs](Logkeeper/StreamAsync.lean)

## Shipped effects and proof boundaries

| Await or effect | Reference correspondence and remaining work |
| --- | --- |
| Writer mutation lock, promise requests and seal replies | The mutation lock serializes elections, trims and deletes on one handle set. A seal gathers two eligible replies, fixes its recovery choice, starts lanes and waits for readiness and publication. Study 119 derives prefix agreement given the elected pair and immutable saved snapshots. The link covers seal admission and recovery rank. Reply provenance, preserving the chosen election on cancellation, and treating a later same-epoch Seal reply as a saved snapshot remain open. [Writer](../../src/stream/writer/mod.rs) · [Recovery](../../src/stream/writer/recovery.rs) |
| Recover chunks, Sync chunks, completion and floor installation | The selected keeper serves the retained accepted suffix under the promise. A fallback keeper must report the same original record epoch. A lane awaits each Sync and skips ranges already carried by the target. The reference needs an explicit observable intermediate image and a link from that image to recovery ranking. The proof of exact payload and epoch-run reconstruction across fallbacks also remains open. [Recovery](../../src/stream/writer/recovery.rs) · [Keeper decisions](../../src/stream/keeper/rules.rs) |
| Append lane wake, dispatch, durable replies, retries and publication | Each lane awaits one operation and updates its accepted and published positions. The decision link checks the chosen quorum for one epoch and position. Append acknowledgement also waits for publication. A separate empty Append publication step and a derivation of the two certificates from distinct durable replies remain open. [Append lanes](../../src/stream/writer/append.rs) · [Decision link](../link/README.md#stream-journal) |
| Writer and observer head rounds | Pending callers are detached when a round opens. An active writer can use an append issued after that cut, then covers the sampled tails and awaits publication. An observer retries fresh Check rounds until one has enough same-epoch head coverage or times out. Study 119 proves the cut result given a confirmed fresh round, durable opening quorum and covered samples. The derivation of these facts from the actual lanes, watches and replies remains open. [Head rounds](../../src/stream/writer/head.rs) · [Cut theorems](Logkeeper/StreamJournal.lean) |
| Read fallback, chunks and long-poll wake or deadline | A writer requests a page from one keeper at a time. The first chunk fixes the returned head. A keeper can requeue a read after a watch notification or timeout. Study 119 proves exact slices from a certified keeper head. Assembly across chunks, cancellation and choosing a floor after fallback remain open. [Reader](../../src/stream/writer/read.rs) · [Keeper call](../../src/stream/keeper/mod.rs) |
| Trim and delete | Trim requires quorum head coverage, established before sending or by the successful Trim replies. The writer advances its floor after two replies. Delete broadcasts to the ensemble and waits for two acknowledgements. Each keeper defers its delete reply until WAL rotation finishes. Study 119 models a monotone floor and a terminal tombstone. Durable floor installation, delete before local Create, broadcast cancellation and quorum deletion remain open. [Writer](../../src/stream/writer/mod.rs) · [Keeper rounds](../../src/stream/keeper/mod.rs) |
| Replacement | The sweeper seals both survivors, copies and publishes the selected history, syncs the learner and replaces both survivors before promoting the learner. Verus checks the local one-member-change guard. Study 119's Lean model has one fixed roster. Authority across split installs, retry and one disk loss remains open. [Sweeper](../../src/stream/keeper/sweep.rs) · [Replacement model bounds](../119-stream-journal/README.md) |
| Keeper queue, WAL rounds, rotation, crash and reopen | The keeper finishes buffered entries and covers each round with a sync before returning ordinary replies. Delete replies wait for rotation. The simulator cuts selected unsynced writes and reopens the shipped WAL. A model needs to connect decision order, incomplete fragments, crash-adopted complete entries, the durable reply boundary and checkpoint selection. [Keeper rounds](../../src/stream/keeper/mod.rs) · [WAL](../../src/stream/keeper/wal.rs) |
| Transport delay, duplication, cancellation, loss and writer crash | A timed-out call or dropped future may leave dispatched work running. The simulator delivers delayed and duplicate complete requests independently of replies. A full model needs request provenance across pending futures, writer loss and epoch replacement, and a correspondence from authenticated byte exchanges to typed packets. [RPCs](../../src/stream/writer/mod.rs) · [Simulation network](../../src/stream/keeper/simulation/network.rs) · [TLS transport](../../src/stream/transport.rs) |

The correspondence inventory marks `sync_head_valid` and `may_replace` as local
Verus laws awaiting a Lean link. An observer round can also open before the
epoch in its samples has installed any quorum. Connecting that round to
Study 119's opening-cut premise requires cross-epoch evidence. [Link inventory](../link/inventory.md#stream-journal) · [Observer rounds](../../src/stream/writer/head.rs#L116)

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

## Replay

```sh
python3 verification/lean/run_stream_traces.py
```

The recorder captures actual keeper state before and after successful empty
Append and incomplete Sync requests. The Lean checker checks the promise,
identity, position and head bounds, retained epoch runs for publication, and
the observed state changes. It reports occurrences of both projection
obstructions. The runner replays each obstruction in strict Study 119 mode
and expects rejection at the named projection check. It also mutates the
captured rows to exercise independent admission and effect checks. The other
RPCs, failed calls, WAL bytes and writer state remain outside the exported
projection. [Recorder](../../src/stream/keeper/simulation/network.rs) · [Checker](Logkeeper/StreamTrace.lean)

The full I/O automaton, the derivation of Study 119's quorum premises from all
reachable actions, and the end-to-end contract theorems remain open. The
consumer still applies records through the head returned by `seal` before
serving. [Specification](../target-journal.md) · [Conformance obligation](../../contract/src/conformance/mod.rs)
