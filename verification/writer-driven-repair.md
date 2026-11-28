# Automatic repair for the writer-driven journal

2026-11-28. Branch `writer-driven/repair`. This note extends `target-journal.md`
section 3, "Replacement". The keeper rules are unchanged. The change adds one
observation request, a repair process, writer ensemble following, and named
journal URL entries.

## The gap

The replacement protocol (`proposer/sweep.rs`) and `sweep_idle` exist, but nothing
nominates streams or runs them. Only the benchmark harness does. Active writers do
not repair their own streams either. `writer/recovery.rs` only runs election and
sync at seal, and a `Writer`'s ensemble per stream is fixed once bound. After a
sweep, an existing client keeps the old ensemble and gets `Unavailable` forever.
`TcpTransport::discover` accepted exactly three addresses and failed if any was
unreachable, so a client could not even start after a keeper loss, and could not
reach a spare.

## Decisions

1. **Who runs it.** A separate process, `logkeeper repair --config FILE`, using
   its own client certificate (for example `urn:logkeeper:client:repair`), listed
   in every keeper's `writers` and `clients`. It is an ordinary proposer and the
   S07 gate is the same as for any writer: only identities on the keepers'
   `writers` list can seal. It is not a duty inside keepers, because keepers never
   coordinate with each other and have no client identity. The process is
   stateless. It reads everything from the keepers on each pass, so a crash or
   restart needs no recovery. Run one replica. Two replicas are safe but can fence
   each other's sweeps.
2. **When a keeper is lost.** Either an operator declares it
   (`logkeeper repair --config FILE --lost UUID`, a one-shot pass that fails while
   any stream remains), or the daemon finds it unreachable for
   `repair_after_secs` (600 s by default, matching the consensus keeper). The
   probe is a `Check` of stream 0. Time only decides when to start a repair. The
   keepers accept or refuse the result by epochs alone, so a false declaration
   (for example during a partition) costs an unnecessary move but cannot break
   safety.
3. **Finding streams.** A new observation request,
   `List { stream: cursor, member, max }` → `Listed { streams: [(id, ensemble)] }`,
   returns, in pages of up to 4,096 in stream order, the live streams whose
   ensemble names `member`. It needs writer authorization and is never written to
   the WAL. The repairer asks every reachable keeper, so the survivors list the
   lost keeper's streams. A learner lists the ensemble it was created with, so a
   move interrupted after both survivors installed the new ensemble is still found.
4. **Choosing the spare.** The config lists every keeper with its zone, including
   spares. The repairer picks a keeper outside the ensemble in the lost keeper's
   zone, choosing among equal candidates by `stream mod n`. If that zone has none,
   it picks a zone neither survivor uses. Otherwise the stream reports `NoSpare`.
   If a survivor already names a learner in the lost slot (an interrupted move), the
   repairer resumes with that learner, because a different learner could never get
   past `WrongEnsemble` on the survivor that already moved.
5. **Epoch.** The repairer uses one more than the highest promise on the
   survivors, with a fresh proposal ID for each pass. If it is fenced by a higher
   promise, it retries above that promise, up to three times per pass.
6. **Writers and clients learn the new ensemble.** When a `seal`, `read`, `head`
   or `delete` returns `Unavailable`, the `Writer` checks the members of its
   current ensemble. If a voting member reports a different valid ensemble
   containing itself, the writer rebinds the stream to that ensemble, closes the
   old lanes and retries, following up to three moves. An active writer at the old
   epoch is fenced by the repair epoch, so its next append returns `Fenced`. The
   consumer re-seals at a higher epoch and the seal follows the move.
7. **Journal URL.** `logkeeper+tls://` now accepts three or more entries. An
   entry is either `HOST:PORT`, whose identity comes from the certificate and which
   must be reachable at startup, or `UUID@HOST:PORT`, which connects lazily and is
   checked against the certificate on first use. The first three entries are still
   the default ensemble, and later entries are spares the writer can follow to. A
   fixed three-address URL keeps working after a replacement only while all three
   addresses stay reachable, and it cannot reach the spare. Deployments should
   publish a URL with UUIDs and spares.

## Safety under races

The repairer adds no keeper rule. It is one more proposer of the protocol that
the Lean, TLA+ and Verus work already covers ("keeper replacement" and the
zombie writer):

- **At most one authority.** The repairer seals at a fresh epoch with a unique
  proposal. A writer at a lower epoch is fenced on any keeper the repairer has
  sealed. A writer that seals higher fences the repairer's later Sync, Append or
  Replace on that keeper. In that case the pass fails or retries above the
  writer, and the keepers decide which proposer wins.
- **No quorum on an old ensemble.** Replace needs the repairer's promise and
  completed Sync on the keeper. The repairer installs Replace on both survivors
  before the learner. While only one survivor has moved, the old ensemble has one
  voting member left that holds it (the other survivor, since the lost keeper is
  gone or a partitioned minority). The new ensemble also has only one, because
  the learner cannot vote. Neither ensemble can form a quorum until the repairer
  finishes. Test `a_writer_sealing_mid_replacement_cannot_split_the_stream` covers
  this window with a live writer sealing in it. If the "lost" keeper is actually
  alive, `{survivor, lost}` can still seal the old ensemble in this window. The
  repairer then seals both survivors at a higher epoch and adopts the higher
  `(synced, tail)` history, which contains everything that quorum committed,
  because any old-ensemble quorum intersects the survivor pair.
- **Committed records survive.** Any committed record is on two of the three
  members, so at least one survivor has it. The repairer picks the highest
  `(synced, tail)` history from both survivors, publishes it to both, and syncs
  the learner before any Replace.
- **Following cannot weaken safety.** The ensemble a writer follows only chooses
  which keepers it asks. Each keeper checks the ensemble on Seal and refuses a
  mismatch. A briefly wrong choice, such as flipping between ensembles while a
  move is half installed, costs only availability, and the follow limit bounds it.
- **No clocks.** Time decides only when the daemon declares a keeper lost.

## Liveness costs and open risks

- **Active streams.** Repairing an active stream fences its writer once. RTDB sees
  `Fenced` and takes the stream back through its S07 takeover path, which costs
  roughly one lease period (5 s) of write unavailability for that database. The
  consensus keeper moves streams without interrupting writers. A disruption-free
  alternative is a same-epoch replacement run by the writer itself under its own
  promise. Replace already permits that, but the writer would have to pause its
  append lanes, and that is not implemented.
- **Second loss.** With two members of one ensemble lost, the stream has one
  copy. Repair reports `Failed` and retries on later passes. It completes if the
  second keeper returns. Otherwise the only path is operator minority recovery,
  which acknowledges data loss.
- **Orphan learners.** If a repairer crashes after copying to a spare it would not
  choose again (because the roster changed), that spare keeps an unused learner
  copy, and its listing makes later passes re-check that stream (reported as
  `AlreadyRepaired`). Nothing deletes these copies yet.
- **Cost of a listing.** One `List` scans the keeper's stream map on the engine
  thread, which takes about O(streams) for each page of 4,096.
- **Extra follow round.** A follow adds one `Check` round to calls that fail
  with `Unavailable`.

## RTDB

RTDB needs no code change: `StreamJournal::connect` calls
`TcpTransport::discover(url)` followed by `Writer::new(transport, ensemble)`, and
the writer follows without the spare being in its keeper list. The deployment
should switch `journal_url` to the named form with spares, for example
`logkeeper+tls://UUID1@a:5448,UUID2@b:5448,UUID3@c:5448,UUID4@c2:5448`.
`DevelopmentStreamJournal::new` in `rust/crates/server/src/multi.rs` still
requires exactly three loopback socket addresses. It would need to accept named
entries and more than three entries for a development cluster with a spare.
