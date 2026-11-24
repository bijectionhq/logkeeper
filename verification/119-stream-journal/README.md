# Study 119 · Stream journal

[Target journal](../target-journal.md) sections 2, 3 and 6 specify the contract,
the keeper protocol and the refinement mapping. This study checks when a
keeper acknowledgement can become visible to a caller. The
[expected results](EXPECTED.md) give the bounds, witnesses and controls.

## Lean refinement

[StreamJournal.lean](../lean/Logkeeper/StreamJournal.lean) uses arbitrary payloads
and histories, natural-number event indices and exactly three keepers. Its
ledger follows [PrefixAgreement](../lean/Logkeeper/PrefixAgreement.lean) and
[DurableAcceptor](../lean/Logkeeper/DurableAcceptor.lean).

| Ledger | Stream journal |
| --- | --- |
| Ballot | Epoch. Zero is an abstract bootstrap sentinel. Concrete epochs are embedded in the positive naturals. |
| Prepared | The two durable first seals selected for an election. |
| Report | The immutable snapshot from each of those seals. A same-identity retry preserves the election snapshot. |
| Vote | The durable history image at a complete Sync or a successful Append. |
| RankLE | Lexicographic order on the history's synced epoch and tail. Original entry epochs are ghost metadata. |
| Chosen | An exact history prefix covered by two durable votes at one epoch. |

Create, Seal, incomplete and complete Sync, synced floor installation,
Append of one or more records, publication, Trim, Check, Read and Delete
each have a keeper transition, matching the shipped keeper rules. An
incomplete Sync stages durable data and a floor; the keeper's view does not
change. Complete Sync publishes the history, its floor and a certified head.
A staged floor can skip positions the writer already trimmed; their ghost
records come from the seed. A delayed same-epoch complete Sync preserves the
published history. Publication raises the head to a certified cut within
the tail, with or without a retained record of the current epoch. Floor
installation advances a synced keeper over a trimmed prefix it never
received. Trim advances the floor and removes records from the retained
view. Delete can tombstone a stream the keeper never created. The proof
keeps trimmed records as ghost data for comparing histories across cuts.

1. A chosen cut extends the previous chosen prefix as the head
   advances. Taking the retained slice preserves contiguity and agreement
   on the positions still retained.
2. The seal winner contains every lower-epoch quorum choice, including a
   choice whose second old vote arrives later. When complete Sync certifies
   and publishes the adopted cut, a late lower-epoch quorum cannot extend
   beyond the seal result.
3. A fresh quorum Check samples a ready epoch. The earlier durable votes
   remain visible at the eligible observations. Quorum overlap and
   [Study 29](../29-read-index/ReadIndexProof.lean)'s cut argument put the
   returned LSN inside the invocation window and above all prior
   acknowledgements. The writer path covers the sampled tails with a certified
   result. The non-writer path takes their maximum and requires quorum
   head coverage. The cut argument uses observable single-record commit
   cuts, including the logical cuts within a pipelined write.
4. The append decision admits a fresh write at the next LSN for the sealed
   identity. An identical retained retry reports success without adding a
   record.
5. The serving keeper's head covers a certified prefix. A read at or above
   its floor returns exactly the requested slice of that prefix, including
   records below another keeper's floor.

The Lean execution supplies captured seal snapshots and quorum certificates
for advertised cuts. The proof derives the ledger rules from those
certificates and the keeper traces. A concrete witness creates, seals and
syncs two keepers, then chooses a record while the third keeper is empty.

[WALBridge.lean](WALBridge.lean) imports Study 117's SharedWAL source at
`logkeeper-k5/verification/117-shared-wal/SharedWAL.lean`. It specializes the
reply-survival theorem to stream keeper images. A covered frame survives
in the correct stream's recovered projection. The runner compiles Study
117's source into Study 119's results directory.

## TLC model and bounds

[StreamJournal.tla](StreamJournal.tla) uses a shared keeper reducer in six
scenarios. TLC explores each bounded program and its permitted interleavings.

| Scenario | Bounds |
| --- | --- |
| `rules` | One stream, one keeper, 25 requests, epochs 1 and 2 and two seal identities. Includes refused requests and retained retries. |
| `rank` | Three keepers, three epochs and one singleton suffix. An epoch-3 seal compares a stale nonempty history with a more recently synced empty history. |
| `protocol` | Two streams, three zones and one replacement identity. Two writer epochs, two records, one lost Append reply, one permanent AZ loss, one learner promotion, one delayed zombie request and one head invocation. The second append's voting pair, zombie recipient, invocation, round, samples, finish and optional shared-tail tear can vary. |
| `wal` | One keeper, two streams, at most four abstract frames and at most one pending frame per stream. A shared covering sync, replies and tears can interleave. |
| `handoff` | One stream, two epochs, three keepers and one record. The newer writer syncs the inherited suffix to two keepers before the older writer's delayed accept reaches the third. |
| `retention` | One stream, one epoch and three keepers. Two keepers trim the committed record. The third retains it and has one further accepted record. A read chooses one keeper and one of the two LSNs. |

The protocol tear occurs at the keeper that later holds the only live copy
of the first choice after AZ loss. The later tail has a frame for each
stream. The covered frames and their reply evidence survive. The learner
can vote after receiving the chosen prefix. Study 117's EmptyRejoin control
covers reusing a blank voter identity. Its covering frontier and stream
projection inform the WAL actions here. The frames represent already
decoded decisions. CRCs, quotas, authentication, runtime scheduling,
liveness and long-poll deadlines are outside these bounds.

## Specification probes

- **D03.** Loss of one of the two acknowledging zones leaves one survivor
  with the record. Both surviving keepers have it after recovery Sync.
  Immediate two-survivor coverage requires three copies before the reply.
- **Writer head after lost replies.** If the durable quorum is the commit
  point, a fresh same-epoch Check alone cannot justify returning a lower
  locally known index. The writer needs a certified cut that covers the
  observations, or can return `Unavailable`. If reply delivery defines
  the commit point, the design needs to reconcile that point with recovery
  from durable accepts.
- **Seal with an inherited speculative suffix.** The adopted cut must
  count as committed when seal returns. Reporting only the old advertised
  watermark can let a delayed lower-epoch accept extend the committed cut
  after the seal.
- **Trim and read routing.** A single keeper may return a retained record
  that a trim quorum already discarded. The retention witness exercises this
  read at the third keeper. `RetentionReadCommitted` compares returned records
  with the chosen history and rejects a read that exposes the accepted tail.
  The Lean proof derives the exact slice from that keeper's certified head.

Open details include below-floor retries after the comparison bytes are
discarded, propagation of floor and tombstones across keeper changes, and
reconstruction of inherited epoch runs from Sync's opaque payloads.
S07's deployment ACL and consumer takeover policy are outside this model.

## Run

```sh
python3 verification/119-stream-journal/run.py
```

The runner uses the existing Lean 4.35.0 package and the pinned TLC 1.7.4
jar. Use `--lean-only` or `--scenario protocol` for a subset. Pass
`--shared-wal /path/to/117-shared-wal` when Study 117 is in a different
checkout. The runner writes logs, generated TLC configurations and mutation
sources to the ignored `.results/` directory. A control must fail at its
designated theorem or invariant.


## Shared checkpoint boundary and append latency

The keeper's shared index changes the file-level representation of the
durable WAL prefix. The model's durable image and the WAL bridge's
per-stream projection still describe the same keeper effects. Study 119's
WAL actions model record and reply durability. The pack sync, index rename,
directory sync and covered-file unlink boundaries are exercised in the Rust
keeper regressions. Read and recovery bounds after replacement are unchanged.

An isolated append still accepts before publishing. In the bounded schedule
of three original keepers, two epochs and one position, epoch 1 delivers
the append to one keeper. A read from that keeper cannot return the record.
The other two keepers seal epoch 2 with an empty history and choose another
payload at the same position. The Rust witness reaches each step. Its
negative control publishes the append's tail on the first accept and the
read-visibility check rejects it.
