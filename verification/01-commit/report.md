# Study 01 report · Commit authority

2026-11-22

## Verdict

Both candidates satisfy the six checked invariants at both bounds in the shared finite model.
All fourteen deliberate variants violate their declared invariant, and all ten acceptance witnesses are reachable.
They share the requirement that the authority serialize durable decisions, including fences and ordering publication.
A one-round quorum commit remains the reference design for interactive latency.
The study compares safety and the existence of acceptance traces.
Latency and throughput require measurements.

## Properties and comparison

See the [brief](brief.md) for the checked interpretation of each property.
The model has one stream, two writer epochs, two distinct payloads, one staged append, and three AZs with up to one permanent AZ loss.

| Checked invariants | LSN bound | Quorum-first distinct states | Object-first distinct states |
| --- | ---: | ---: | ---: |
| All six hold up to the bound | 2 | 19,456 | 1,816 |
| All six hold up to the bound | 3 | 423,936 | 11,160 |

The counts are reachable states under the abstraction.
They measure neither implementation cost nor operational capacity.
Safety runs observe replies at emission and barriers at their authority observation, and committed history is append-only.
Acceptance runs enable extra observation state, including whether the first receipt arrived before AZ loss.

## Amendments and negative controls

TLC used one worker and breadth-first search.
Trace lengths count transitions after initialization.
Here `D` means the minimum data persistence required by the candidate, which is two `Persist` steps for quorum and one for object-first.
The [amendment ledger](../amendments.md) records the resulting rules.

| Amendment | Mutation | Named invariant | Shortest failing trace | Transitions, quorum / object |
| --- | --- | --- | --- | --- |
| A01 | `ignore_position` | `DenseHistory` | Stage LSN 0 → D → commit → stage LSN 0 again → D → commit. | 8 / 6 |
| A02 | `ignore_fence` | `Fenced` | Stage epoch 1 → D → install epoch 2 → commit the epoch 1 proposal. | 5 / 4 |
| A03 | `fence_omits_tail` | `ExactFenceCut` | Stage LSN 0 → D → commit → fence and report an empty prefix. | 5 / 4 |
| A04 | `single_vote` | `Recoverable` | Stage → persist in AZ 1 → commit → lose AZ 1. | 4 / — |
| A04 | `publish_before_data` | `Recoverable` | Stage → commit a reference to an object that has yet to be stored. | — / 2 |
| A05 | `reply_before_commit` | `ReceiptMatchesCommit` | Stage → D → acknowledge the proposal without a committed entry. | 4 / 3 |
| A06 | `retry_by_lsn` | `ReceiptMatchesCommit` | Stage value A → D → commit → answer success for value B at that LSN. | 5 / 4 |
| A07 | `barrier_by_held` | `ExactBarrier` | Stage → persist once → return cut 1 while the committed cut is 0. | 3 / 3 |

## Acceptance programs and developer cost

For a client, the two candidates have the same stream, writer, append, and barrier contract.
The durability operations below occur behind it.

| Requirement | Quorum-first program | Object-first program | Transitions, quorum / object |
| --- | --- | --- | --- |
| P01 | Use the installed grant and stage, replicate, commit, receive a receipt, and observe the committed cut. | Use the same grant and stage, upload, publish, receive a receipt, and observe the committed cut. | 6 / 5 |
| P02 | Commit with the receipt missing, install epoch 2, and resolve the identical request against committed history. | Publish with the receipt missing, then use the same reconciliation program. | 6 / 5 |
| P03 | Acknowledge a record, lose one AZ, install epoch 2, and commit a new record using the two surviving replicas. | Acknowledge a record, lose one AZ, install epoch 2, upload, and publish with the surviving authority. | 12 / 10 |
| P04 | Persist an epoch 1 proposal, install epoch 2, and keep the delayed proposal ineligible at its still-current LSN. | Upload the epoch 1 proposal and apply the same epoch check at publication. | 4 / 3 |
| P05 | Persist on one replica and return the current committed cut. | Upload the object and return the current committed cut before publication. | 3 / 3 |

## Residue

The implementation of a serializable, surviving authority is assumed.
This study neither establishes consensus correctness nor evaluates object-store failure contracts.
It abstracts membership and handoff between groups, actual durable media and process recovery, competing proposals, network invocation intervals, and concurrent streams.
A recovered payload is represented by its surviving durability evidence.
The P01 slice observes the cut and leaves actual read-back and application to a refinement study.
The P03 witness covers single-AZ continuation, with loss of authority quorum and progress under fairness left open.
No production Rust code or real deployment is checked here.

The next design studies should expose competing authorities during failed moves and the race between trim and replay admission.
The production audit can then trace guarded paths through the public quorum client, server dispatch, repair/copy entry points, and journal inspection.

## Reproduction

Run from the Logkeeper root with Python 3.13 and Temurin Java 21.0.13+9.

```sh
JAVA_BIN=/path/to/jdk/bin/java python3 verification/01-commit/run.py
```

The runner pins the [TLA+ tools 1.7.4 distribution](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4), SHA-256 `936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`.
That distribution reports itself as TLC 2.19, revision `5a47802`.
Each run writes its generated `Commit.cfg`, exact command line, and full output to `.results/<case>/`.
The tool is cached under `.tools/` inside the study.
