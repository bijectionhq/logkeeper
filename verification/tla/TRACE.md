# Consensus keeper trace validation

The fault harness records one NDJSON event stream per seeded cluster. TLC replays
it through [KeeperTrace.tla](KeeperTrace.tla). This follows the approach of
constraining a TLA+ execution with observations from an implementation run.
[Validating Traces of Distributed Programs Against TLA+ Specifications](https://arxiv.org/abs/2404.16075).

`KeeperTrace` uses the vote order and park match from
[LogkeeperProtocol](LogkeeperProtocol.tla) and the majority, lease and removed
voter rules from [EpochLeases](EpochLeases.tla). The three modules use
[KeeperSafety](KeeperSafety.tla) for these predicates. The bounded models
explore their own initial cuts and action interleavings. The replay starts from
empty replicas and consumes observed transitions, with extra state for disk,
lease adoption, application and offload.

Each nonterminal state has a successor only if the next recorded action is
defined and its guard holds. The only terminal loop is at the end of the
input. TLC's deadlock check therefore rejects the first invalid event, and
acceptance means the entire projection is a finite behavior of `KeeperTrace`.
A TLC parse, evaluation or infrastructure error also fails the command and
is reported separately. The CI test mutates passing traces and requires
rejection at the modified event.

## Observation map

| Keeper observation | Replay state and model correspondence |
| --- | --- |
| WAL boundary selects a vote | Replica `vote`, with the partial order in `LogkeeperProtocol.VoteLeq`. Committed votes agree on the leader within each observed term. |
| WAL boundary selects append, truncation or ownership changes | Replica `log` and generation resets. Appends are complete batches. Shared indexed terms require matching overlapping prefixes. A normal rewrite preserves previously applied entries and the durable commit cut. |
| State machine applies an entry or WAL selects a commit cut | `appliedIdx` and `commitIdx` from `LogkeeperProtocol`, with separate watermarks for application and durability. Applied entries must agree at an index within each recovery era. |
| Snapshot selected, built, installed or used to purge | `snapIdx` and the suffix base. Snapshot selection is monotonic, a local build covers applied state, and a purge must be covered by the selected cut. |
| Follower accepts a park request, group closes or reopens | `groupState` and the exact vote and applied-tip test of `ParkStream`. Closing preserves durable state. |
| Holder adopts a lease, observes lapse, or evaluates an authority gate | `lease`, `myEpoch`, `catEpoch` and `catFenced` from `EpochLeases`. The adapter carries the recorded duration, margin, media incarnation and local fence floor. A fenced earlier configuration cannot pass the authority gate after recovery activates. |
| Catalog applies enrollment, lease policy, fence or recovery | Catalog actions are deduplicated by committed catalog LSN. Recovery changes the target, fencing and epoch state together. A writer-named recovery also fences the other survivors until their copies finalize the new revision. |
| Offline keeper waits, selects a recovery WAL record, then applies the typed marker | `Recover`, `wait`, `recTerm`, `survHist` and `reportedHead` from `EpochLeases`. The replay checks the recorded wait against the longest fenced lease, the exact cut and loss point, the term bump, and the marker's epoch, position and consistency. |
| Object upload completes, then an offload progress command applies | A contiguous uploaded interval comes from a committed head. Replicated progress has upload evidence for newly covered retained positions, stays within the head, and constrains the local retention floor. |

The capture is scoped to a temporary cluster and compiled with `cfg(test)`.
A WAL round emits only after its durable boundary is selected. That includes a
round interrupted after selection and excludes one interrupted before it. The
harness event order uses in-process synchronization. Raft indices are shifted
by one to reserve zero for an absent cut, and full Raft terms are encoded as
four 16-bit digits for TLC. Command digests omit replica-local admission
tickets. The harness separately checks client linearizability, convergence and
offloaded payloads.

The replay trusts OpenRaft's quorum decisions and the snapshot decoder. It
observes storage and application transitions, so it has no complete history
of RPC sends, vote replies, effective joint-quorum certificates or snapshot
bytes. Applied agreement is observable where entries pass through application.
The symbolic drift and partition interleavings remain in `EpochLeases`; the
adapter checks observed holder clocks and recovery wait windows on one host.
A passing finite trace gives evidence for that run and the guards in this
projection.

## Running

Use Python 3, Java 17 or later, and the Rust toolchain in the repository.
The runner fetches and verifies the same pinned TLC jar as `check.sh`.

```sh
LOGKEEPER_TRACE_CI=1 LOGKEEPER_CONSENSUS_LEASES=1 \
  cargo test --locked --features stream --lib consensus_trace_ci -- --nocapture

LOGKEEPER_CONSENSUS_LEASES=1 LOGKEEPER_TRACE_SEEDS=24 \
  cargo test --locked --features stream --lib consensus_trace_soak -- --ignored --nocapture

python3 verification/tla/check_traces.py path/to/seed.ndjson
```

The Linux test workflow runs the CI case. It requires event coverage across
four traces and preserves rejected inputs. The soak varies all seven profiles
and streams with three and five voters. Set `LOGKEEPER_TRACE_FIRST_SEED` and
`LOGKEEPER_TRACE_SEEDS` to select its range. The harness finalizes liveness
leases before starting the workload in either case. A failed run keeps the
NDJSON inputs in the directory it prints. Set `LOGKEEPER_TRACE_OUTPUT` to
place those inputs beneath a particular directory. Each TLC attempt removes
its temporary state directory, optionally placed under `LOGKEEPER_TLC_SCRATCH`.
