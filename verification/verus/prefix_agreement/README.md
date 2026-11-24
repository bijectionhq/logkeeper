# Ordered prefix agreement

[The harness](proof.rs) imports the [shipped local rules](../../../src/ordered/replication/rules.rs) and the [shipped vote recorder](../../../src/ordered/replication/evidence.rs) shared with [rotation slot evidence](../rotation_slot_evidence/README.md).
[The laws](laws.rs) check the pure decisions called by the durable voter, the coordinator, and cohort transfer.
The [manifest](area.json) runs the production and law modules and mutates shipped code and its contract so each control reaches its named law.

| Shipped entry point | Verus law | Lean reference and representation |
| --- | --- | --- |
| `Inner::prepare` via `depose_prepare` | `promise_only_advances_above_floor` | `DurableAcceptor.PrepareAdmitted` and `prepare_or_retry_is_step`. A prepare at the existing floor acknowledges a retry. The abstract floor advances only on a strict increase. |
| `Inner::accept` via `accept_ballot` | `accept_at_or_above_promise` | `DurableAcceptor.AcceptAtPromise` and `accept_at_promise_is_step`. The current promise must equal the proposed ballot. |
| `Group::confirm` via `record_vote` and `configured_majority` | `chosen_votes_bind_ballot_voter_and_image`, `majority_is_strict`, `majority_counts_only_configured_voters`, `majority_counts_each_voter_once` | `PrefixAgreement.Chosen` and `JournalRefinement.Majority`. `distinct_configured_votes_are_majority` relates the native list lengths to the model's count over the roster. `PrefixTrace.checked_certificate_is_chosen` introduces `Chosen` from this quorum and its exact votes. |
| `Group::prepare` via `choose_base` and `recovery_choice` | `winner_dominates_observed` | `PrefixAgreement.WinnerDominates` and `RankLE`. The fold keeps the higher ballot of each pair. On an equal ballot the caller requires exact prefix equality, so the reference's secondary history-length comparison ties as well. `rank_trans` composes successive comparisons. |
| `Group::repair_seed` and `Group::install_seed` via `seal_image` and `install_image` | `sealing_carries_exact_predecessor_image`, `installation_carries_exact_predecessor_image` | `JournalRefinement.ExactImage` and `Protocol.Transfer.exactImage`. Sealing returns the selected state for its named successor. The adapter changes the voter scope and clears the predecessor seal before encoding. Installation returns the exact authenticated base field when source and destination match, and `DurableVoter::initialize_repaired` uses it as its initial accepted prefix. |

`PrefixAgreement.ballotRank` maps `(round, nonce)` to `round * 2^128 + nonce`; `ballot_rank_order` proves the lexicographic comparison used by the shipped rules.
UUIDs map to their big-endian `u128` values.
A missing native floor maps to zero; native ballot admission requires a nonzero round and nonce.
The certificate compares the actual candidate's scoped digest, authenticated voter UUID, ballot, mirrored-slot result, and requested read-back flag.

Run from the checkout root.

```sh
tools=/Users/sachaichbiah/code/codesign-agents/tools
python3 verification/verus/run.py --verus "$tools/verus" prefix_agreement
python3 verification/lean/run_prefix_traces.py
```

The trace runner uses the native `simulation` feature to instrument the three existing ordered-group tests and two ordered scenarios in the leadership and fault suites.
Those two suites also exercise the legacy protocol; that protocol has a separate recovery contract.
The traces contain durable promises, their reports, a coordinator's prepare quorum and winning report, proposals, durable accepts, choices, restart selections, predecessor seals, and installed bases.
The recorder interns exact decision frames and exact physical images by byte equality.
It reconstructs a compact image's logical history from its position and command-history commitment using the frames observed during the execution.
For repair it independently encodes the selected state with the successor's metadata and compares those bytes to the installed media's base.
The [Lean checker](../../lean/Logkeeper/PrefixTrace.lean) checks each event and the agreement of the resulting choices.
The native fault scenario adds a stale accept to its recorded stream and the runner also substitutes the predecessor base in a recorded installation.
Both controls require the named rejection at the exact injected event.

The local proofs use the authenticated endpoint and digest-binding contracts.
Each `Replica` instance represents one configured voter with a stable UUID throughout a round.
Trace validation covers the recorded executions, including one lost accept and a warm restart after a newer prefix reached only one voter.
The [asynchronous group model](../../lean/async-group.md) projects each modeled action to these reference definitions. It describes the remaining Rust action boundaries, including executor cancellation, the Promise and image projections, and filesystem effects. The native trace runner can also generate seeded fault schedules.
