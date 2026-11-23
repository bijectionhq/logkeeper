# Study 92 · Fresh observation and exact read recovery

2026-11-23

## Verdict

Latest observation and exact recovery answer different questions.
A latest query can use one authenticated invocation-bound quorum read index and acquire local protection for the actual applied cut.
Retry after losing that response is a new observation with its own freshness interval.
An explicit recoverable invocation can reproduce its original result through a writer replacement only if the caller and current authority can identify and protect that original decision.
The two paths can share custody mechanisms.
The markerless path needs no per-invocation chosen journal record.

This split preserves exact protected reissue for callers that ask for it.
The reference applies it only to a latest observation or a new attempt using that contract.
A previously pinned transaction basis, a supplied historical basis and an ambiguous transaction commit retain their own semantics.

## Caller inventory

Source inspection used RTDB `f3be413735` and Bijection `4f7dc923b0d`.
This table describes the interfaces found at those revisions.

| Caller | What must stay exact | Existing behavior |
| --- | --- | --- |
| RTDB implicit latest snapshot | A valid latest cut for this observation, any prior await token, and any already pinned transaction basis. | `Session.pin` redeems the await token, then uses an explicit snapshot token or obtains a fresh basis. The placed fresh-basis path confirms the required replica read index and waits for application. Later statements in a read transaction reuse its pinned basis. See `rust/crates/node/src/{session,node,database}.rs`, `rust/crates/multi/src/logs.rs`, and `ServeOnSubscriber` in `allium/rtdb-multi.allium`. |
| RTDB explicit snapshot and historical read | The original basis already named by the caller and its authorized protection. | An explicit snapshot token bypasses fresh selection. A reopened read at a known immutable basis still needs retained storage and authorization. See `Session.pin` and `dev/doc/tx.allium`. |
| RTDB Flight SQL owned read | One exact applied present for a held handle and later witnesses scoped to that handle. | `open_owned_read_action` takes an empty body, reserves a bounded local slot, orders an empty present transaction via `reserve_ordered_present`, pins the exact catalog, and returns a newly minted handle. Subsequent point and range operations use that handle. The open request does not supply an original identity that can look up a lost first reply. See `rust/crates/flight-sql/src/owned_actions.rs` and `rust/crates/node/src/{session,node}.rs`. |
| RTDB placed transaction reconciliation | The exact original transaction attempt and its outcome or applied token. | The opaque token binds the original attempt. Redemption checks the exact outcome and waits for a recoverable closed-epoch frontier when needed. See `rust/crates/node/src/placed_receipts.rs` and `Node.redeem_placed_attempt`. |
| Bijection storage-engine boundary | An explicit world and basis, a durable protected reader where required, or the exact mutation receipt on retry. | `WorldStore.read` distinguishes latest from a named basis, and a collected basis refuses. The stock XTDB adapter uses an as-of basis. The contract describes ambiguous **mutation** reconciliation through an original receipt key. See `llm-wiki/wiki/storage-engine-contract.md` and `crates/native_store_runtime/src/xtdb/world.rs`. |
| Bijection warehouse Flight SQL transaction begin | The warehouse transaction identity named by the submission. | The gateway sends a submission ID as the begin mutation's key and receives a transaction handle. This ownership path is separate from the RTDB read-index and owned-read entry points. See `cli/internal/flightsqlserver/warehouse.go` and `cli/internal/actions/discovery/flight_sql_warehouse.go`. |

These paths show a useful place to split the Logkeeper reference.
The survey does not establish the product policy for every ambiguous protected-read creation at the Bijection gateway.
Retries of a side effect or of an already selected protected operation cannot automatically become new observations.

## General proofs

Lean 4.35.0 checked ten theorems using standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| Fresh admission performs an exact standing-gate transition for one authentic invocation, installed scope, applied ordered floor and current process session. | `fresh_observation_admission_is_one_exact_standing_gate_transition`, `a_late_process_or_foreign_scope_cannot_admit_fresh_work`. The floor and applied-view observations must be authentic for those meanings. |
| The acquired snapshot is a legal logical cut inside the invocation's interval. Its protected extents are resident. | `a_certified_latest_read_admitted_at_the_gate_has_a_linearization_witness`. This refinement uses Study 31's standing custody with an exact same-scope fresh round, certified applied choice and unit logical command cuts. |
| An admitted read keeps its own borrowed basis when the authorizer becomes unavailable. After effective stop it cannot finish. | `a_fresh_observation_keeps_its_exact_basis_through_authorizer_loss`, `effective_stop_excludes_later_fresh_result_delivery`. Custody is the existing standing transition system and exact stop is a physical premise. |
| Observations that look identical on recovery and had distinct original answers cannot both reconstruct the original. | `same_recovered_observation_cannot_supply_two_distinct_original_answers`. Evidence that survives failure must distinguish those histories if the operation promises exact recovery. |
| The explicit delivery preserves the original result and fails closed on a missing receipt. | `an_exact_retained_answer_survives_authority_loss_without_resampling`, `missing_exact_receipt_has_no_fallback_to_a_fresh_answer`. This is completion of already admitted delivery, under its original still-held borrow. Fresh authorization still uses the ordered rule from Study 87. |

The negative Lean mutation drops the current-session check.
Its necessity law fails at the check's projection.

## Comparative models

TLC 2.19 explored ten bounded reference configurations and obtained five safety counterexamples and two temporal ones.
The model has one initial data cut, at most one later data cut, a current ordered position and scope, one gate, and one read attempt on each side of a simulated lost reply.
Its temporal cases assume weak fairness of the enabled modeled transitions and the stated surviving routes and backing.

| History | Ordered reference | Split reference | Weakened design |
| --- | --- | --- | --- |
| Lost latest answer at data cut 1, installed replacement at cut 2 | A new latest observation returns 2 in 8 states. It uses one marker per observation in this model. | The same program returns 2 in 8 states. Neither observation needs a marker. | This program has no demand for recovery of the first answer. |
| Lost exact original result at cut 1, new scope at cut 2 | Reissues 1 in 8 states. | Reissues 1 in 8 states. | Fresh fallback returns 2 in 6 transitions. Forgetting the retained handle causes a temporal violation. |
| Retirement precedes invocation at the same data head | Previously checked by the ordered reference. | Refuses in 6 states. | Comparing only data positions admits after retirement in 5 transitions. |
| Gate closure or scope replacement after the round | The reference compares the local gate branch on the split path. | Refuses in 7 states for each race. | A cached gate or stale scope authorizes use in 4 transitions. |
| Exact reissue probes before an ordered close wins | Uses the ordered authorizer shared with the split path. | Refuses in 8 states. | A probe acting as exact reissue permission finishes the closed operation in 8 transitions. |
| Latest invocation overlaps retirement | Previously checked by the standing-custody reference. | A still-protected earlier cut is eligible under the current overlap policy. The configuration covers 8 states. | A different strict physical cutoff requires separate coordinating evidence. |
| Authorizer lost after the fresh borrow is admitted | Prior protection is independently held. | Completes in 6 states. | Requiring recontact leaves a temporal counterexample. |

The TLA+ work count represents chosen read-related decisions in these small paths.
It has no throughput or latency measurement.

## Amendments

Use [A364–A367](../amendments.md#study-92--2026-11-23) for the distinction between fresh observation, known basis and original-result recovery.

## Acceptance programs

1. Observe latest, lose that answer, advance the installed group, and invoke latest on a new call.
   Return a fresh applied cut at or beyond the new invocation floor using a live exact borrow.
2. Choose a protected result with an original invocation identity, lose its answer, replace the writer, and recover by that exact identity.
   Return the original result under its still-authorized custody.
   Missing original evidence refuses rather than sampling latest.
3. Race fresh proof with process or gate replacement and race exact reissue with an ordered close.
   Refuse both stale attempts.
   A protected operation admitted before authorizer loss can complete while its own borrow is still held.

## Residue

The proof composes a same-scope logical cut with a standing-custody transition and covers abstract exact retained completion.
A same-lineage membership transition and physical batch endpoints have separate proof obligations from Studies 29 and 30.
The candidate conservatively begins a fresh round on an incompatible scope change.
An adapter must bind its actual authenticated scope and local snapshot to both sides of the gate transition.
Bijection caller review must confirm where a fresh retry is acceptable and whether any exact open requires a caller-known identity and durable retry window.
Compare an atomic capture-and-first-use path against separate durable admission and reissue before adding more control machinery to exact handles.
The finite-window nonce alternative remains a separate candidate for independent exact invocations.

## Reproduction

From the Logkeeper checkout, use Python 3.13, Java 21 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/92-read-contracts/run.py
```

[run.py](run.py) records exact tool invocations, configurations and traces under .results/.
