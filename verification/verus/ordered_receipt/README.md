# Ordered receipts and D01 retry

The harness imports [receipt persistence and replay](../../../src/ordered/receipt.rs)
and [fingerprint comparison and receipt retention](../../../src/ordered/admission.rs).
In the applied path, `State::apply` creates a receipt from the returned
`State::decide` result and passes that same value to insertion and the caller.
The insertion law checks that the exact receipt and fingerprint are stored at
the authenticated principal and request identity. A refused mutation can be
recorded with its refusal. A refused barrier leaves the receipt book unchanged.
The verifier uses the standard Verus model for
[ordered Rust map keys and updates](https://github.com/verus-lang/verus/blob/9da409bde488f7e8c74c66116249d817629f96fa/source/vstd/std_specs/btree.rs).

## Lean correspondence

| Verus definition or law | Lean reference in [Logkeeper.Protocol.Ordered](../../lean/Logkeeper/OrderedReceipt.lean) |
| --- | --- |
| `abstract_book` | `abstract_book` projects each `State.outcomes` row by its `(principal, RequestId)` key into its request fingerprint and exact original receipt. |
| `replay_mutation`, `replay` | `replay_mutation` and `replay`. The original outcome is reused only after exact fingerprint equality for a mutation. |
| `record_after_apply`, `retain_applied` | `record_after_apply` and `retain_applied`. Positive stored outcomes equal the successful applied result. |
| `retains_receipt` | `retains_receipt` uses the applied decision position and the invocation's exclusive expiry, with the live-hold exception. |
| `recording_uses_the_applied_outcome` | `positive_receipt_is_applied` and `refused_barrier_leaves_no_receipt`. |
| `mutation_retry_exact` | `mutation_retry_exact`. The Lean theorem `reissued_append_identifies_chosen_append` composes this rule with `Protocol.same_chosen_append` under its chosen-prefix premises. |
| `reconciliation_requires_original_placement` | `original_placement_matches` compares the original append placement to the installed reducer placement. |
| `expired_request_cannot_admit_fresh_work` | `fresh_request_expired` uses the exclusive expiry after the exact retained-receipt path. |

The book projection preserves the authenticated scope, exact original applied
position, and returned outcome. Deployment and incarnation encode
`Protocol.Placement`. For a positive append, principal and nonce identify the
`Protocol.Attempt`, the fingerprint gives its `requestDigest`, and
`AppendResult.cut` gives its `DataCut`. The retry horizon uses the numeric
decision coordinate in `Protocol.AppendReceipt.expiresAt`. The proof leaves
chosen-ledger membership, the decision-cut digest, and the canonical
outcome encoding to separate obligations. Hash security and canonical request
encoding supply the relationship between digest equality and request equality.

`State::apply` takes the keyed lookup before command execution. A prior outcome
is either replayed exactly or produces a conflict. Barriers cannot replay from
that lookup. They can retain an admitted receipt as hold provenance.
`State::retained_receipt`, used by replication before submitting a decision,
checks the Barrier variant and placement before calling the same mutation
replay implementation. The expiry sweep and the three release and disposal
paths share the verified removal operation.

The classification of concrete commands, the expiry index and live-hold
invariants, and the dispatch and fast-path call sites were inspected in Rust.
Their whole-reducer proof remains open. Snapshot restoration and
replication's confirmation of the chosen prefix are separate obligations.

The controls try to replay a barrier, compare only fingerprint lengths, evict
too early or too late, lose live-hold provenance, insert a refused barrier, and
skip an applied insertion. The shared
[correspondence check](../../lean/run_ordered_correspondence.py) compares Lean
evaluation with Verus specs on retry and recording cases.

`use-success-for-refused-mutation` changes only the recorded outcome, substituting an earlier success for a refusal. It fails the exact insertion postcondition of `record_after_apply`.
`accept-foreign-original` drops only the original placement check in `State::reconcile_append`.
`admit-at-expiry` lets a fresh decision use an identity exactly at expiry, where the remaining retry-horizon arithmetic still fits.
