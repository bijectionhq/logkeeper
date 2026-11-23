# Ordered object withdrawal (L7)

The area includes the shipped admission, retained-reference scan,
fresh-withdrawal decision, and fence insertion from `src/ordered/object_withdrawal.rs`. The reducer uses
these functions for append and checkpoint preparation, and for the
`WithdrawObject` arm. Snapshot validation uses the same admission gate.

| Lean reference | Rust projection and Verus law |
| --- | --- |
| `Logkeeper.ObjectWithdrawal.fenced` and `canAdmitReferences` | The domain of the actual fence map is the set of fenced names. `fenced_refuses_reference` checks an arbitrary fenced member of a canonical list. `fenced_refuses_opaque_references` checks the empty-domain requirement for opaque lists. |
| `Logkeeper.ObjectWithdrawal.referenced` and `canWithdraw` | The adapter projects a name as referenced if a retained root, preparation, held root, or retained replay record includes it. Root, preparation, and hold lifetimes are represented in the root-reference table. `referenced_refuses_withdrawal` checks that a live reference or incomplete inventory blocks a fresh withdrawal. |
| `Logkeeper.ObjectWithdrawal.State.fence` and `order_preserves_fence` | A map entry preserves the immutable name, exact provider version, and decision coordinates. `withdrawn_name_stays_fenced` checks fresh refusal or insertion and a later admission attempt for that name. `retry_withdrawal_matches_version` checks exact retry without rewriting the fence. |

Verus uses the standard map and ordered-key model. The Rust adapter uses
lexicographic ordering of 32-byte names, checks canonical lists, derives
the live-reference and inventory-completeness observations from `State`,
and provides funding and receipt coordinates before insertion. The proof
checks traversal of the root-reference map and retained record queue. It
takes the per-row membership test on sorted names as a projection.
The State projection, the completeness of provider names supplied by
callers, and byte-level compaction and repair refinement remain separate
obligations.

The Lean `Trace` theorem ranges over arbitrary finite sequences of
multi-object transitions, including compaction and repair with a
`Carries` premise for exact references, opaque status and fences.
The witness changes both the compact image and the cohort while one
name stays fenced and a distinct name stays referenced. Lean controls
show that a dropped fence reopens a name and omitted references can
authorize withdrawal. Verus mutations also omit either reference source,
permit withdrawal against an incomplete inventory, or weaken the exact
version check. The existing native
`exact_object_withdrawal_survives_compaction_and_cohort_repair` test
exercises the encoded, installed path.
