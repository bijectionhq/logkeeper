# Study 90 · Preserve the seal through physical delivery stop

2026-11-23

## Verdict

An exact, durably available stop receipt can satisfy the recovery obligation of an unavailable extent used exclusively by terminal deliveries.
The successor reopens the same authenticated sealed book regardless of which evidence it has.
Physical delivery still requires the original live borrow, and the current owner later clears the row through ordinary ordered settlement.
Keeping the full extent until that settlement can strand an otherwise ready handoff after both old routes disappear.

An extent can also back replay, a protected read, or a second delivery.
A stop affects only its own obligation.
Each still-required role and each crash-selectable recovery path must keep its own coverage before an extent can be disposed of.

## Properties

Lean 4.35.0 checked thirteen theorems over arbitrary finite delivery books and lists of selectable paths using standard axioms only.

| Property | Evidence and premises |
| --- | --- |
| An extent needed for the base or a protected read remains in custody. A shared delivery-only extent can be omitted only after exact durable evidence for every dependent delivery. | `coverage_keeps_replay_and_protected_reads_in_custody`, `a_shared_extent_needs_terminal_evidence_for_every_delivery_before_substitution`. The role predicates enumerate all needs, and named recovery verifies the complete manifest. |
| A terminal receipt for each affected delivery is sufficient for its share of coverage. An unverified or volatile receipt gives no coverage. | `exact_durable_stops_can_supply_the_delivery_only_portion_of_coverage`, `an_unproven_or_volatile_stop_cannot_replace_a_missing_delivery_extent`. The original provider verifies the exact lineage, delivery key and binding. Durable evidence is available to the selected recovery path. |
| Different ready physical realizations of the same immutable names recover the same sealed state. Exact local coverage permits the existing checked installation without source or provider recontact. | `mounting_recovers_exactly_the_named_cut_across_two_ready_media_realizations`, `exact_local_terminal_coverage_allows_activation_without_recontact`, `activation_does_not_consume_or_reissue_the_original_delivery_rows`. Installation admissibility and immutable naming retain their previous premises. |
| A terminal witness can drive ordered settlement, while reply completion still requires the original live borrow. | `a_durable_terminal_witness_cannot_authorize_a_stopped_reply`, `after_activation_the_same_proof_can_drive_exact_ordered_settlement`. The physical adapter enforces irreversibility of a certified stop. |
| Reclaiming the original extent requires post-disposal coverage on every selectable base, including one whose older delivery row still needs the proof. | `a_selectable_base_with_an_unsubstituted_replay_need_blocks_disposal`, `an_older_selectable_delivery_basis_needs_its_own_recoverable_receipt_before_disposal`. The caller supplies the complete set of selectable bases. |

The Lean control removes the guard for an independent base need.
The theorem excluding substitution for that need fails at its proof step.

## Comparison

TLC 2.19 checked thirteen finite reference cases and found the expected counterexamples in twelve comparison runs.
The scenarios place one original delivery under a sealed move and vary the surviving evidence and independently retained roles.
A live sibling is present in the shared-delivery case.
The source and provider each lose connectivity before activation.
The target then tests a reply, crashes and reopens if activation was possible.
Temporal runs assume weak fairness of the enabled modeled actions.

| Scenario | Chosen design | Shortest counterexample in the compared design |
| --- | --- | --- |
| Exact durable receipt, original extent unavailable | Activates, refuses the stopped reply, reopens, and settles in 10 states. | Requiring the extent or a new provider response stalls after `Seal → LoseSource → CustodyChanges → StageReceipt → LoseProvider`. |
| Prune at mount | Activation keeps the original chosen book. | Pruning the stopped row while mounting changes what activation installs at step 6. |
| Permit use from a receipt | A stop cannot reopen, including when the extent still exists. | Treating a receipt as physical authority emits a stopped reply at step 7. |
| No proof or volatile proof | Both reference cases stop before unsafe activation. | Accepting an in-memory receipt activates, then loses all recovery coverage at `CrashAndReopen` at step 8. |
| Reused slot, different pool, or foreign lineage | All three receipts are refused. | Checking only the slot accepts the wrong binding at step 6 in each case. |
| Shared with a protected read, base replay, or live sibling | All three retain the independent dependency. | Dropping the other owner's need admits an unsupported activation at step 6 in each case. |
| Older crash-selectable base | Reclaim is allowed in the case where the older path can also use the receipt. The case with no older-path receipt preserves the extent. | Checking only the visible path permits `DisposeOriginal` at step 6 and strands the older selector. |
| Unaffected original live borrow | Activates, replies and reopens from the still-covered extent in 9 states. | The comparison shares the same immutable cut and performs no terminal substitution for the live borrow. |

The exact-receipt case has the same ordered program as the original extent-retention design.
The difference is the recovery realization.
An alternative that carries a chosen, atomic settlement in its activation frame could define a different ordered program, but would introduce a new compound command with exact proof selection and replay rules.
This study rejects an unchosen mount-time clear and uses the existing settlement path.

## Amendments

Use [A355–A359](../amendments.md#study-90--2026-11-23) for terminal recovery evidence, shared dependencies and reclamation.

## Acceptance programs

1. Choose a funded delivery and seal the source.
   Stop the borrow at its original custodian and durably stage the exact receipt before losing that route.
   Activate after losing both old routes and the delivery-only extent.
   Reopen after crashing, refuse a stopped reply and apply the exact ordered settlement.
2. Substitute a recycled serial, foreign pool, foreign lineage, or volatile receipt.
   Refuse installation if neither valid receipt nor covered media is available.
3. Add an independent need for the same extent from replay, a protected read or a live sibling.
   Preserve that need even with the original exact stop.
4. Make an older recovery root selectable with the original row and no durable way to use its receipt.
   Refuse disposal.
   Once both roots recover with the extent absent, authorize disposal through the existing physical fence and accounting path.

## Residue

The reference separates historical decoding from durable readiness.
It treats receipt authentication, actual stable exhaustion of the physical borrow, name identity, local receipt durability, and complete dependency enumeration as premises.
A ready selector or install still needs to bind its exact durable receipt realization, including any older checkpoint or replay path that must understand it.
Keep the receipt charged while any selectable path needs it, and bound and verify its canonical representation.
The receipt supplies an alternative way to recover a terminal delivery obligation.
Media disposal remains subject to the provider's existing closing fence, durable publication and exact physical accounting.

If the old custodian disappears before the target obtains either usable media or durable exact terminal evidence, the target lacks the information needed to decide.
The modeled safety guard leaves it waiting.
The next refinement is the common checkpoint and ranked recovery path, so the same witness can be staged, selected, and retired through actual receipt and media transitions.

## Reproduction

Use Python 3.13, Java 21 and Lean 4.35.0 from the Logkeeper checkout.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/90-terminal-delivery-witness/run.py
```

[run.py](run.py) records tool invocations, configurations, and counterexamples under `.results/`.
