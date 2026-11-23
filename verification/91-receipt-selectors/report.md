# Study 91 · Bind terminal receipts to selectable recovery

2026-11-23

## Verdict

An already settled delivery can leave the same receipt in use by an older crash-selectable view or a borrower.
A selector becomes publishable once every newly needed receipt has both exact durable bytes and a durable name.
Each selectable root keeps that coverage through settlement, publication, crash and reopen.

Put the exact terminal evidence in the chosen settlement frame by default.
It then travels with the exact ordered suffix and needs no detached receipt at application.
A named receipt remains useful as a physical recovery witness for a still-outstanding terminal delivery.
Its lifetime follows the views and borrows that use it.
The older tail has its own lifetime even when no detached receipt is needed.

## Properties

Lean checked twelve theorems with standard axioms only over the typed rotation, arbitrary traces, and exact commanded replay.

| Property | Evidence and premises |
| --- | --- |
| Publication and every later transition preserve exact recoverable receipt names for all selectable views and exact borrow pins. | `every_trace_keeps_the_journal_and_exact_selector_receipts`, `successful_publication_requires_exact_bytes_and_name_for_each_new_receipt`. The policy enumerates each actual view's receipt needs and the media models the two barriers. |
| The old selectable view or an independent pin can block reclamation after logical settlement. | `old_selector_or_live_pin_can_keep_a_logically_settled_receipt`. Release of a pin denotes the last dependent use of the exact named copy. |
| A durable authorized receipt can realize the exact terminal obligation. The ready receipt plan cannot change the ordered result. | `a_named_attested_receipt_supplies_the_exact_terminal_witness`, `named_receipts_cannot_change_the_recovered_ranked_book`. Exact provider authentication and the correctly scoped original row come from the previously checked contract. |
| Any legal crash selector can read the exact suffix from its durable local frames, recover the chosen book, and apply a self-contained settlement. | `a_selected_root_reads_its_exact_suffix_including_inline_settlement_proofs`, `a_crash_choice_recovers_the_exact_chosen_book_with_its_named_receipts`, `replaying_a_self_contained_settlement_needs_no_detached_stop_receipt`. The base is certified for its exact cut, the receipt plan is bound to the view, and the supplied cutoff is the chosen valid history. |

The Lean control removes the durable-name conjunct from the receipt predicate.
The law requiring durable discovery fails at its proof step.

## Comparison

TLC 2.19 checked seven finite reference cases and seven comparison runs.
Each model starts with a valid older image and can publish at most one replacement before one cold crash.
The crash can select either available root while the selector change is unstable.
The reclamation scenarios assume weak fairness with selection eventually stable and no further crash.

| History | Reference result | Compared failure |
| --- | --- | --- |
| Replacement still needs a named receipt | Both crash outcomes reopen in 12 states under fairness. | Publish after bytes alone in 2 transitions or after foreign bytes under the name in 3. |
| Old basis needs a detached receipt and a raw tail | Both crash outcomes reopen in 16 states. | Logical clear alone drops a still-needed receipt in 1 transition. Visible-only collection drops it in 2. |
| Old basis can replay inline settlement with no detached receipt | Both crash outcomes reopen in 20 states. | Collecting the raw tail based on the new visible checkpoint strands the old selector in 2 transitions. |
| Old proof has an independent borrower | Both crash outcomes reopen in 26 states. | Ignoring the borrower drops its proof in 3 transitions. |
| Eligible collection after stable publication | Detached, inline, and borrowed cases reclaim under fairness in 6, 8, and 10 states. | Retaining every receipt stutters with an old proof after all requirements on it end. |

## Amendments

Use [A360–A363](../amendments.md#study-91--2026-11-23) for durable discovery, self-contained settlement, and independent collection.

## Acceptance programs

1. Stage the exact witness bytes and persist their name before publishing the replacement selector.
   Cut power before and after selector persistence.
   Recover the exact chosen book under either legal root.
2. Apply and checkpoint settlement while the previous root remains selectable.
   Preserve the receipt if the old path names it and preserve the old raw frame if the path replays it.
3. Leave an independent borrower after the previous root becomes unselectable.
   Allow file reclamation once that borrower releases the pin and both recovery choices can do without the file.

## Residue

The model checks the local selector protocol, exact replay and the typed receipt contract.
The complete checkpoint codec still has to produce the authenticated receipt plan and bind it to the selector and all relevant physical dependency claims.
The proof assumes the ready plan and complete role inventory from Study 90.
It abstracts the canonical wire encoding, signature rotation, real filesystem and object-store durability, exact pin aggregation, and physical byte and staging budgets.
The inline candidate is the reference because its chosen command is self-contained.
A detached candidate can also be sound if every reference in both roots, suffixes and active borrows remains durably accounted for.
This study makes no comparative latency or byte-amplification claim.

## Reproduction

Use Python 3.13, Java 21 and Lean 4.35.0 from the Logkeeper checkout.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/91-receipt-selectors/run.py
```

The [runner](run.py) records tool invocations, configurations and counterexamples under .results/.
