# Study 94 · Spend standing read credit at choice

2026-11-23

## Verdict

Give the installed journal prepaid physical supply with a bounded original-provider serial range.
Assign the lineage-wide delivery serial and the exact physical borrow only when the journal chooses the read.
This avoids a gap in ordered delivery caused by an old provider that staged a per-request serial and then disappeared before the journal learned how to reconcile it.

A newly funded window can serve without taking over the old physical charge.
The retiring window's fence names the exact delivery book at retirement, including choices its provider may have missed.
Keep original funding until every required exact assignment has settled.
A durable window generation prevents an older funded window from reopening after an intervening replacement.
Ordinary append and the split-read path can continue under their own admission conditions when fused-read coverage is unavailable.

This resolves the per-request preparation dependency in the candidate.
The split program remains the reference until the standing charge and rotation cost are qualified.

## General proofs

Lean 4.35.0 checked eleven theorems with standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| Every assigned borrow receives a serial within its original custodian's prepaid range. Disjoint physical ranges cannot alias. | `issue_uses_the_original_pool_and_only_its_prepaid_range`, `disjoint_provider_ranges_cannot_issue_the_same_borrow`. The provider must reserve each slice exclusively against its own durable allocator, including ranges no longer current in this journal. |
| Preparation does not take a lineage delivery serial. A successful chosen open advances the delivery and physical cursors together, retains the exact original-provider borrow, and checks the chosen basis. | `physical_preparation_does_not_reserve_a_delivery_serial`, `a_successful_choice_advances_both_cursors_and_keeps_the_original_borrow`. The choice invokes the guarded atomic capture from Study 93. The paid window authenticates the exact lineage and installed placement. |
| The chosen cursor stays within its reserved range. Exhaustion refuses before changing the read nonce or consuming a delivery. | `one_reserved_range_can_pay_only_its_bounded_number_of_chosen_operations`, `exhausted_standing_allowance_refuses_before_spending_the_read_nonce`. Per-use storage still needs its separate bounded delivery slot and valid frame. |
| The installed authority can adopt a new exact funded window while preserving the delivery book. Installing an older or equal generation refuses. | `installation_carries_the_old_book_and_needs_only_the_new_paid_window`, `a_window_at_or_below_the_installed_watermark_is_never_reinstalled`. The prior authority and updated generation must be recoverable from the exact chosen state. |
| The window switch exports a freeze of the actual chosen book at the same ordered position. The original can only refund under authentic closure and exact terminal evidence for its outstanding assignments. | `replacement_fences_the_old_window_with_the_exact_delivery_book`, `provider_silence_cannot_refund_a_hidden_chosen_delivery`. An already cleared row must have used the normal terminal settlement contract. |

The Lean controls drop the range exhaustion check and the installation watermark check.
Each fails its corresponding necessity law at the designated proof step.

## Comparative models

TLC 2.19 checked five finite reference configurations and reproduced five safety failures and two temporal failures.
Each history uses one move and one serving window per side.
The choice, its notification to the original provider, and original settlement are separate actions.
The orphan configuration assumes the comparison protocol requires reconciliation of its earlier externally reserved serial from the now unavailable provider.
It supplies no portable ordered fence that could resolve that reservation in the successor.
Progress checks use weak fairness over the enabled modeled actions.

| History | Outcome |
| --- | --- |
| Already funded successor while the original provider is unreachable | The reference finishes in 7 states. The preparation-ordered serial variant stalls after activation. Rebinding the old physical allocation to the new delivery violates scope in 5 transitions. |
| Original choice was hidden from its provider before sealing | The reference preserves the old debit while the new window can serve, in 16 states. Either refunding from the provider's empty observation or dropping the assignment from the seal violates original custody in 5 transitions. |
| Original paid extent fills the pool | The reference waits for original disposition before staging the optional replacement and finishes in 11 states under reachable settlement. Ignoring old and new overlap exceeds capacity in 5 transitions. |
| Original paid window returns after a replacement | The reference ignores the older generation and finishes in 10 states. Dropping the watermark check reopens the old window in 5 transitions. |
| New basis has no fused-read credit | Ordinary work and a separately supplied split read complete in 10 states. Requiring optional credit to publish or advance ordinary work stalls. |

An early-serial design with a durable authoritative preparation record and a portable exact cancellation can avoid the modeled orphan.
That alternative has to pay for persistence and recovery of preparation.
Allocating the delivery serial at choice removes that dependency from this path.
Standing funding still needs adequate headroom for overlapping retained and new allocations.
This study does not compare throughput or resource cost at production sizes.

## Amendments

Use [A373–A377](../amendments.md#study-94--2026-11-23) for assigning from standing funding, window non-reuse, and keeping optional funding out of the common write path.

## Acceptance programs

1. Stage old preparation, lose its provider before learning any result, install the successor and its already paid current window.
   Open and complete a new first delivery without recontacting the old path.
2. Choose and retain an original borrow that the provider has not yet observed, then switch windows.
   Preserve that exact row and original debit.
   Use the successor's distinct paid window for new use and permit old refund only after authentic exact settlement.
3. Reoffer the original window after a successful rotation.
   Refuse reuse even if its original receipt and original custody still survive.
4. Publish or append with optional funding exhausted.
   Use a separately funded ordinary or split path, and refuse an unfunded fused open.

## Residue

The model separates paid original-provider range ownership from the installed choice that spends it.
It assumes authentic complete original scope and basis coverage, global non-overlap in the physical allocator, and verified original provider disposition.
The checked window switch uses already installed core writer authority.
An integrated implementation needs authenticated window history and cursor recovery in the named checkpoint and chosen handoff, and original provider application of the chosen assignment and fence.
Measure how many closed windows and live borrowers can remain charged under realistic skew before choosing a range size.
Prove pooled staging, turnover and returned-charge bounds before adopting fusion as the default.
[Study 95](../95-standing-read-recovery/report.md) adds the checkpoint and seal recovery comparison.
It requires the cursor itself, including its fully spent value, to fit the fixed-width field.

## Reproduction

From the Logkeeper checkout, use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/94-standing-read-credit/run.py
```

[run.py](run.py) records the pinned verifier commands, configurations and traces under .results/.
