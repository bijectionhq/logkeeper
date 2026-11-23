# Study 96 · Settle standing credit at its original provider

2026-11-23

## Verdict

The original provider installs the exact recovered delivery book as the window's fence.
That set can contain a chosen operation the provider never observed.
An authenticated operation in the frozen set can still start while its original charge is live and its exact serial remains unused.
An unlisted operation refuses, and a terminal operation cannot restart or take an effect.
Installing the fence preserves the provider's existing operation state.

Refund checks the exact frozen drain and the original allocation's stable physical absence, then applies the existing pool refund.
The allocator's durable issuance state and positive lookup of a live charge suffice to reject delayed use after that row is removed.
The provider can drop the retired window's admission record without retaining one enforcement tombstone per rotation.
This does not discard any independently retained receipt needed for replay or an external reconciliation.

## General proofs

Lean 4.35.0 checked fourteen theorems with standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| A previously chosen but unobserved operation can start after fence from the exact frozen row and its still-paid original allocation. | `a_chosen_seal_installs_the_exact_original_fence_without_resetting_provider_status`, `exact_fence_admits_an_unobserved_choice_with_its_original_charge`. The recovered attachment comes from the checked ordered seal, and the provider authenticates its chosen evidence. |
| Delayed or conflicting work cannot substitute a row, replace the installed fence, or act after terminal completion. | `frozen_admission_requires_the_exact_selected_row`, `an_installed_frozen_book_cannot_be_replaced_by_a_rival`, `a_terminal_borrow_never_starts_or_takes_effect_again`. Authenticate the exact original operation and its provider terminal observation. |
| A hidden unsettled assignment blocks drain. A drained window permits no effect at the modeled boundary. | `a_recovered_hidden_assignment_still_blocks_disposition`, `a_drained_original_window_permits_no_delayed_effect`. Effect admission checks both exact frozen membership and local state. |
| A guarded refund enforces drain and original physical absence and uses the actual pool refund transition. It frees room even when the old charge fills the pool. | `a_refund_decision_requires_the_frozen_drain_and_original_physical_absence`, `an_exact_refund_at_capacity_returns_the_old_row_without_requiring_new_space`. The physical row identity is unique and the lower effect and closure proofs apply to it. |
| An issued absent allocation cannot reappear through any finite pool trace. After refund an old request refuses even if it still has all its old metadata. | `an_issued_absent_allocation_cannot_reappear_in_one_pool_step`, `refund_allows_permanent_retirement_without_retaining_a_tombstone`. The provider's durable allocator never resets or wraps within its incarnation. |

The Lean control drops the exact frozen-row comparison.
The law that admits only the original chosen row fails at its designated proof step.

## Comparative models

TLC 2.19 exhausted three reference configurations of 28 states each.
The model gives the original provider one charged slot and asks it to install and retire three successive windows.
The three scenarios have a hidden chosen operation, a locally observed chosen operation, or no chosen operation.
Progress assumes weak fairness and eventual availability of authenticated fence, terminal, and physical absence evidence.

| Compared rule | Failure |
| --- | --- |
| Form the fence from entries the provider has already seen | The hidden chosen operation loses its original backing after 7 transitions. |
| Permit an unlisted operation after fence | An unchosen physical effect starts in 4 transitions. |
| Ignore terminal state on a delayed retry | A consumed operation can act again in 6 transitions. |
| Remove the charge while physical data is still present | The pool loses required accounting in 8 transitions. |
| Admit an old identity on the basis of its issuance alone | A retired operation can enter in 9 transitions. |
| Keep one terminal enforcement record per window | Two completed rotations exceed the one-record bound after 17 transitions. |
| Require free capacity before refund | A full original slot prevents its own release. TLC finds a temporal counterexample. |

The model leaves physical certificate formation, process recovery, and complete locator retention abstract.
A supplier that stays unreachable and provides no valid terminal or absence evidence keeps its original charge.
The progress checks do not assume that an outage silently creates headroom.

## Amendments

Use [A383–A387](../amendments.md#study-96--2026-11-23) for the provider-side fence, effect boundary, exact refund and bounded admission metadata.

## Acceptance programs

1. Choose an old operation, lose its first provider notification, and install the recovered original fence.
   Permit the exact recorded original operation if it still has its original paid window and is eligible.
   Reject a different row at that address.
2. Observe exact completion or effective stop for every required frozen operation.
   Reject delayed effects and wait for stable physical absence.
   Refund the original window at full capacity without requiring a replacement allocation first.
3. Rotate more than once, then present a delayed original request to the provider.
   Reject it through positive live membership and non-reused serials after the retired admission record is cleared.

## Residue

The composition assumes the provider verifies the frozen book against the actual chosen seal and associates terminal evidence with the exact original operation.
Production still needs a complete guarded dispatch surface so an alternate effect or reclaim entry point cannot bypass those checks.
Durable provider restore must preserve its active records, terminal operation states while the row is live, and allocator high-water mark.
Per-window status is modeled as a typed function scoped to the prepaid range.
The actual encoded status table, selector retention, and aggregate charged staging costs still need proof.
The split path remains the reference while the optional fused path is being qualified.

## Reproduction

From the Logkeeper checkout, use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/96-standing-provider-settlement/run.py
```

[run.py](run.py) records commands, exact configurations and counterexamples under .results/.
