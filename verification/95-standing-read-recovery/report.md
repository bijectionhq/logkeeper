# Study 95 · Recover the standing credit cursor

2026-11-23

## Verdict

Persist the exact standing credit generation, immutable archived proof name, and spent cursor in the authenticated named checkpoint.
An empty delivery book can still have spent physical serials.
When a crash selects an earlier checkpoint, its exact chosen suffix advances the cursor before new admission.

A cross-placement seal authenticates the frozen source grant and spent cursor alongside the delivery book.
Activation carries the watermark forward and starts with no current standing grant.
The target funds a strictly newer window.
The old grant remains evidence for its original scope's exact settlement.

Historical recovery uses immutable proof metadata.
Requiring an optional live physical grant to reopen ordinary state can stall recovery even when mandatory inputs are all present.
Fresh fused use requires its own current backing check.
Missing current backing refuses submission before the normal fused frame can be proposed.

The producer also needs one more representability check.
A range can end at the largest encodable physical serial while the exhausted cursor, which counts spent serials, needs one larger value.
Study 94's admission rule now requires the fully spent cursor to fit the checkpoint's fixed-width field.

## General proofs

Lean 4.35.0 checked fifteen theorems with standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| The standing section roundtrips in at most one tag byte plus three fixed-width fields. The generation survives even when no current grant is present. | `a_saved_window_has_an_exact_bounded_encoding`, `absent_window_still_recovers_the_full_installed_watermark`. This bound covers the section and its archived proof name. The referenced proof body has its own retention budget. |
| Every chosen post-admission cursor fits. Recovery restores the exact cursor even at exhaustion and excludes a foreign placement. | `every_chosen_cursor_fits_even_at_exhaustion`, `recovery_restores_even_an_exhausted_current_range_without_resetting_it`, `a_window_certificate_of_another_placement_cannot_restore_a_current_grant`. The archive resolver and provider certification are authentic and immutable. |
| An exact named checkpoint opens the delivery book and credit from one envelope. Either exact base and complete suffix reproduce one state. | `a_named_checkpoint_reopens_the_books_and_standing_cursor_from_one_cut`, `every_exact_selectable_base_replays_the_same_credit_and_delivery_cursors`. Base certification binds the complete state to its chosen cut. The replay model covers existing retained commands and standing opens and installations. |
| Historical proof alone grants no fresh authority. Once a live submission is admitted for the exact state, chosen replay produces the same decision independent of current provider state. | `historical_proof_alone_cannot_admit_fresh_work`, `a_live_submission_replays_the_same_decision_without_live_provider_state`. Admission and choice must bind the same applied snapshot and original coverage. |
| The source verifies the exact frozen grant and watermark in the named seal. The successor imports the watermark, discards current credit and refuses old reinstall. | `a_chosen_seal_preserves_the_watermark_and_fences_the_original_window`, `target_activation_restores_the_fence_watermark_without_reviving_old_credit`, `the_successor_rejects_the_predecessor_window_even_after_source_loss`. This composes the checked source and target seal decisions using the same authenticated named content. |

The combined handoff also preserves the original retained delivery book and its issuance floor exactly.
See `a_funded_handoff_preserves_the_entire_old_delivery_book_without_active_credit`.

The Lean control drops the placement check from archived grant recovery and fails its designated law.
The updated producer rule also passed the Study 94 Lean suite and both of its controls.

## Comparative models

TLC 2.19 checked six finite reference configurations and reproduced eight safety failures and one temporal failure.
The reference cases use a prior spent borrow, at most one fresh borrow, one older checkpoint or handoff, and weak fairness where progress is checked.

| History | Reference | Failure in the comparison |
| --- | --- | --- |
| The original delivery row is gone | Restore the spent cursor and open the next serial in 5 states. | Resetting based on the empty book repeats the first serial in 4 transitions. |
| Recover an older base before the prior spend | Replay the chosen suffix and open the next serial in 5 states. | Ignoring the suffix repeats the first serial in 4 transitions. |
| Resume with a small cursor field and an otherwise representable next serial | Preserve ordinary writes and refuse the unencodable next cursor in 5 states. | Checking only the issued serial overflows the spent cursor after 4 transitions. |
| Activate the sealed successor | A strictly newer window serves in 6 states. | Dropping the watermark admits an old generation in 4 transitions. Carrying old credit as current fails in 2. Refunding original backing at installation fails in 4. |
| Archived certificate belongs to a different placement | Refuse in 3 states. | Ignoring placement permits use in 4 transitions. |
| Historical metadata is present and optional live backing is absent | Reopen, write and refuse fresh fusion in 5 states. | Treating the metadata as live authority permits use in 4 transitions. Requiring optional live readiness to recover produces a temporal counterexample. |

## Amendments

Use [A378–A382](../amendments.md#study-95--2026-11-23) for exact standing checkpoint state, representability, and separation of historical proof, fresh use and original settlement.

## Acceptance programs

1. Choose a delivery and settle it, leaving no live row for its serial.
   Reopen the exact same-placement window and allocate a different physical serial.
   Repeat from an older checkpoint with the chosen spend in its retained suffix.
2. Spend the last allowed slot.
   Store and reopen the exhausted cursor exactly, then refuse a further fresh use.
3. Lose live backing for optional fusion with historical metadata and mandatory recovery dependencies intact.
   Reopen and commit ordinary work while refusing the optional use.
4. Seal a funded original, activate its successor and recover the old generation watermark from the exact attachment.
   Refuse reopening the original at the target.
   Keep its existing delivery and original custody obligations exact.

## Residue

The model assumes archived certificate metadata is durably recoverable wherever a selected checkpoint or its suffix needs it.
The local standby section names that metadata, so production qualification needs actual durable discovery and immutable object bindings.
Fresh admission and frame choice need an authenticated proof that physically paid basis coverage applies at the chosen position.
Existing provider release and terminal witness obligations still apply to already chosen deliveries.
[Study 96](../96-standing-provider-settlement/report.md) composes recovered fence installation, exact pre-refund drain, and permanent refusal after collecting the original allocation.
The study has no production throughput or allocation-budget result.

## Reproduction

From the Logkeeper checkout, use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/94-standing-read-credit/run.py lean
python3 verification/95-standing-read-recovery/run.py
```

[run.py](run.py) records tool invocations, configurations and traces under .results/.
