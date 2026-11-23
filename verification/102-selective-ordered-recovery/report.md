# Study 102 · Recover the selective read window with the ordered state

2026-11-23

## Verdict

The selective window can use the existing ordered protected-read and retained-delivery semantics.
Advance its bitmap only with a successful admission or authenticated abandonment in that same command.
Closing a read clears its own protected admission under the existing stop rule.
Its spent identity and any separately funded delivery stay recorded.

The named checkpoint carries one fixed-width floor word and a bitmap of `ceil(windowBits / 8)` bytes.
The existing floor decoder projects its bytes from that same summary.
The opener validates the canonical packed representation, exact encoded window and required custody alongside the same named body.
Either certified base can replay its exact chosen continuation.
A later ranked successor preserves all earlier resolved invocations, including across a grant change.
New scope issuance uses a fresh window, and an old request must still match the exact active grant before acquiring a hold.

## Evidence

Lean 4.35.0 checked sixteen theorems with standard axioms only.

| Guarantee | Evidence and premises |
| --- | --- |
| Exact writer scope and atomic protected capture | `a_selected_nonce_is_fresh_in_its_exact_scope` and `accepting_a_read_records_its_window_bit_and_the_original_protected_effect`. The adapter uses the existing basis, reservation and capture decisions. |
| Preservation through close, delivery decisions and scope changes | `closing_a_read_does_not_clear_its_admission_window_or_delivery_book`, `every_applied_command_preserves_spent_invocations`, and `every_replayed_scope_change_preserves_past_admissions`. The delegated operation uses the existing ordered and retained-delivery reducers. |
| Recovery through either certified base and ranked handoff | `both_selectable_bases_restore_one_window_and_its_original_reads`, `any_recovery_preserves_a_spent_invocation_from_a_certified_prefix`, and `an_installed_ranked_successor_preserves_the_exact_prior_invocation`. Exact grants, certified bases, aligned frames and authenticated ranked installation remain inputs. |
| Bounded canonical summary and exact named body | `the_window_has_a_fixed_bit_packed_checkpoint_size`, `decode_the_exact_packed_window`, `a_successful_decode_rejects_padding_and_has_no_other_wire`, and `a_named_open_uses_its_own_exact_ready_window`. The open path checks the authentic envelope and all existing read and delivery dependencies. |

The Lean control weakens the active-writer equality and fails at the exact-scope law.
TLC 2.19 exhausts two same-scope configurations of seven states and two handoff configurations of 45 states.
The bounded progress laws assume weak fairness of eligible actions, a free result slot once the old read closes, exact protected backing, and delivery stop or completion at its original custodian.
The earlier nonce arrives after local recovery in the same-scope cases.

| Deliberate comparison | Evidence |
| --- | --- |
| Omit the chosen suffix when the old selector wins | The closed read opens a second time in five transitions. |
| Lose sparse marks when opening the newer checkpoint | The same invocation opens twice in five transitions. |
| Clear the identity window on close | A duplicate opens in three transitions. |
| Accept a predecessor request under a successor window | Admission under the wrong grant occurs in eight transitions. |
| Clear an independently retained delivery when closing the read | Its custody obligation disappears in four transitions. |
| Use a strict next-only window for independent requests when the first arrives after recovery | TLC finds a temporal stall before the later read can open. |

## Amendments

[A404–A407](../amendments.md#study-102--2026-11-23) bind selective admission to the established ordered effects, exact serialized summary and retained delivery lifetime.

## Limits

The refinement adapter uses the legacy capture and abandonment logic after selective authorization.
A temporary predecessor floor is used only inside those two old checks and is overwritten in the combined result by the canonical summary's floor.
It has no authority at handoff, checkpoint, or journal advance.
The design can factor out the shared checked effects before implementation.

The named opener proves the pure checkpoint codec and exact selection under the existing authenticated catalog and declared delivery dependencies.
The configured window width is fixed for the modeled grant and is supplied by the authorized configuration.
The product still needs the configuration binding, canonical complete frame format, physical media and provider proofs, and Bijection confirmation of where independent overtaking is allowed.
The finite model exercises one fault-free transfer after one recovery.
The general handoff theorem uses the previously verified ranked installation contract for any finite chain.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/102-selective-ordered-recovery/run.py
```

[run.py](run.py) saves the tool commands, finite configurations and negative controls under .results/.
