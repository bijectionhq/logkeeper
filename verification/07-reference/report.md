# Study 07 report · Consolidated stream reference machine

2026-11-22

## Verdict

Sixteen Lean theorems check substantive parts of the logical stream contract for arbitrary finite traces or arbitrary bounded resources.
The proof combines the append, replay, trim, writer and placement fence, activation, and terminal transitions in [one reference machine](Kernel.lean).
There are six deliberate weakened variants and each invalidates the intended law.

## Properties

| Theorems | Claim within the model |
| --- | --- |
| `initial_valid`, `every_trace_preserves_bounds` | A reachable state stays within both log bounds. The trim floor stays under a committed checkpoint and no live replay lies below it. |
| `trace_extends_history` | Every later state preserves the earlier committed sequence as a prefix, including after activation. |
| `retired_absorbs_trace` | Terminal retirement persists through all subsequent reference-machine transitions. |
| `receipt_committed_exact`, `retained_receipt_survives` | Every exact receipt identifies an existing committed record and can be observed again while its LSN is retained. |
| `barrier_reports_committed_end` | An authorized barrier result is the exact committed end at the observation step. |
| `append_receipt_program` | An authorized writer at the head with both kinds of capacity can append and obtain the matching receipt. |
| `wrong_lsn_refused`, `stale_writer_refused` | No append admission exists for a stale position or superseded writer. |
| `two_durable_locations_survive_one_loss` | Two distinct locations with durable copies imply at least one retained copy after any one modeled location loss. |
| `replay_issuance_is_monotone`, `spent_replay_stays_unused`, `close_permanently_refuses_delayed_admission` | An issued and spent permit stays absent for every future trace, including a move. |
| `prepare_and_admit_replay_program`, `closing_replay_preserves_others` | The reference can prepare and admit an exact LSN and can close one ID without affecting others. |

The only axiom dependencies reported by Lean are standard.
The controls check wrong LSN admission, granting append to a stale writer, trim past the certified prefix, trim past an active replay, returning a speculative barrier cut, and accepting admission without a live prepared permit.
They re-exercise A01, A02, A07, A13, A14, and A44.

## Scope and developer cost

The acceptance program invokes append with the exact known next LSN and sufficient budget, then uses that LSN to obtain the reference receipt.
The logical freeze certifies the current holder. Activation carries its epoch and holder at the new placement.
The [placement study](../11-authority-refinement/report.md) proves that the modeled source seal and reservation-based installation refine these transitions.
The reference machine already makes any replacement of the installed history visible to the monotonicity law.
Certificate authenticity, prefix durability during recovery, all acceptance programs, and independence of every mechanism remain open at full design scope.
The single-location-loss theorem assumes durable copies at distinct fault domains and checks the cardinality argument.

## Reproduction

```sh
LEAN_BIN=/path/to/elan/bin/lean python3 verification/07-reference/run.py
```

The runner pins Lean 4.35.0 and records baseline and mutation diagnostics in `.results/`.
