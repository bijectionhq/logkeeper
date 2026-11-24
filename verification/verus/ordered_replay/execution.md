# Ordered replay Verus execution

Source commit `bfd0e4ac2f45a0c7540d8951e844b406681a1135`.
Verus `0.2026.11.05.31e44e6`, Darwin ARM64, Rust `1.99.1`.
Used the installed Bijection verifier and its Z3 with `verification/verus/run.py --verus <verus> --evidence <scratch> ordered_replay` under `BIJECTION_LOCAL_EXECUTION=owner-authorized`.

| Case | Verified functions | Expected diagnostics |
| --- | ---: | --- |
| Baseline | 4 | 0 |
| `lose_last_record` | 3 | 1 postcondition failure in `retained_indices` |
| `substitute_cursor_history` | 3 | 1 postcondition failure in `cursor_offset` |

The baseline includes `laws::selected_replay_indices_cover_exact_interval` and `laws::resume_requires_exact_cut_in_original_interval`.
The production proof checks offsets within the selected resident record sequence and the requirement for exact cursor equality.
The installed prefix and its record sequence, checkpoint authentication, page byte transport, and RTDB decode and apply retain separate obligations.
Production Rust was checked only where included by Verus.
