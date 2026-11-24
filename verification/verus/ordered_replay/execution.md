# Ordered journal proof execution

Source commit `5e12d2e5549b56056ef307277123e33fa8a5060c`. The Verus harness inputs and controls were compared byte-for-byte after rebasing.
Verus `0.2026.11.20.9da409b`, Darwin ARM64, Rust `1.100.0` and Z3 `4.16.0`.

| Area | Baseline verified functions | Negative controls rejected |
| --- | ---: | ---: |
| `ordered_replay` | 11 | 6 |
| `ordered_lease_reducer` | 63 | 11 |
| `prefix_agreement` | 42 | 11 |
| `rotation_slot_evidence` | 44 | 13 |

`verification/verus/run.py --verus <verus> --evidence <scratch> ordered_replay ordered_lease_reducer prefix_agreement rotation_slot_evidence` reproduces the runs.
The replay baseline checks `laws::selected_replay_indices_cover_exact_interval`, `laws::resume_requires_exact_cut_in_original_interval`, `laws::bounded_replay_emits_original_record` and `laws::exhausted_replay_has_the_original_terminal_cut`.
The quorum baseline checks the production vote transition, including the matching voter, ballot, candidate digest and readback flag, distinct configured membership and the strict-majority threshold.

Lean 4.35.0 built the 44-job package, including `Logkeeper.Protocol.held_record_survives_trim_and_transfer`, with standard axioms. Changing its live-hold trim premise to `True` caused the retention step to fail during elaboration.
TLC 1.7.4 checked the held replay model at five and eight positions and detected skipped delivery, substituted terminal history and early completion. The sealed replacement baseline at two records checked 35,148 states. The below-quorum successor control loses its only copy in four transitions, the direct replacement control permits a stale decision in two, and the equal-length substitution control loses the original copy in five.

The checked transitions consume the supplied scoped vote or resident record. The software correspondence from accepted media and sealed repair bytes to the installed image, original hold and its RTDB consumer remains open.
Production Rust was compiled only where included by Verus.
