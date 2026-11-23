# Study 98 · Reuse a refund through crash-selectable checkpoints

2026-11-23

## Verdict

A pool may report a refund and spend the returned capacity once every legal recovery choice can reconstruct the exact refund.
A stable replacement image is sufficient.
An exact durably discoverable refund in the owner's existing ordered suffix also suffices while the predecessor is still selectable.
The dependent charge follows it in the same order.

Redo lets a ready refund return before selector synchronization.
It retains its original bytes and name until every selectable base covers it.
With independent media, the retained redo and the replacement image can coexist.
If the reserve covers only the image, the redo can fill enough of the reserve to prevent the checkpoint that would retire it.
The copy-and-switch variant can finish at that smaller bound, with the selector on its reporting path.

Use the owner's existing ordered log for the shared-suffix reference and fund its overlap with the next checkpoint.
This uses one refund reducer and one recovery order.
A stable whole-image cut remains a valid alternative with a different space and critical-path tradeoff.

## General proofs

Lean 4.35.0 checked eleven theorems with standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| An accepted refund removes the exact original paid row and requires its durable fence and physical erasure state. A decoded history projects to the existing pool ledger. | `any_refund_frame_returns_the_exact_closed_absent_row` and `every_decoded_history_refines_the_pool`. The row's local evidence represents authenticated stable closure and absence. |
| The combined owner state preserves the chosen typed ledger under arbitrary finite command and media histories. Every legal crash root reconstructs the same pool from the exact base and retained suffix. | `arbitrary_ordered_refund_and_reuse_traces_remain_recoverable` and `every_crash_choice_of_the_composed_machine_recovers_the_current_budget`. The initial pool is sound and the local media satisfy the existing byte and namespace barriers. |
| At full occupancy a dependent charge refuses until the refund is applied. The composed machine can order refund and refill in two commits with the right original row. | `at_capacity_the_original_refund_must_precede_a_dependent_debit` and `the_composed_refund_and_refill_program_starts_at_full_capacity`. The exact single original row is eligible for settlement. |
| A predecessor that still replays a position prevents reuse of the corresponding redo extent. Distinct overlapping redo and alternate checkpoint allocations require their sum. | `predecessor_coverage_blocks_reusing_the_redo_extent` and `overlapping_redo_and_alternate_image_need_their_combined_reserve`. Independent pins remain subject to the underlying rotation rule. |

The Lean mutation ignores the original physical serial while keeping the logical scope check.
The exact-original law fails at its designated proof step.

## Comparative models

TLC 2.19 models three rotations from an already full pool, one refund frame at a time, and up to two crashes.
The initial resident base has separate funding.
The redo frame occupies one extra unit and the alternate image two.
A local crash can reverse a volatile selector switch.
A staged frame continues to occupy its reserved slot after crash even when the bytes need rewriting.
The temporal cases assume fair eligible local transitions, with selector synchronization disabled only in the designated outage cases.

| History | Result |
| --- | --- |
| Copy-and-switch, two-unit reserve, available selector barrier | Three refunds and workspace turnover in 84 states. |
| Ordered redo, three-unit reserve, available selector barrier | Three refunds and workspace turnover in 514 states. |
| Ordered redo, selector barrier unavailable, local durable log working | The first refund returns in the 216-state configuration. Further refunds can wait for rotation once the finite lane fills. |
| Reuse credit while an older selector remains legal, using the exact redo | Eight-transition witness. |
| Two distinct crash points and three successive refund and reuse generations | A 36-transition witness reopens the predecessor after a credit has been reused, then loses unnamed bytes from a later redo frame. |

| Deliberate weakening or changed premise | Counterexample |
| --- | --- |
| Let a visible image alone fund ordinary reuse | The predecessor can recover both the unrefunded old debit and the new charge against one unit of budget in five transitions. |
| Report after syncing redo bytes but before durable discovery | The acknowledged refund cannot be recovered from the predecessor in four transitions. |
| Recycle the redo based on the visible selector alone | The older selectable checkpoint loses its required refund in eight transitions. |
| Give ordered redo only the two-unit image reserve | There is a fair stall after the first durable refund because the checkpoint cannot fit alongside the retained redo. |
| Require a stable selector before reporting, with that barrier unavailable | The copy-and-switch variant can have a complete visible image and still cannot report the first refund. |

The comparison measures safety, progress under the stated fault schedules, and reserved units.
A bounded log can batch records and use fewer synchronous checkpoint publications, but this model has one reserved redo slot and supplies no batching or throughput result.

## Amendments

[A392–A395](../amendments.md#study-98--2026-11-23) govern consumption of returned credit, redo retention, and the physical overlap reserve.

## Acceptance programs

1. Start at full occupancy with one exact closed, absent allocation.
   Order its refund through the installed owner, then admit an independent charge into the returned capacity.
   Recover the same ordered pool from the predecessor and replacement choices while both selectors remain legal.
2. Pause the selector barrier while the durable log remains available.
   Return the refund using exact durable redo.
   Keep the redo slot occupied until a stable replacement covers it.
3. Crash into an older selector after dependent reuse, and crash again after writing new redo bytes before durable discovery.
   Once both roots cover the old refund and the physical workspace is safe to reuse, rotate the slot and repeat.

## Residue

The Lean rotation model represents a base by its exact ordered prefix and replays an abstract typed command.
A real compact checkpoint must authenticate the resulting whole owner image at its cut.
The study does not yet give canonical wire sizes, filesystem or object-store atomic behavior, real quorum persistence, or the physical peak of the runtime adapter.
The three-unit comparison applies to its abstract sizes and disjoint extents.
A real shared workspace must count all concurrently protected redo, selector images, pins and staged artifacts in each pool.
The refund reducer uses already settled local provider evidence.
The broader storage-effect and authority-transfer proofs still govern how that evidence becomes safe to order.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/98-settlement-redo/run.py
```

[run.py](run.py) records commands, configurations and raw counterexamples under .results/.
