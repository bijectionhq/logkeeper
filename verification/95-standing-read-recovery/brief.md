# Study 95 · Recover the standing credit cursor

2026-11-23

## Question

Can either selectable checkpoint or an exact sealed handoff recover standing read credit without reissuing a physical borrow ID or making ordinary recovery depend on optional live backing?

## Sources

Use [standing credit](../94-standing-read-credit/report.md), [named delivery recovery](../88-retained-delivery/report.md), [sealed delivery handoff](../89-sealed-delivery-handoff/report.md), and [receipt selection](../91-receipt-selectors/report.md).

## Model and comparisons

Add the exact standing-window generation, archived certificate name and spent cursor to the named checkpoint control.
At the source seal, bind the frozen grant and its cursor to the same named control as the exact delivery book.
A successor imports the generation watermark and the delivery book without enabling the old grant.
Compare cursor resets, replay from an older root without its exact suffix, foreign placement proof, reviving the old grant at handoff, loss of the watermark, and waiting for current physical coverage during historical replay.
Check the fixed-width cursor at range exhaustion, separately from the last issued physical serial.
Use the existing committed reducers for replay in Lean and one prior spend, one checkpoint selection or move, and one later opening in TLC.

## Properties and programs

- An exact named checkpoint retains the generation and cursor, including when no delivery row remains live.
- Replaying the complete chosen suffix from either exact base yields the same control state.
- The exhausted cursor remains representable.
- Archive proof recovers historical state. Current physical backing authorizes fresh effects.
- A sealed predecessor's grant is frozen for original settlement and cannot activate on the successor.
- The target keeps the predecessor watermark, and original charge settlement still requires its exact separate evidence.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
Run negative controls first.
Keep commands, configurations and traces under .results/.
