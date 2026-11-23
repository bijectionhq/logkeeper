# Study 112 · Erase journal-retained history by key-generation rotation

2026-11-23

## Question

How must an erasure commit compose with crash-selectable roots, the grant fence and held views, so that recovery never needs a revoked key and never restores erased history?

## Sources

Use D02 in the [requirements](../requirements.md), RTDB's `verification/redesign/R7-eraser.md`, [journal rotation](../26-journal-rotation/report.md), and [dynamic protection](../109-dynamic-protection/report.md) (A445).

## Model and comparisons

Compare the reference commit rule with three weakenings: committing when one slot shows the clean root, admitting an old-generation append after the rotation cut, and revoking held views at commit.
Use TLC 2.19 for the bounded comparison and Lean 4.35.0 for any number of selectable images.
