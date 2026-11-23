# Study 57 · Recover the chosen incarnation state

2026-11-23

## Question

How does an incarnation authority recover exact ordered inventory decisions when a durable majority is ahead of its learner or the selected checkpoint?

## Sources

Use [journal rotation](../26-journal-rotation/report.md), [ranked recovery](../32-configuration-closure/report.md), [ordered replay of attached evidence](../49-unified-source-history/report.md), and [finite inventory encoding](../56-finite-inventory/report.md).

## Model

Compare resumption at the installed chosen cut with restarting at the last learned cut, applying a lone accepted candidate, or reconsidering a command from newly available evidence.
Keep votes, choosing, application, and checkpoint publication separate.
In Lean, reduce ordered incarnation controls to the finite custody rules, and use the existing ranked recovery and crash-selector models to derive the replay cut.
Represent authenticated external evidence by a predicate over immutable command inputs. Treat media and custody adapters as premises.

## Properties

- Claim an incarnation only through an exact chosen and applied registration result.
- A later recovery cutoff includes previously chosen results even if no learner or client saw them before the crash.
- Replay the recorded evidence at each ordered position.
- Recover the exact inventory and its original reply sequence through each crash-selectable base.

## Tools

Use TLC 2.19 with a single worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for finite inventory refinement and correlated recovery.
