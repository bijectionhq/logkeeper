# Study 103 · Bind the selective window to its writer grant

2026-11-23

## Question

Can writer replacement preserve exact read deduplication and service without a separate policy service, while an authorized successor can change the window width?

## Sources

Use [the canonical selective window](../101-selective-read-window/report.md), [the ordered reducer and packed checkpoint](../102-selective-ordered-recovery/report.md), [the exact writer grant](../76-stable-writer-handoff/report.md), and [the installed service contract](../architecture-reopening/comparison.md).

## Comparison

Compare accepting equal packed size, resizing a live grant, accepting an offer for another grant, losing an old independent delivery, opening history with the current width, and requiring a reachable policy service for reads or writer replacement.
Keep the actual ordered writer transition, read admission, and retained delivery semantics from the reference.
Lean connects dynamic window width to that reducer and checks the full historical policy tuple at the named checkpoint.
TLC compares two slots, two grants, one prepared width change, and one older selector.
The historical selector case abstracts the suffix by its exact application result.
Use the Lean replay theorems for arbitrary finite chosen histories.

## Acceptance

- Open an older checkpoint using its own certified grant and width, then replay the chosen successor's different width.
- Reject a same-length bitmap interpreted under a width the historical grant did not choose.
- Replace a worker under the inherited installed width while the optional policy offer is unavailable.
- Accept an authenticated change only along with its exact successor, and preserve independent original read custody.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
The runner writes commands and negative controls under .results/.
