# Study 90 · Preserve the seal through physical delivery stop

2026-11-23

## Question

Can a successor activate after a delivery stops during the sealed interval and its delivery-only extent is unavailable, while preserving exact replay and every independent owner of that extent?

## Sources

Use the [sealed transfer](../89-sealed-delivery-handoff/report.md), [independent paid delivery book](../88-retained-delivery/report.md), [original-custodian settlement](../23-custody-authority-handoff/report.md), and [exact read and storage custody](../19-shared-object-custody/report.md).

## Model and comparisons

Compare keeping original custody through activation with allowing a durable original-provider stop receipt to realize the stopped obligation.
Compare that evidence-only change to pruning rows before the ordered owner settles them.
Keep canonical seal selection and book reconstruction identical across these alternatives.
Check role overlap with the base replay or install, a protected read, and a sibling delivery.
Model receipt transfer, independent loss of both old routes, and a target crash in TLC.
In Lean use arbitrary finite delivery books, typed immutable catalogs, and authenticated and durable receipt predicates.
Treat complete role enumeration and actual physical stop as explicit premises.

## Properties and programs

- A durable exact receipt can replace a missing delivery-only dependency after the stop.
- A missing independent base, read or still-live delivery dependency blocks installation.
- Stale serial, foreign custodian, foreign lineage and volatile receipt supply no replacement.
- The exact seal book and counters survive activation and reopening.
- Terminal evidence never supplies permission to finish an already stopped operation.
- Exact terminal evidence can drive the installed owner's later ordered settlement.

## Reproduction

Use TLC 2.19 with Java 21, Lean 4.35.0 and Python 3.13.
Run negative controls before both reference checks.
Keep commands, results and counterexamples under .results/.
