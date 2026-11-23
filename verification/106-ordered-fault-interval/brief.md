# Study 106 · Recover the ordered AZ protection interval

2026-11-23

## Question

Can a current recovery majority reopen either crash-selectable checkpoint and continue with the exact protection owed before voter replacement, renewal, or a lost reply?

## Sources

Use S02, S57, S89, L01 and L26 in the [requirements](../requirements.md).
Use the existing [journal rotation](../26-journal-rotation/report.md), [ranked configuration closure](../32-configuration-closure/report.md), and [serving and protection rules](../105-service-scope-protection/report.md).

## Model and comparisons

Compare checkpoint-only restoration, implicit reset on voter replacement, live reclassification, and recovery by replaying ordered confirmations and renewals.
Represent the fault interval by the chosen position that established it and one optional confirmed loss.
A confirmation is eligible in its own lineage and interval, independent of which voters hold the lineage.
Renewal requires protection evidence that covers the exact installed basis, including the current voter family, custody and acknowledged inputs.
One bounded comparison checks late confirmations, old and new selectors, a voter replacement, and a renewal race in which foreground work adds a recoverability obligation.
A second bounded comparison checks renewal progress under an unending series of covered writes, then injects a write whose bytes do not yet have restored coverage.

Check exact recovery and scope safety as invariants, independent serving under stable conditions as a temporal property, and renewal after repair as a reachability witness.
In Lean, compose the custody proof for a successful renewal, ranked membership changes and the existing crash-selector exactness lemma over arbitrary lists of ordered records.

## Boundaries

Abstract signed incident and repair evidence as relations over the exact statement and opaque inline evidence.
The renewal position denotes a unique previously chosen journal position.
Exact quorum installation, authorized effective membership and custody changes, and named authenticated checkpoint bodies are premises.
The cases hold one loss interval and one possible renewal while modelling at most one crash and one voter replacement.
In the renewal race at most one newly acknowledged obligation needs repair.
The load comparison abstracts a fully covered append as an event and assumes stable quorum and custody.
Use TLC 2.19 and Lean 4.35.0 with the shared runner's 60-second per-command limit.
