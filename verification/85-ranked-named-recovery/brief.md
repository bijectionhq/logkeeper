# Study 85 · Bind a named checkpoint to the current ranked installation

2026-11-23

## Question

Can the successor recover the exact journal and read book from either named checkpoint when a predecessor learner missed a chosen command, and publish that image only at the current installed cutoff?

## Sources

Use [the recovery and read requirements](../requirements.md), [durable configuration closure](../32-configuration-closure/report.md), [bootstrap activation](../33-activation-slot/report.md), [authenticated checkpoint framing](../51-checkpoint-envelope/report.md), [combined read replay](../83-ordered-read-replay/report.md), and [the invocation floor](../84-read-invocation-floor/report.md).

## Model and comparisons

Use the existing fenced source quorum and destination single-choice activation slot.
Separate the selected candidate, physical staging, quorum installation, and its use at the current installed frontier.
Compare the exact path with the learned prefix, longest accepted prefix, position-only checkpoint matching, publication before install, wrong successor scope, superseded revision, same-revision frontier advance, quorum loss after installation, missing suffix, requiring every predecessor, and requiring installation before staging.
Keep three predecessor voters with one absent, two competing accepted reports, two genuine checkpoints, and one rival checkpoint in the bounded model.
Use arbitrary histories and typed recovery evidence in Lean.

## Properties and programs

- Inherit every earlier choice even when its learner died and the data frontier stayed fixed.
- Open the immutable control and data components authenticated for the exact certified prefix.
- Verify all local suffix bytes through the cutoff and retain the exact closure and consumed nonce.
- Stage with the fenced source quorum and exact media, then activate only after the destination chooses the exact seed.
- Refuse delayed publication through a foreign or superseded scope, or after the same scope has advanced.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
Run negative controls before baseline checks.
Keep the commands, configurations, and traces in .results/.
