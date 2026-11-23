# Study 83 · Replay protected reads through the same chosen cutoff as the journal

2026-11-23

## Question

Can either selectable recovery basis reproduce an exact protected read and its release after the original evidence issuers disappear, even when the data frontier is unchanged?

## Sources

Use [S54, S68, S69, and L05](../requirements.md), the [ranked source replay](../75-joint-realized-replay/report.md), the [protected admission](../81-recoverable-read-admission/report.md), and the [joint checkpoint and seal](../82-joint-read-recovery/report.md).
Keep exact current provider coverage as a separate serving condition.

## Model and comparisons

Order the full protected admission and exact logical release in the same frame family as journal commands.
Compare exact replay with replay of a journal-only projection, skipped holds and releases, slot-only release, and online reauthorization.
Compare current serving coverage with issuance based solely on historical evidence.
Make the physical sequence either complete with one staged tail, rival with an altered proof, or short.
Keep one result slot, two invocation and permit identities, two selectable bases, and a fixed data frontier in TLC.
Use an arbitrary finite slot set, a typed chosen prefix and arbitrary suffix length in Lean.

## Properties and programs

Check exact selected history and result provenance, coupled rows and holds, stale release refusal, and original authenticated reissue.
Check that a sealed predecessor refuses logical release and an old certificate alone cannot authorize current service.
Under weak fairness, exact replay and covered service complete through historical issuer loss.
The acceptance histories recover across close and slot reuse from either selectable basis and refuse incomplete media and missing current custody.

## Tools and reporting

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
Run negative controls first with the shared per-process limit.
Keep the raw errors, commands, and model configurations in the study directory.
Record the explored histories, general theorems, immutable evidence assumptions, amendments, and remaining certification interfaces.
