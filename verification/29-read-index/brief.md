# Study 29 · Fresh reads without a command per invocation

2026-11-22

## Question

Can a quorum observation supply a fresh exact read cut without adding a read marker to the replicated log?

## Sources

Use the [requirements](../requirements.md), [membership quorums](../12-quorum-membership/report.md), [snapshot reservations](../18-snapshot-admission/report.md), [fixed-group agreement](../27-prefix-consensus/report.md), and [ordered marker](../28-ordered-application/report.md).
Read RTDB Multi's `SealIsAPromise`, `SealsAreAnnounced` and `ReadIndexUsesTheActiveLoglet` at RTDB commit `fc6da3a4a3) and the incumbent [client](../../src/client/mod.rs) and [voter](../../src/server/state.rs) read-index paths at `85a594e`.

## Model

Use one fixed voter group, two ballots, and append-only chosen prefixes.
The approved active ballot has exact durable coverage of every earlier chosen command when a round starts.
Each positive observation comes from a distinct eligible voter and captures its exact accepted history in the round's scope.
The round begins after its invocation.
Samples can arrive before or after a ballot fence, and an old target can be lost when a later ballot chooses different bytes.
The exact chosen and applied prefixes can advance separately.

Interpret the logical frontier as one cut per ordered command.
Also check a physical frontier that can skip intermediate cuts on a durable batch.
Keep the actual snapshot, replay custody and transport outside the finite model.
Use the ordered application model for the exact read result in Lean.

## Checks and comparison

- Every successful round belongs to the invocation and respects any preceding higher-ballot quorum fence.
- Its maximum observed index covers choices before the round, including a choice the serving replica has yet to learn or apply.
- Returned contents are an exact applied chosen prefix with a cut in the invocation interval.
- Compare serving the sampled exact prefix after certification with serving a separately validated applied prefix through the sampled index.
- Compare the logical cut with a physical-batch contract that requires the maximum observation to match a cut certified before the same round.
- Falsify cached rounds, ignored fences, incomplete activation, local learned head alone, speculative exposure, and reusing a sampled history solely by position.
- Exhibit a successful no-marker read during a partial fence and delayed delivery of an already valid round.

## Tools and report

Use TLC 2.19 with one worker and a 512 MiB heap, and Lean 4.35.0 with the pinned toolchain.
Run the negative controls first.
Report state counts and the shortest traces separately from general refinement proofs.
Track replay reservation, read availability under sustained writes, and dynamic membership as separate obligations.
