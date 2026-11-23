# Study 27 · Commit agreement across replica-group ballots

2026-11-22

## Question

How can a successor retain every chosen command even when recovery sees a mix of partial accepts, competing prepares, and lost replies?

## Sources

Use the [requirements](../requirements.md), the [logical reference stream](../07-reference/report.md), the [membership proof](../12-quorum-membership/report.md), and the [rotation proof](../26-journal-rotation/report.md).
Read RTDB Multi's `SealIsAPromise` and `RecoverTail` at `fc6da3a4a3` and the Logkeeper [winner selection](../../src/client/recovery.rs) and [quorum recovery](../../src/client/writer.rs) at `85a594e`.
The durable promise argument follows the fixed-group quorum reasoning in Lamport.
The whole-log ranking resembles the view change in Viewstamped Replication. [Paxos Made Simple](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf) · [Viewstamped Replication Revisited](https://dspace.mit.edu/entities/publication/80846d94-fcd3-40e6-87fb-8d91fe99a5d1)

## Model

Keep group membership fixed.
Model a uniquely owned ballot with an immutable proposal chain that can extend while votes are delayed.
A prepare persists a higher acceptance floor and captures that voter's latest complete accepted prefix.
A ballot starts with a prepare quorum and its greatest accepted prefix.
A vote persists the entire exact prefix logically, including the adopted seed.
A later vote for a longer prefix in the same ballot also certifies the contained positions.
Abstract chunk transport, journal bytes, and group activation after adoption.
Use the prior media contract for durable accepted data and promises.
Treat physical voter identity and authenticated reports as premises.
A group ballot and an RTDB writer grant remain distinct.

## Checks and comparison

- Safety. Any two chosen prefixes agree at their common positions.
- Safety. Every later elected ballot starts with all earlier chosen prefixes, including when the earlier quorum completes after part of the recovery exchange.
- Compare ranking by accepted ballot and then length to ranking by either field alone.
- Falsify with a lost promise, an empty view stamped with its prepare ballot, and a receipt built from matching payloads voted for in different ballots.
- Exhibit a successor choosing a shorter committed branch over a longer minority branch, adoption of an unchosen minority vote, and an exact receipt after a genuine same-ballot quorum.

## Reproduction and report

Use TLC 2.19 with one worker and a 512 MiB heap and Lean 4.35.0.
The generic bounds allow any schedule of enabled ballot actions.
Use restricted schedules with the same transitions for the three-ballot divergent-tail comparison and the four-ballot mixed-receipt comparison.
Retain commands, configurations and traces.
Report state counts and trace lengths separately for generic and restricted checks.
Mark the limits around liveness, fresh read barriers, reconfiguration, and shipped protocol behavior.
