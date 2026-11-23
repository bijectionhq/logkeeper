# Study 32 · Configuration closure and successor installation

2026-11-22

## Question

How does a replacement configuration recover every preceding choice when the coordinator has incomplete receipts, voters are still receiving delayed packets, and a zone can fail during transfer?

## Sources

Use the [requirements](../requirements.md), [journal membership study](../12-quorum-membership/report.md), [fixed-group prefix consensus](../27-prefix-consensus/report.md), and [reconfigured reads](../30-reconfigured-reads/report.md).
The incumbent Allium contract ties commit to writes on a durable quorum and recovers by ranked sealed reports. [RTDB Multi at fc6da3a4a3](https://github.com/bijectionhq/rtdb/blob/fc6da3a4a3/allium/rtdb-multi.allium#L449-L474)

## Model

Use one group lineage and two or three successive ordinary or joint voting scopes.
Within a scope, model a single immutable proposal chain and each voter's durable accepted end.
Keep choices implied by these votes separate from learned confirmations.
Permit delayed old votes at unfenced recipients even after successor activation.
Compare recovering the greatest captured end with using the coordinator's learned end.
Compare intersecting scope fences, receiving reports without durable fences, and freezing every previous voter.
Validate the physically installed successor copies against the exact recovered history.

Isolate concurrent successor proposals with joint closure quorums that may use either constituency.
Compare ordered selection of one intent with locally irrevocable intent votes on either constituency or on the successor alone.
Treat the ordered choice as one authoritative decision.

Isolate payload loss after first recovery from three fixed old replicas.
Compare irrevocable binding to that first recovered cut with reselecting an exact candidate from another surviving quorum before installation.
Check unique authoritative installation separately from physical staging.
Each case abstracts transport authentication and integrity of accepted storage.

## Properties and acceptance

- Check that every previously or later confirmed predecessor choice is in the recovered image.
- Exhibit a previously unknown quorum choice that survives transfer, late completion of a covered predecessor quorum, and peer coverage across two changes.
- Check stable and joint quorum progress with one AZ unavailable.
- Exhibit two successor activations from disjoint closure quorums when those quorums select their own intent.
- Lose the only copy of a speculative longer tail after first recovery, then install a shorter safe cut. Refuse to expose two competing exact installation attempts as authoritative.
- Generalize the closure and transfer results to ranked ordinary ballots, arbitrary voter lists, and finite histories of changes.

## Tools and evidence

Use TLC 2.19 with one worker, a 512 MiB heap and a 60-second case limit.
Use Lean 4.35.0 and check deliberate rule weakenings.
Keep the general one-change state space and the focused joint interleavings separate.
Distinguish failure before versus after choosing the installation and compare strict physical quorum timing with exact prefix safety.
