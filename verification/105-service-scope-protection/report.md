# Study 105 · Separate a serving cut from its protection promise

2026-11-23

## Verdict

The installed journal can serve an exact surviving cut without classifying a missing AZ.
Reachability answers which inputs and voters the journal can use now.
The protection promise answers which losses acknowledged work can survive.
Keep those facts independent.
Use the full single-AZ envelope while the first physical loss is unknown, including when a cut excludes an AZ.
For fresh work, check exact recoverability before acknowledging.
For earlier work, retain certified custody until replacement preserves the promise.
A confirmed first loss retains the existing degraded path within that interval.
Requalification restores the full envelope and includes both current quorum and exact recoverability.

## Properties and comparison

Lean 4.35.0 checked ten theorems with standard axioms only.
`every_authorized_trace_preserves_assurance` proves preservation for arbitrary finite sequences of abstract serving selections, acknowledgments, copy changes, confirmed losses and renewals.
`identical_observations_cannot_offer_single_copy_progress_and_protection` proves that a journal which sees the same observations when A is lost and when A is slow cannot both promise to acknowledge B-only work in the lost-A world and protect it from a first loss of B in the slow-A world.
`two_distinct_copies_cover_any_single_loss` proves a sufficient witness for a replication layout.
The Lean control weakens the fresh acknowledgment rule and fails at the proof that admission preserves the full promise.

TLC 2.19 checked the following configurations.

| Policy and history | Evidence |
| --- | --- |
| Treat timeout of A as proof of AZ loss | Promise violation in two transitions. Observe B and C, open the cut and acknowledge the new B-only input. |
| Same policy with an actual first loss injected | Lost acknowledged input in three transitions. Open, acknowledge on B, then lose B. |
| Withdraw A's retained old copy just because the serving cut excludes A | Lost previous acknowledgment in three transitions. Open, withdraw A, then lose B. |
| Renew after obtaining voter readiness but without repaired coverage | Renewal violation in two transitions. Open under diagnosed loss of A, then renew with only B holding the prior input. |
| Omit exact inputs from cut readiness | Invalid cut in one transition. |
| Require the unresolved envelope when B is the only candidate location | Temporal counterexample to unconditional acknowledgment. Cut opening still passes with four states. |
| Preserve both obligations with an injected first physical loss | Safety holds in 37 distinct states. |
| Preserve the envelope and replicate the new input to B and C | Eventual acknowledgment with stable service holds in 10 states each for slow A and physically lost but unclassified A. |
| Use a verified first loss of A | A surviving copy in B suffices in the existing interval, with nine states checked under stable service. |
| Verify repair, then allow one more physical loss in the renewed interval | Safety holds in 29 distinct states. |
| Refuse a cut with a missing required input | Safety holds in the single reachable state. |

Weak fairness applies to cut opening, replication when configured, and acknowledgment when continuously eligible in the temporal comparisons.
The injected-loss and renewal cases are finite safety checks.
Separate bounded acceptance traces reach loss of B after safely replacing A's copy, and loss of B after verified renewal with new acknowledged work.

## Amendments and developer cost

[A417–A421](../amendments.md#study-105--2026-11-23) preserve the public guarantee and scope the service predicate independently.
The worker continues to send the same append and see the same acknowledgment.
Internally the journal opens the exact cut with B and C, then acknowledges new work only after obtaining the required durable coverage.
When the bytes are already durably placed in B and C, the quorum and data evidence can come from the same operation.
An object reference or checkpoint dependency needs its own exact coverage evidence when the quorum acknowledgments do not cover it.
While diagnosis is unavailable, a one-copy acknowledgment waits for another independent placement or authenticated evidence of which loss has already happened.
Reusing the retained copy's capacity waits for a safe replacement or other authorized disposition with the same coverage.

## Residue

The Lean model takes exact copies, complete inputs, current cut validation, verified diagnosis and renewal readiness as premises.
The TLC renewal stands in for a fully qualified new voter family and clears lost copies rather than reviving them.
Neither model checks provider authenticity, liveness under repeated changes, crash replay of the charged failure interval, atomic copy withdrawal at the effect boundary, or how repair earns enough protected capacity.
Compose the protection change with ordered reconfiguration and both crash-selectable roots before using it as a production guarantee.
A product that wants one-copy acceptance without a known loss would have to change the advertised fault envelope.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/105-service-scope-protection/run.py
```

[run.py](run.py) records each configuration, command and counterexample under .results/.
