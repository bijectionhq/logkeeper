# Study 04 · Terminal retirement and physical erasure

## Question

Can a stream close with a quorum while accurately distinguishing physical erasure from a cleanup that still needs custody access?

## Sources

Use S08 and P08 from the [requirements](../requirements.md) and RTDB's `DroppedStreamsAreTerminal` invariant.
Use the prior handoff study for the distinction between serving authority and every location that still holds or could receive a copy.

## Model and comparisons

Record an authorized copy destination before sending bytes.
Delivery can occur before or after the stream closes.
Local durable fences serialize with writes at each location.
Once a location is fenced, it erases existing data and can certify that delayed writes will be refused.
Model three or four possible locations, independently reachable, with one initially holding data.
Compare against cleanup of present bytes without fencing, omitted custody reservations, discarding fences early, and majority-only cleanup.

A logically closed stream admits no new copy reservations.
Physical erasure requires a disposition for every inventoried location.
The model assumes trusted local evidence and eventual fair processing for reachable locations.
It abstracts legal and provider-specific definitions of deletion, media inspection, ciphertext or key retention, clocks, and retirement during a live cross-group transfer.

## Properties

| Property | Kind | Required behavior |
| --- | --- | --- |
| `CustodyKnown` | Safety | Every resident or in-flight copy has an inventoried destination. |
| `ErasureStable` | Safety | A completion receipt implies a closed stream with no resident copies, and later delivery preserves absence. |
| `AllAcknowledged` | Safety | Every inventoried location was accounted for before completion. |
| `ProgressWithAccess` | Liveness | Every requested erasure completes when all actual custody locations eventually stay accessible under weak fairness. |
| `ProgressWithMajority` | Competing liveness claim | Erasure completes with a surviving majority even if a recorded location stays inaccessible. |

## Rules

Use the shared pinned TLC runner and the Lean 4.35.0 pin within the study.
Run mutations before the baseline, then test both liveness claims and a delayed-delivery acceptance trace.
The [report](report.md) records model bounds, programs, counterexamples, and limits.
