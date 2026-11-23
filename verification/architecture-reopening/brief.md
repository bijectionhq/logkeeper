# Logkeeper architecture reopening

2026-11-23

The decision is whether a stable durable journal group with replica replacement meets the required RTDB operations, and which owner should coordinate actual cross-group capacity and storage effects when relocation is necessary.
The review follows Bijection's protocol design procedure at commit `c5232b7429f`.
[Bijection protocol design procedure](https://github.com/bijectionhq/bijection/blob/c5232b7429f/llm-wiki/wiki/protocol-design.md)

## Blind seed round

Three agents received the same requirements and no incumbent mechanism or peer proposal.
Each was asked for two or three structurally distinct seeds.
They used isolated conversation contexts and wrote no shared files.

## Shared contract issued to the agents

RTDB Multi is a regional multitenant database platform.
The journal returns an exact append request, range, and committed-prefix receipt.
Each stream incarnation has a single effective eligible writer, ordered expected-position fencing, and exact bounded reconciliation.
A fresh barrier returns an exact cut within its invocation.
A state watch can reopen a certified checkpoint below retention.
Authenticated trim retains exact reconstructability and protects replay suffixes and live borrows.

A stable reachable authority with recovery and capacity headroom continues through directory outage.
An eligible worker replacement can catch up and serve through that authority with the incumbent and fresh allocation service unavailable.
A genuinely authorized durability-placement change preserves all chosen bytes and results and excludes old extensions.
Funded work with a fully installed continuation can finish from retained evidence while old routes are unavailable.
Ordered retirement excludes fresh invocations.
Physical erasure has its own exact completion, after every original scope is disposed and late materialization is fenced.

The fault envelope is one AZ loss during a protected interval.
A new allowance requires verified repair.
The network can delay, lose, and duplicate messages, and directory, coordinator, and custodians can become unavailable.
Processes can crash and restart.
Authentication excludes forged effects and Byzantine participants.
Liveness premises include sustained eligibility, the necessary surviving scopes and routes, and fair service.

Shared tenant admission can expose contention.
Parked streams keep lightweight metadata.
Per-pool physical bytes, staging, retained results, retention and replay are finite.
Control and repair have reserved headroom.
Numeric throughput and latency budgets remain for the product owner and operator to set under Q01.

## Common histories and observables

| History | Shared schedule | Required observation |
| --- | --- | --- |
| H1 · Normal write and read | Install eligible holder, append with a lost response, order a fresh read, publish a reconstructable checkpoint, then trim past the original cursor. | Exact result or retained-floor response as applicable. The read returns an invocation-valid certified cut. No accepted command goes missing. |
| H2 · Worker and voter replacement | An old append has a hidden chosen certificate. A competing tail has staged physically. Lose one AZ, the incumbent worker, directory publication and fresh allocation. Keep the current group's surviving quorum, recovery inputs, and provisioned headroom. | Discover the chosen prefix from the reachable group, preserve the hidden choice and exact result, safely replace the worker, and exclude the rival and stale writer. Distinguish replacement of a worker from replacement of a required durability replica. |
| H3 · Opposite-pressure moves | Two deployments need different amounts from two physical pools. One pinned old reader survives installation. Lose the coordinator or one original route after preparation and again after valid installation. | Charge per pool including old and staged copies. Reject unsafe admission or make progress without a hold cycle. A fully covered installed move completes from its local evidence. Only the original scope returns its own charge. |
| H4 · Delayed physical write during retirement | Admit a staged write, delay its physical effect, close the deployment, and lose an original custodian. Try to certify completion, then deliver the old write. | Confirm ordered closure when the current authority can do so. Erasure stays pending until each scope has exact verified closure and disposition. A verified fence excludes late materialization. |
| H5 · Evidence or headroom exhausted | Stall checkpoint production or keep an admitted exact old replay pin. Remove one required exact attachment during recovery and fill ordinary admission. | Refuse unsafe recovery and ordinary work at the relevant bound. Retain the exact needed inputs and reserve enough control progress for valid cleanup. |

For every seed, name its decision owners, durable success event, and which authority is needed in each failure history.
Compare foreground and relocation round trips, pointwise peak bytes, independent unresolved debt, and the authorization applied at the physical write.
An exact historical event feed beyond the retained journal, an unconditional timing-isolated tier, a stricter deadline for overlapping reads, and an additional AZ fault before repair require separate product decisions.

## Exit

Preserve all seed records and compare every seed with the incumbent against H1–H5 before shortlisting.
Retain a simpler reference and a structural alternative with a clear observation that could reject each.
Mark model results, mathematical limits, unqualified assumptions, and proposed product-contract changes separately.
