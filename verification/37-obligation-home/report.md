# Study 37 report · Move the home of unresolved activation obligations

2026-11-23

## Verdict

Give each activation handle a stable home independent of its physical owner.
Transfer the exact outstanding book under the existing authority seal, preserving the original physical keys and result bindings.
Keep one monotone locator binding for the home.
Publish a successor only after its exact cut has installed.
Once fresh discovery can reach that successor independently, the old coordinating endpoints can shut down while the source and custodian are unavailable.

A permanently inaccessible locator before publication can prevent safe planned shutdown.
Continuous ownership churn can starve retries even with a reachable locator.
Reconciliation requires a usable ownership interval or an equivalent guarantee that a complete, authorized exchange will get through.

## Bounded comparison

TLC explored one home, one retained result, one unresolved plan at an exact original custodian key, and up to four sequential owners.
The model separates the installed owner, published locator, cached client address, and stopped endpoint set.
Seal, transfer, installation, locator publication, source record, and provider fence are atomic actions at their respective boundaries.
The seven safety invariants cover book exactness, charges, exact discharge, publication of installed owners, survival of the current owner, locator continuity across shutdown, and terminal absence.

| Candidate and setting | Owners | Distinct states | Checked result |
| --- | ---: | ---: | --- |
| Stable home, reachable | 2 | 196 | Seven safety laws, installation, predecessor shutdown, and reconciliation hold. |
| Stable home, reachable | 4 | 2,028 | Same laws hold. |
| Stable home, source and provider down | 4 | 100 | Seven safety laws, installation, and predecessor shutdown hold. |
| Stable home, counterparts return after predecessor shutdown | 4 | 119 | Seven safety laws, installation, shutdown, and conditional reconciliation hold. |
| Stable home, locator down | 3 | 64 | Seven safety laws and installation of a sealed cut hold. |
| Forwarding through predecessors | 3 | 173 | Five shared safety laws, installation, and predecessor shutdown hold. |
| Keep forwarders while debts remain, reachable | 3 | 105 | Five shared safety laws, installation, predecessor shutdown, and reconciliation hold. |

The authority cases schedule install, publish, lookup refresh, shutdown, and counterpart work with weak fairness.
The bound on owner changes makes ongoing sequences of moves finite.
The separate churn projection checks the premise that this hides.
With two Boolean variables and weak fairness, TLC finds a cycle that alternates successful address refresh and a move.
Each refresh exposes a delivery opportunity, but the next move invalidates it.
With strong fairness of the delivery action, the completion property holds over the three reachable states.
That check identifies a progress premise for delivery.

## Counterexamples and amendments

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A140 | `omit_result`, `omit_plan`, `rebind_plan`, `forget_charge` | Install in three transitions while losing an obligation, changing its physical key, or forgetting its charge. |
| A140 | `stale_image`, `post_seal_discharge` | Install a previously discharged obligation from an out-of-date cut in five transitions. |
| A140 | `assume_settled` | Discharge without a durable source record or original custodian fence in one transition. |
| A141 | `publish_before_install` | Point discovery at a merely sealed or staged successor in two transitions. |
| A141 | `regress_locator` | Replay an earlier publication after shutting down the old endpoint and make it the advertised route in six transitions. |
| A141 | `stale_is_missing` | Synthesize terminal absence at a cached old address in four transitions. |
| A142 | `stop_before_publish` | The only published endpoint stops in four transitions. |
| A142 | Forwarding through predecessors | After the origin shuts down, a stale client cannot resolve the current owner even with the source and provider available. A debt stays charged forever. |
| A142 | Keep forwarders while debts remain | Both counterpart paths are down, and the old forwarders cannot shut down even after later owners install. |
| A143 | Locator unavailable before publication | Exact install finishes. Independent route publication and planned shutdown remain blocked. |
| A144 | Weak fairness under continuous churn | A fair refresh and move cycle overtakes each attempted exchange. |

The fifteen-transition outage witness transfers both debts across three owner changes and shuts down all predecessors while both counterpart paths remain unavailable.
The twenty-one-transition recovery witness starts with the same outage and the original cached route.
After every predecessor stops, the cache refreshes directly to the last owner and both counterparts reconnect.
The source durably records the original result and the original custodian fences the copy key.
The new owner then discharges both exact obligations.

## General proofs

Lean checked thirteen theorems with standard axioms only. [Proof source](ObligationHome.lean)
The authorized route stays monotone over arbitrary finite traces, never names an uninstalled version, and excludes each stopped predecessor.
The current discovery decision checks the live locator binding and current owner reachability without requiring retired endpoint records.
The exact booked obligation survives any such trace until its own exact authorized settlement.
The model constructs a handoff and shutdown that preserve the entire book without waiting for settlement.
A source starting from an exact pending record can retrieve that binding through the published reachable current owner after any number of changes, provided the settlement evidence has yet to exist.

A pure forwarding chain needs the original endpoint.
If all independent evidence is unavailable, two executions with different exact results give the same observation, so no total reconciler returns both correct answers from that observation.
The Lean schedule also constructs arbitrarily many fresh lookups each overtaken by the next owner change.
The four proof controls fail at their expected sites after weakening exact installation, exact settlement, the shutdown guard, and the outage observation.

## Remaining obligations

The distributed authority proof must refine the certified cut and logical home identity to the actual replicated state, including the admission issuance fence.
The locator needs its own fault envelope, monotone update and recovery contract.
The comparator assumes reserved successor capacity, a finite owner bound in the main model, and one copy and result.
The Lean model uses the stopped-owner predicate and exact discharged labels to record history for theorems.
The design's locator has one binding per home and keeps no per-owner forwarding records.
The proof leaves byte accounting, lifecycle of the logical home namespace, and authenticated cross-service retry and dispatch to refinement.
The modeled shutdown removes coordinating endpoints.
Moving or destroying an original physical custodian still requires its separate custody protocol.
[Study 38](../38-activation-composition/report.md) composes routing and activation histories when source and custodian evidence arrives during staging.

Apply [A140–A144](../amendments.md#study-37--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner writes configurations, commands, checker traces, and proof diagnostics to the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/37-obligation-home/run.py
```
