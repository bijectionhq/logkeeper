# Study 79 · RTDB failover on an installed Logkeeper group

2026-11-23

## Verdict

The common reference now executes the successful path of P142 over the ranked chosen source.
An authenticated route to the installed lineage and placement suffices to request a higher grant.
Recovery keeps the chosen append and receipt even with a rival staged payload present.
An eligible successor gets the exact fence cut, reconciles the retained original result, refuses the rival at the same position, and can serve a fresh marker after materializing its cut.
The first new append uses the existing extent and the next paid byte and log positions.

A genuine result under the correct writer can still be stale for a new invocation.
The receiving gate needs both an exact invocation match and a non-reused invocation identity.
A cached grant cut cannot substitute for a fresh ordered marker.

## Bounded comparison

[RTDBFailover.tla](RTDBFailover.tla) chooses the original append on two of three AZs before exploring loss of each AZ.
A rival can be staged in the third AZ and carries no choice.
The incumbent and other control dependencies stay unavailable for the continuation.
The model includes one older authentic marker under the successor, a fresh invocation, and a delayed append from the old writer.
The original receipt is retained and the original paid window has room for one new append.
The proof of progress uses weak fairness for losing an AZ and then recovering, granting, reconciling, catching up, ordering and serving the marker, refusing the stale attempt, and appending.
The missing-coverage run checks safety only.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Exact surviving coverage | 128 | All seven invariants hold. The trace eventually reconciles and appends against the original window under the stated fairness. |
| Missing exact attachment | 5 | The group offers no replacement grant or append from the incomplete recovered scope. |

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Recover from available staging | Lose one of the chosen AZs and accept the surviving rival as the choice in three transitions. |
| Confirm a retry by position alone | Reconcile a different request as committed in five transitions. |
| Keep old writer authority after replacement | Accept a stale writer's delayed append in five transitions. |
| Ignore the invocation identity | Serve using the earlier authenticated marker in eight transitions. |
| Reuse the previous invocation identity | The ordinary equality check accepts the earlier authentic marker in eight transitions. |
| Serve before applying the inherited cut | Deliver a correctly chosen fresh marker and serve before local replay in eight transitions. |
| Replace the original paid window | The first new append uses a different window in ten transitions. |
| Ignore missing exact coverage | Start recovery from an incomplete scope in three transitions. |
| Require directory contact | The reachable and funded journal cannot grant the replacement. TLC finds a temporal counterexample. |
| Require fresh allocation | The recovered worker reaches the barrier but the next append can stall forever. TLC finds a temporal counterexample. |

## General proofs

[RTDBFailover.lean](RTDBFailover.lean) checks nine theorems with standard axioms only.
It uses the actual chosen source, ranked recovery, writer fence, retained receipt book, and funded append reducers.

The direct route gate rejects a different lineage or placement.
The append lemma derives its exact committed payload, original receipt, and spent byte position from admitted source checks.
Ranked replay uses the chosen suffix and excludes extra unchosen bytes.
Recovery with a missing exact suffix is refused.
A successful grant keeps the retained results and the original funding.

The marker lemma derives the exact nonce and applied data cut from the ordered command.
The receiving gate checks authenticity, the exact current invocation, and availability of a materialized protected cut.
The independence counterexample shows why equality alone cannot protect a recycled invocation identity.
A previous authenticated result can satisfy all other delivery checks even when its marker predates the later call.

The composed P142 theorem starts from an arbitrary exact image before the hidden append and a certified selected base.
It proves ranked reopen, grant, exact receipt and rival refusal, fresh-marker delivery after the named apply step, and the next append against the original extent and advanced cursor.
The selected base may already include the hidden append or recover it from the exact local suffix.
The theorem assumes concrete route and result attestations, exact retained receipt eligibility, stage availability, current keeper eligibility, and fresh append headroom.
The finite model separately checks progress under each single AZ fault and exercises a genuinely stale writer attempt.

## Amendments

[A312–A314](../amendments.md#study-79--2026-11-23) make direct route authentication and exact reconciliation explicit, bind successful barrier delivery to a non-reused invocation, and keep the same paid append path through failover.

P142 is checked in the reference under the named premises.
P149 covers the earlier genuine marker and identity reuse.
Existing rules still distinguish retained reconciliation from SQL outcomes after trim.
If required bytes or staging headroom are missing, the availability premise for new service has failed.

## Residue

The run does not qualify the network, voter media, provider scopes, client-side nonce allocation, deployment eligibility signatures, or SQL checkpoint materialization.
An integration needs to bind the actual read-marker certificate to its invocation and committed result.
It must obtain that marker through the installed journal and materialize its exact cut using the existing snapshot and replay custody rules.
The current RTDB Multi Allium target still uses directory CAS and a new loglet at Claim.
An RTDB integration must refine that path to the stable-group contract before it can qualify P142 at runtime.

## Reproduction

Run with TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner checks the negative controls first and retains commands, configurations, and raw logs under .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/79-rtdb-failover/run.py
```
