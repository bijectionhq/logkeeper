# Study 43 · Reserve concurrent recovery across failure domains

2026-11-23

## Verdict

One physical pool can run out of space while the region has enough spare capacity in total.
Two moves can also deadlock if each holds a pool the other needs.
The capacity contract checks every pool and binds a complete vector to each exact source seal before it can take effect.
An atomic vector and ordered partial holds both satisfy the finite preparation comparison.
A durable exact abort returns partial holds by closing admission at each affected pool.
After sealing, neither restart nor a delayed timeout can reclaim the commitment.
A funded move can promote its exact recovered image while ordinary pools are full and the superseded copy is still charged.

## Properties and comparison

[ConcurrentLedger.tla](ConcurrentLedger.tla) counts ordinary use and two moves across two zones.
The normal case uses asymmetric vectors `(2, 1)` and `(1, 2)`.
Each zone has room for three or four abstract units.
Promotion reclassifies the reserved amount into resident and obsolete bytes, and the matching local disposition returns the obsolete charge.
The skew case begins with three ordinary units in zone 1, no ordinary use in zone 2, and a request for two units in each zone.
There are five units of total spare capacity and one spare unit in zone 1.

| Candidate case | Laws | Distinct states | Result |
| --- | --- | ---: | --- |
| Numeric ledger, capacity 3 in each zone | Pointwise bounds, exact reservations and obsolete charges, exact release, and eventual funded installation | 760 | Holds up to the bound |
| Numeric ledger, capacity 4 in each zone | Same laws | 1,680 | Holds up to the bound |
| Numeric ledger, old custodians unreachable | Same laws with old disposition disabled | 564 | Holds up to the bound |
| Numeric ledger, skewed ordinary usage | Same safety laws | 2 | Holds up to the bound |
| Atomic vector | Exclusive holds, complete sealed vectors, exact terminal decisions, refusal after closure, and both installs | 24 | Holds up to the bound |
| Ordered preparatory holds | Same laws | 43 | Holds up to the bound |
| Ordered holds with exact abort after restart | Same safety laws, durable abort reconciliation, and installation of the competing move | 108 | Holds up to the bound |

[PrepareVector.tla](PrepareVector.tla) uses two intents over two exclusive unit pools for all three preparation cases and for the unordered comparison.
The numeric ledger gives weak fairness to eligible funded promotion.
The preparation model gives weak fairness to eligibility for restart, acquisition, terminal decisions, installation, and abort reconciliation.
Installation ends the modeled prepare holds, so the two-install progress result uses reusable preparation space.
The numeric ledger separately charges continuing residency and old custody after promotion.

| TLC negative control | Shortest safety counterexample or temporal trace |
| --- | --- |
| Check only total capacity | One reservation in the skew case overfills zone 1. |
| Time out a sealed reservation | Reserve, seal, and abort. The seal loses its credits in three transitions. |
| Drop obsolete charge at promotion | Reserve, seal, and promote. The old bytes lose their charge in three transitions. |
| Accept release against a matching route | Install two moves, dispose one move's copy, and release the other's charge in eight transitions. |
| Forget charges at restart | Reserve and restart. The funded vector disappears in two transitions. |
| Charge for installation again | Fill ordinary room around a sealed vector. Promotion needs more of the full pool and the trace stutters. |
| Acquire holds in arbitrary order | Each move acquires the other move's missing pool. After restart, each waits and the trace stutters. |
| Seal a partial vector | Acquire one pool and seal in two transitions. |
| Reclaim a seal's local hold on timeout | Acquire both pools, seal, and reclaim one pool in four transitions. |
| Accept a prepare after closing its aborted identity | Restart, abort, fence an empty pool, and deliver a delayed prepare. It allocates capacity in four transitions. |

[CapacityLedger.lean](CapacityLedger.lean) proves the pointwise bounds and uniqueness of reservations over arbitrary finite histories.
Unrelated admission and advancement preserve the exact row of a funded move.
Given authenticated installation and placement charges that fit the declared footprint, promotion uses the existing reservation and retains the actual obsolete charge.
The composed recovery theorem links these laws to Study 42's ranked exact-cut installation with the original custodian state preserved.
The Lean disposition predicate scopes a whole row. The TLC ledger exercises disposition per zone.

[OrderedPrepare.lean](OrderedPrepare.lean) proves that requested resource ranks strictly increase along any wait path, so a cycle cannot occur.
It gives a two-intent counterexample for arbitrary ordering.
The terminal decision lemmas exclude a later abort after seal authorization, and exclude seal after abort.
The local trace lemmas preserve a complete bound vector before installation and keep a closed, empty pool closed against delayed preparation.
Lean checked twenty reported theorems using standard axioms only.
The three Lean negative controls caught omitting the incoming charge, accepting a foreign disposition, and ignoring an installed local refusal.

## Amendments

[A166–A170](../amendments.md#study-43--2026-11-23) require pointwise accounting, a durable complete seal commitment, acyclic preparation, exact local abort closure, and exact physical disposition.
Acyclic acquisition is independent of the choice of an atomic vector operation.
The opposite-order counterexample establishes the need for a cycle breaker when partial holdings can block one another.

## Acceptance programs

- P44, saturated restart. Admit one ordinary unit per zone and reserve and seal both moves. Restart with both zones at four units. Promote both moves and retain both obsolete charges with their custodians unreachable. TLC reached this in nine transitions.
- P44, skew and disposition. The pointwise admission guard refuses the skewed request. In a separate five-transition witness, install a funded move, verify its own obsolete copy's disposition, and release that local charge.
- P45, partial abort. Hold one pool for the first move and restart. Commit its abort and close its local hold. Let the second move acquire both pools and install. Deliver the first move's old prepare and refuse it at the closed pool. TLC reached this in nine transitions.

An atomic admission submits the complete vector as one operation.
An ordered admission sends one exact hold request per required pool and records their coverage before issuing the same seal authority.
Source seal and certified promotion use the same exact move identity under both candidates.

## Residue

The comparison separates numerical capacity and distributed preparation into two models.
The distributed refinement still needs to map each partial hold to a numeric charge, carry recovery evidence across changes to pool authority, and safely compact terminal identities while old requests remain in flight.
The numeric reference uses an abstract capacity profile and a certified-install premise. It needs a proof for the actual placement and physical dependency accounting.
The specialization to Study 42 assigns the old copy the selected cut's size. The generic profile supports distinct resident and obsolete footprints.
The aborted row in this numeric model denotes capacity already returned or reclassified by the physical accounting boundary.
[Study 48](../48-settlement-composition/report.md) composes that accounting boundary with logical abort and shows why pending writes prevent an immediate refund.
An implementation with unequal copies must measure or bound the incumbent independently, including writes already authorized for it.
Ordered acquisition excludes wait cycles among the modeled pools. New admission also needs a reachable resolver, available resources, and a scheduling policy that gives a waiting move a sustained opportunity to acquire them.
Liveness at permanent saturation is limited to work that already owns its required capacity.
These results cover design models.

## Reproduction

Run from the Logkeeper repository with TLC 2.19, Java 21.0.13+9, Lean 4.35.0, and Python 3.13.
TLC uses one worker, a 512 MiB heap, and a 60-second limit per case.
The runner checks the pinned TLC jar hash, records commands and raw traces in `.results/`, and runs the negative controls before the baselines.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/43-concurrent-capacity/run.py
```
