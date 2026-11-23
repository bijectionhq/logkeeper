# Study 72 · Pool-local physical identities and joint recovery

2026-11-23

## Verdict

A source plans logical reservations by original pool incarnation, exact custody key, role, and required footprint.
The pool chooses the physical version only when it grants the reservation and charges the extent.
The pool uses its own durable sequence.
The physical identity includes the original pool incarnation, so different pools can issue the same local serial.
The reservation's original receipt identifies the exact allocated extent.
The source seal binds the resulting exact paid allocation vector for activation and historical replay.

The pool's ranked recovered cut includes the gate, physical debits, their outstanding provider work, and the local allocator watermark.
A replacement owner restores these from the same certified cut before accepting work.
Closing a scope leaves its physical debit in place until the existing exact disposition rule permits refund.

## Bounded comparison

[LocalIssuance.tla](LocalIssuance.tla) checks two pools of capacity three and three preauthorized plans with mixed sizes.
The older plan stays undelivered while a later plan at the same pool and an independent plan at the other pool first try to prepare.
TLC checked four safety invariants and one liveness property in separate baselines of 52 distinct states each.
The liveness check assumes weak fairness for each continuously eligible preparation and for delivery of the delayed request once its condition is met.
All three plans have enough local capacity in this scenario.
A six-transition witness prepares the later and independent plans at serial 1 in their respective pools.
It fences the later scope with its debit still present, changes that pool's owner, and accepts the delayed old plan under the replacement at serial 2.

| Weakening | Counterexample |
| --- | --- |
| Fix physical versions at plan issue | The other pool prepares, but the newer plan at the affected pool cannot take its preassigned second serial while the first plan remains undelivered. No fair local step can resolve that dependency. |
| Use a bare local serial as a physical identity | Two independently prepared plans at different pools collide after two transitions. |
| Restore a stale allocator | Prepare, fence, and take over with an earlier counter while retaining the original grant history. The durable identity is now beyond the recovered watermark. Three transitions. |
| Restore stale debits | Prepare, fence, and take over without the original physical charge. The applied preparation has lost its backing. Three transitions. |
| Restore a stale admission gate | Prepare, fence, and take over without the fence. The exact old admission scope reopens. Three transitions. |

## General proofs

[PoolState.lean](PoolState.lean) checks twelve theorems.
Eligible preparation creates the exact grant, local sequence advance, and positive byte charge together.
Exact retry resolves to one current physical row for the original custody key.
Other pools cannot change eligibility or the resulting local version.
Preparations at distinct pools commute.
Arbitrary interleavings preserve exact paid grants, the local capacity bound, and monotone issuance.
The exact closed key remains refused across authorized gate operations, including floors and rollover.
The number of outstanding charged rows is bounded by the positive charges and pool capacity.
A paid extent persists through later decisions unless the original physical version has verified stable absence.

[PoolTakeover.lean](PoolTakeover.lean) checks three theorems.
The same exact history selects one joint image.
The existing ranked handoff and quorum rules make the earlier chosen history a prefix of the current installed one through arbitrarily many owner changes.
Any later recovery majority contains a voter with that installed basis.
Valid replay from the prior exact cut preserves the fence, nondecreasing allocator, and exact charged scope unless its verified disposition has occurred.
The Lean negative control drops the pool incarnation from physical identity and fails the cross-pool noncollision law.

## Amendments

[A282–A284](../amendments.md#study-72--2026-11-23) replace preassigned physical order with local minting, separate plan identity from realized allocation identity, and require joint recovery of all pool ownership state.

## Acceptance coverage

- P123 and P124. A newer local preparation and a preparation at another pool can finish ahead of an older delayed plan. After a fence and takeover, the delayed plan receives the next local serial while the fenced original charge remains.
- P125. Recover the exact gate, issuer watermark and physical debit at the same cut. The general proof allows legitimate intervening disposition.
- P126. Retry a live preparation and resolve its one charged physical row. Reuse of a local serial in another pool yields a different immutable identity.

## Residue

The ranked proof uses exact, authenticated voted and installed image evidence and valid local transitions.
The list of successor images is the reference semantics for each ordered record.
An implementation can encode commands and periodic bounded checkpoints after proving that its decoder produces exactly those images.
Voter durability, exact physical custody of each selected image, and the current fault envelope are supplied by the other models and still need a single composed recovery proof.

Earlier funded seal and regional models bind a plan to already named physical extents.
The new proof derives the identity of a charged local row when that row is granted.
The source certificate must bind realization of the logical plan by the exact receipts, and replay the original vector after any loss of the coordinator or pool route.
The reference proof joining that certificate to the funded source, activation, and physical settlement remains open.
Regional shared reads and eviction must use the full pool-incarnation-plus-serial identity.
A production allocator with finite counters needs the existing exhaustion and incarnation rollover contract.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configuration, theorem checks, and failing traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/72-pool-local-issuance/run.py
```
