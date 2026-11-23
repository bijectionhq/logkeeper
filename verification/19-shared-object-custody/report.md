# Study 19 report · Custody of shared checkpoint objects

2026-11-22

## Verdict

Admit each manifest under durable registrations for all reachable physical versions.
A snapshot keeps the root's registration alive while it can discover dependencies.
Each version's custodian orders new references and reads against its disposal fence.
A release of an exact root-version interest is terminal even if it reaches the custodian before acquisition.
Provider deletion uses the exact fenced identity.

A surviving fork can continue using a version after the parent withdraws its own reference.
Erasing the source residence then requires independent verified coverage for that fork before withdrawal of its reference.
Deployment-scoped erasure covers the retired deployment's custody and authority.
Erasure of content that a surviving fork is entitled to read is a different requirement and conflicts with that entitlement.

## TLC results

The five safety invariants and the conditional disposal property hold across 6,324 distinct states with two roots and 79,868 states with three.
Both bounds include two exact physical versions that can share a name, one outstanding physical borrow, delayed acquisition, stale scans, and an interruptible provider link.
Authorized deletion eventually settles when its provider link becomes stably available and the deletion action is weakly fair.
A permanently inaccessible provider gives a temporal counterexample to unconditional settlement.

| Amendment | Mutation | Shortest safety counterexample |
| --- | --- | --- |
| A57 | `skip_dependency` | Prepare, acquire only one of two required versions, and publish. Four transitions. |
| A57 | `release_live_root` | Release the parent's existing live root dependency. One transition. |
| A58 | `stale_scan` | Prepare and send a registration, scan the unreferenced version, then accept the registration. Fence disposal from the scan. Five transitions. |
| A58 | `accept_during_disposal` | Prepare and send a registration, scan and fence the version, then accept the delayed registration. Five transitions. |
| A59 | `unfenced_release` | Send a reference registration, close the root, and release the exact interest. The late registration then resurrects it. Five transitions. |
| A60 | `ignore_borrow` | Borrow an already registered version, close the root, release its last reference, and fence disposal against the still-active read. Eleven transitions. |
| A60 | `delete_by_key` | Fence an unreferenced version, then delete by key and remove a distinct required version. Three transitions. |

A nine-transition witness publishes a fork before the parent withdraws and admits its read of the shared version afterward.
A five-transition witness consumes a delayed registration after an early release and observes refusal.
A nineteen-transition witness publishes a replacement root before the surviving fork withdraws its old root, drains an old borrow, and removes the source version.
The latter uses a pre-existing replacement version and checks custody and transition order.
Validating the replacement bytes and installing their verified content is a separate premise.

## General proofs and composition

Thirteen [Lean theorems](SharedCustody.lean) use only standard axioms.
For arbitrary finite traces, every live root and active physical borrow keeps its exact physical versions.
Released references stay closed under arbitrary delayed actions, and a fenced version never reopens.
Once a version is unreferenced and unborrowed, the erasure program affects only that version's physical presence.
The live-fork theorem rules out erasing a version while the fork still needs it.

The product trace projects to the earlier snapshot admission machine.
A logical root can enter the catalog's ready state only after every physical dependency is registered.
The physical root cannot close while its logical registration remains ready.
For each admitted snapshot, all versions reachable through any finite dependency path remain present.
The proof covers shared subgraphs and arbitrary depths in the immutable dependency graph.
Weakening closure completeness, terminal reference release, or physical close against the logical catalog breaks the matching Lean law.

## Residue

The model treats provider version identity and bytes bound to that identity as trusted.
The RTDB graph verifier still needs to prove complete enumeration of the actual manifest, including inherited members and pack indices.
The provider boundary must authenticate version-specific registration, release, copy equivalence, and disposition and must settle outstanding writes under the erasure contract.
[Study 22](../22-residence-transfer/report.md) checks the abstract exact-copy and publication contract for relocation.
Physical borrow counting assumes exact admitted operations and outcome evidence from the endpoint.

Independent registration allows different custodians to stage the closure without an atomic cross-provider write.
The root authority needs a durable, replayable preparation and close record for all outgoing interests.
[Study 20](../20-registration-recovery/report.md) checks cancellation recovery and compaction of reference fences within an established channel.
Authorization across erasure domains remains a refinement obligation.
RTDB's existing lineage and owner fences are a concrete strategy for rehome and deletion.
This study checks the version-scoped contract those fences or a finer-grained custodian must satisfy.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/19-shared-object-custody/run.py
```
