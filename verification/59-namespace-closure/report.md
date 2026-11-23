# Study 59 · Close the provisioning authority

2026-11-23

## Verdict

Keep an already provisioned authority at the storage effect boundary while its subordinate namespaces are created and retired.
The root reserves a finite guard plan for the new scope.
Creating a guard atomically checks the exact current namespace and its provisioning state.
Each child guard belongs to that namespace and planned address.
Publish the namespace for service after the complete guard plan is present.

Closing the root excludes new provisioning and new child grants.
An old funded child write can still land before its own effect fence.
Fence and clear each original child, then obtain stable disposition of all other original provider effects.
Once the namespace is exactly empty, the retirement decision removes its live scope from the provider root.
An already empty namespace can make the same terminal decision atomically without waiting for a queued create to answer.
The root's durable issuance watermark excludes that create and any delayed use after reuse of the address.

## Bounded comparison

[NamespaceClosure.tla](NamespaceClosure.tla) models one root location, up to two successive namespaces, one or two planned child guards, buffered and replayed creates, child payloads, and an independent auxiliary obligation per slot.
One booked namespace covers its original guards, possible effects, and bytes until exact settlement.
The checker tracks recorded proof identities, submitted requests, and auxiliary settlement history.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Two namespaces and one planned slot | 201 | All five safety laws hold. |
| Two namespaces and two planned slots | 6,839 | The same laws hold with multiple independent guards. |
| Permanently stalled create, seal first | 4 | All safety laws and eventual retirement and refund hold under the stated fairness. |
| Permanently stalled create, atomic empty cancellation allowed | 4 | The same safety and progress laws hold. |

The two temporal cases start with one issued create that can never land and an empty bank.
The modeled closure and refund authority stays available, and weak fairness applies to sealing, finishing, and refunding.
The cases give conditional progress at that bound.

| Weakening | Shortest counterexample or temporal result |
| --- | --- |
| Dispatch an unrestricted create after an earlier admission check | Reserve, send, finish the empty namespace, and deliver the old create. Four transitions. |
| Match the address without the namespace generation | Queue a create, close and refund the old namespace, reserve the next, and apply the old create. Six transitions. |
| Certify an empty observation | Reserve and certify a namespace while its provisioning scope still accepts work. Two transitions. |
| Arm new child work after the parent seal | Reserve, send, seed, seal, and arm. Five transitions. |
| Omit independent auxiliary work | Materialize and publish a guard, register an auxiliary obligation, then clear the guard and close the bank while that obligation remains. Nine transitions. |
| Wait for every earlier create to respond | A permanently stalled create keeps the closure gate disabled, even though the authority can fence new creation. |

## General proofs

[NamespaceClosure.lean](NamespaceClosure.lean) checks ten theorems using standard axioms only.
The model uses a finite index type for the planned slots and imports the guarded child reducer.
Live guards remain associated with the exact current root and planned addresses.
Serving requires every guard, and sealing disables new child allocation while preserving the older child reducer's settlement rules.
Removing a child after it is vacant preserves the previous closure contract for every issued child write.

An exact terminal namespace has no owned guard at any planned address.
The retirement exclusion persists through arbitrary finite traces of restart and later registration, using the root watermark and live scope.
Finishing requires exact auxiliary closure evidence.
An authorized, exactly empty bank can finish and exclude its queued creates before those requests respond.
The terminal evidence remains bound to that original scope through replacement and supplies the namespace-closure premise of the Study 55 incarnation settlement.
Returning the inventory slot still requires that scope's independent accounting to be clear.
The Lean controls fail if exact root identity is removed from seeding or auxiliary evidence is omitted from finishing.

## Amendments

[A227–A230](../amendments.md#study-59--2026-11-23) bind provisioning at the durable root, preserve old closure through reuse, reconcile empty cancellation with sealed draining, and include every child and auxiliary effect in terminal evidence.

## Acceptance programs

- P86. Close a funded, exactly empty namespace with a queued create. Keep the old proof and open the next namespace at the same location while the old create remains undelivered. TLC finds this in eight transitions. Lean proves the delayed creation remains refused.
- P87. Seal a namespace after a guard has landed and auxiliary work is outstanding. Close and dispose the original guard and settle that auxiliary work before returning capacity. TLC finds this in eleven transitions.
- P88. Let an old funded child write land after the parent seals and before the child fence. TLC reaches it in seven transitions with the original charge still present.

## Residue

The root in this study is an existing durable authority outside the individual pool namespaces it retires.
Root bootstrap or permanent shutdown is a separate authority operation.
The atomic provider creation primitive consults the root at the actual guard materialization boundary.
A root-side reservation followed by an unrestricted provider create does not satisfy that premise.
Provider-specific fencing, external provisioning permissions, full auxiliary enumeration, and certified recovery of the root remain refinement and qualification work.
Auxiliary closure is exact, permanent evidence for the recorded scope.
The physical accounting and read obligations determine when individual child disposal can be authorized.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner saves exact tool commands, diagnostics and traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/59-namespace-closure/run.py
```
