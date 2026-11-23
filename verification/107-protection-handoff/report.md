# Study 107 · Carry protection through a move and its storage effects

2026-11-23

## Verdict

The allowance belongs to the deployment's continuing protection obligation.
Moving to another ordering group in the same regional failure domain changes the placement while carrying the deployment's incarnation, exact interval and obligations.
The target may activate on the original spent allowance with an exact locally verified seal and current protection.
A later authorized renewal is a separate decision.
The target may accept a confirmation of the unchanged interval when the physical loss happened after the source sealed.
Other deployments in the target group retain their own intervals.

Activation can rely on surviving original custody.
A source copy leaves the protection witness set when the corresponding withdrawal is durably authorized.
Subsequent requests check the resulting survivor set, including every previously authorized withdrawal whose effect may still arrive.
The original custodian applies the exact physical generation and retains the debit until verified disposition.

## General proofs

Lean 4.35.0 checked twelve theorems with standard axioms only.
`cross_group_install_refines_the_existing_fence_and_carries_protection` composes the original logical move and destination membership proof with the exact seal-bound interval, acknowledged input set and surviving custody.
`a_ready_target_can_install_without_renewing_the_interval` constructs the protected installation under the inherited allowance.
`a_source_confirmation_can_use_the_carried_interval` proves a confirmation scoped to the same deployment and interval still applies after transfer.
`installation_and_reserved_withdrawals_protect_the_original_promise` proves surviving physical coverage for every inherited failure case after any finite trace of withdrawal authorizations, effects and collection.
It uses the certified initial witness set and charged custody as premises.
One Lean control removes the equality on the frozen interval.
The other enables a physical withdrawal without an issued reservation.
Both fail at their intended proof obligation.

## Bounded comparisons

The tests use one acknowledged input, three AZs, one source and successor, and a neighboring deployment.
The withdrawal comparison additionally allows a physical address to be reused at a fresh generation.
For temporal move checks, weak fairness applies to stable enabled steps, including source disconnection and, where configured, delivery of valid loss evidence.

| Weakened rule | Shortest failure or temporal result |
| --- | --- |
| Reset the interval at activation, accept a stale control body at the same data frontier, or overwrite a neighbor's interval | Four transitions each to an invalid activation. |
| Recontact the source or require full healthy renewal before activation | Two separate temporal counterexamples with a funded and ready survivor. |
| Release original A on activation with only B covering the input | Lose B in six transitions from the initial source and lose an acknowledged input. |
| Authorize against physical copies that are still present even though withdrawal has already been approved | Authorize A and C against the same three-copy layout, apply both effects, then lose B. Five transitions. |
| Count two physical copies in the same AZ as independent coverage | Authorize and apply removal of A, then lose B and both remaining copies. Three transitions. |
| Execute delayed deletion using the location alone | Authorize removal of A's original version, install a new generation at its address, then deliver the old effect. Three transitions. |

| Reference case | Bounded evidence |
| --- | --- |
| Carry the spent allowance after the source disappears | Eventual acknowledgment under the inherited allowance, six states. |
| Lose A after seal and confirm at the installed target | Eventual acknowledgment with a matching confirmation, ten states. |
| Present rival control at the same data frontier | Refusal with three reachable states. |
| Activate while exact coverage still depends on original custody | Safety holds in ten states. A seven-transition witness additionally stages C, releases A, loses B and keeps C. |
| Reserve against pending withdrawals | Safety holds in 20 states. The two-transition witness authorizes and completes an eligible exact effect. |
| Refuse remaining copies in the same failure domain | Safety holds in four states. |
| Late effect matches only the original generation | Safety holds in 44 states. |

## Amendments and integration

[A428–A433](../amendments.md#study-107--2026-11-23) record the carried interval, the distinction between activation and reclamation, and the exact ordered witness rule.
P216 and P217 carry and confirm the original interval under the successor.
P218 moves the protected copy before authorizing release, and P219 exercises delayed and competing withdrawals.
There is no new RTDB caller operation.

The study reran Studies 11 and 13 against the current kernel.
Study 11's old active-writer retirement proof needed one compatibility change after the kernel added fenced vacancies.
The proof now supplies the active-writer case of the widened retirement premise.
Both original runners passed their reference cases and controls.

## Residue

The proof needs complete enumeration of all obligations and exact versions.
In particular, a placement's seal, each selectable checkpoint and each original borrow can have its own dependency on the same physical version.
The implementation must compose their reservations at the real custody and effect authority, preserve pending authorizations through crash recovery, and settle exact dispositions before credit reuse.
The model assumes a common regional AZ mapping and exact stable provider actions.
It abstracts canonical seal framing, transfers across different regional fault domains, end-to-end authenticated reservations and physical headroom qualification.
The effect trace keeps the installed obligation set and loss policy fixed.
A concurrent change to that set or policy needs the same witness treatment.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/107-protection-handoff/run.py
```

[run.py](run.py) saves configurations, counterexamples and proof diagnostics under .results/.
