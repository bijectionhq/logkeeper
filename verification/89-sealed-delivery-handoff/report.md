# Study 89 · Transfer unfinished delivery at the exact seal

2026-11-23

## Verdict

A sealed move can carry outstanding paid deliveries through loss of the predecessor journal.
One authenticated attachment carries the exact read section, the writer's consumed invocation floor, and the independently funded delivery book, including its lineage-wide issuance floor.
The predecessor validates the attachment against the applied seal's actual control state before accepting the seal.
The successor reopens the attachment named by the sealed journal and validates the complete dependency set before applying the existing ordered installation.
The original physical custodian continues to own the borrow.

Two same-data-frontier cuts can disagree on outstanding deliveries, even if they contain the same application data.
Taking the highest data LSN cannot recover this control state.
A reachable and fully funded successor can activate with local durable evidence after the source disappears.
A delivery still needs its own original held borrow to complete, and reclaiming its slot requires evidence of stable completion or effective stop at the original custodian.

## Properties

Lean 4.35.0 checked the following for arbitrary finite book sizes with standard axioms.

| Property | Evidence and premises |
| --- | --- |
| The exact named control reopens both books and the consumed writer floor. Independent delivery extent coverage is required after logical read closure. | `an_exact_control_opens_both_books_and_the_writer_floor`, `opening_one_control_authenticates_the_original_dependencies_of_both_books`. The sound book encodings fit their declared size. The authenticated envelope resolves through a catalog of immutable named objects. |
| A prospective ordered seal is admitted only if the seal's own mounted attachment matches the actual sealed read and delivery state and exact ordered position. | `choosing_a_seal_checks_its_mounted_books_and_floor_against_the_applied_cut`, `mount_uses_only_the_named_attachment_at_the_seal_position`. The original reducer must accept the funded seal. |
| Source-to-target activation preserves every delivery row, its original physical identity, and the lineage-wide issuance floor. | `source_to_target_preserves_each_delivery_and_the_issuance_floor`. The modeled target has the same immutable authenticated catalog for the chosen move. The target runs the existing ordered authority and writer-floor transition. |
| Local preparation and valid ordered installation suffice for activation. A missing original independent extent prevents it. | `a_local_mounted_cut_and_valid_install_are_sufficient_for_activation`, `activation_refuses_a_missing_independent_delivery_extent`. The authentic seal, valid install and durable local dependencies have already arrived. |
| The target can finish the exact original packet with the authenticated original caller and original live borrow. The active target may apply exact stable settlement of that borrow, and the sealed predecessor refuses. | `an_activated_target_can_finish_the_original_paid_delivery`, `an_activated_target_can_apply_the_original_providers_settlement`, `the_sealed_predecessor_cannot_order_settlement`. Physical availability, signer authority and stable stop evidence are provider premises. |

The Lean mutation removes the equality between the staged and applied delivery books while leaving the other comparisons intact.
The law requiring equality of the delivery books fails at the equality proof.

## Comparison

TLC 2.19 exhaustively checked the configured finite histories.
Fairness grants an eventually enabled local transition.
The model's transfer starts with two distinguishable cuts at data end 7, one delivery slot, an older spent serial and one still outstanding.
The move source can disappear after the durable seal.
Invalid-cut scenarios present stale or split candidates at mount to compare whether the candidate can become active.

| Scenario | Corrected design | Weakened design and shortest failure |
| --- | --- | --- |
| Valid cut, then source outage | Completes the original paid delivery in 6 distinct states. | Requiring source recontact stutters forever after `Seal → LoseSource → Mount`. |
| Stale control at the same data frontier | Refuses the stale attachment in 4 distinct states. | Comparing data frontiers accepts the wrong ordered control after `Seal → LoseSource → Mount → Activate`. |
| Split control at the correct ordinal | Refuses the mixed attachment in 4 distinct states. | Checking the ordinal alone installs an older floor after `Seal → LoseSource → Mount → Activate`. |
| Missing original extent after read closure | Refuses the uncovered mount in 4 distinct states. | Counting only live read dependencies allows activation with missing custody after `Seal → LoseSource → Mount → Activate`. |
| Original stop evidence at the successor | Settles and refuses old serial reuse in 8 distinct states. | Reparenting the physical identity loses custody at activation after 4 transitions. Resetting the delivery floor admits spent serial 1 after `Seal → LoseSource → Mount → Activate → Stop → Settle → RetrySerial`. |
| Sealed predecessor receives settlement | The target consumes settlement in its own order. | Letting the sealed source clear reaches `Seal → OldAuthorityClear` and acknowledges a change absent from the sealed cut. |

## Amendments

Use [A351–A354](../amendments.md#study-89--2026-11-23) for the source admission, local installation, counter scope and settlement rules.

## Acceptance programs

1. Authorize a paid delivery, close the original read, then choose a move at the same data LSN.
   Seal one control attachment covering both books and floors.
   Lose the source after the target has installed durable local copies of the dependencies.
   Activate and reproduce the original packet from the still-held borrow.
2. Present an earlier delivery book at that same data LSN, or combine a current read section with an earlier delivery floor.
   Refuse the candidate.
3. Present the authentic sealed control with an original delivery extent missing even though no read slot references it.
   Refuse activation.
4. Receive the original custodian's exact terminal evidence.
   The sealed source refuses an ordered clear, and the installed successor clears that row in its own order.
   Retry a spent delivery serial and refuse it.

## Residue

The pure reference reuses the existing ordered reducers, but the combined seal admission still needs binding to the actual chosen frame and replay interpreter.
The Lean source-to-target composition assumes an immutable named catalog shared in meaning by both sites.
It abstracts replication of that catalog and validation from separately reconstructed stores.
It also abstracts complete dependency enumeration, the live provider acquisition and stop protocol, signer authority, the canonical bytes of the whole attachment, and the bytes and quota accounting for simultaneous copies.

A stop can disable reply use before its proof reaches the current ordered owner.
The move needs either retained charged recovery custody or a proved transition that can consume authentic terminal evidence before dropping that dependency.
The current model requires custody during activation and applies settlement afterward.
The next comparison should model a stop arriving during the sealed interval with independent provider and journal outages, and test a terminal-evidence substitution against that conservative path.

## Reproduction

From the Logkeeper checkout, run the following with Python 3.13, Java 21 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/89-sealed-delivery-handoff/run.py
```

[run.py](run.py) records the per-case commands, model configurations, counterexamples, and proof output under `.results/`.
TLC checks seven weakened designs before its five baseline runs.
The Lean runner verifies a deliberately failing law before checking the thirteen reference theorems.
