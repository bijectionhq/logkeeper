# Study 93 · Atomically capture and authorize first use

2026-11-23

## Verdict

Atomic first use can remove an ordered decision for an explicit recoverable read while preserving its original result and the independent lifetime of its first delivery.
The viable candidate delegates a prepaid physical credit before selection, then binds it to the exact applied basis in the same journal decision as capture.
A proof that is already tied to the previously selected checkpoint can be overtaken again at every attempt.
The split program can avoid that race by keeping the already captured basis protected while preparing first use.

Delegation introduces a specific ownership obligation.
The original provider cannot withdraw an unassigned credit while the installed journal may still choose it.
An exact unused fence permits the original charge to be returned.
On assignment that charge backs the resulting borrow until exact completion or effective stop.
The installed owner can fence an unused delegation after its original writer is replaced.

Use the split path as the reference for independently staged exact operations.
Keep atomic first use as a candidate when existing standing custody can cheaply supply enforceable delegated credits across eligible view changes.
Ordinary markerless observations and later reissue retain their own admission paths.

## General proofs

Lean 4.35.0 checked eleven theorems with standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| One applied command publishes the exact original read capture and its separately retained first delivery. | `an_open_publishes_its_exact_capture_and_independent_delivery_together` invokes the existing ordered admission reducer and returns its exact marker and paired read state. It inserts the delivery entry and the same command position in the bounded book. |
| Prepaid coverage is checked on the chosen basis. A previously funded view does not authorize a different uncovered view. | `a_credit_for_a_previous_uncovered_basis_cannot_authorize_current_capture`, `one_prepaid_credit_can_cover_the_exact_current_basis_without_preselecting_a_position`. The provider's scope is authentic and coverage denotes the exact full role-specific basis. |
| Missing delivery room refuses the whole open. The tentative capture does not spend the nonce or change either book. | `a_missing_delivery_slot_refuses_the_whole_open`. The refusal advances only the command position under the existing source reducer. |
| Assignment and unused fencing are mutually exclusive for the exact serial. Old grant replacement does not prevent the current owner from fencing an exact unused credit. | `a_chosen_unused_fence_preserves_outstanding_rows_and_refuses_delayed_open`, `an_assigned_credit_can_no_longer_be_fenced_as_unused`, `the_current_owner_can_fence_unused_credit_after_writer_replacement`. The exact unused fence authorization is authentic and the credit key remains non-reused in the original lineage. |
| The resulting delivery completes from its own held original borrow. Replay with either certified checkpoint reconstructs the exact chosen open and fence history. | `successful_open_can_finish_from_its_own_exact_borrow`, `any_exact_checkpoint_and_suffix_reproduce_the_same_atomic_open_and_fence_history`. Installed provider protection and immutable replay inputs remain premises. |

The Lean control removes the applied-basis coverage field.
The law requiring coverage of that exact basis fails at its proof step.

## Comparative models

TLC 2.19 explored ten reference configurations and reproduced seven safety and three temporal counterexamples.
One read and one delivery credit are in scope.
The churn case schedules advancement between preparation and each applied attempt.
Two labels distinguish views, and every advancement invalidates the fixed preparation even when the earlier label recurs.
The model uses weak fairness within this chosen schedule.
The split variant assumes its initial logical capture can reserve from current registered custody and preserve the selected basis until the later grant.

| History | Comparison |
| --- | --- |
| Stable ready view | Fixed and delegated fusion each finish in 4 distinct states. |
| Advance between preparation and choice | Fixed fusion retries forever. Split completes in 8 states and uses two successful read-related decisions. Delegated fusion completes in 5 states and uses one. |
| Accept the overtaken fixed ticket or ignore a missing coverage role | The wrong basis or unbacked assignment violates safety in 3 transitions each. Delegated reference refusal with uncovered basis takes 4 states. |
| Fence and return before a delayed open | The reference refuses in 5 states. Using cached credit admits against returned funding in 4 transitions. |
| Provider releases charge independently of the journal | The view remains apparently eligible to the group, which can choose an unfunded delivery in 3 transitions. |
| Replace the original writer before deciding the unused credit | The installed owner fences the credit and the original provider can return it in 6 states. Requiring the old writer produces a temporal failure. |
| No delivery room | Reference refusal preserves the logical capture state in 3 states. Applying the capture alone violates atomicity after 2 transitions. |
| Retry after assignment | Reference finishes without reuse in 5 states. Weakening either repeat-assignment rejection or the unused fence check violates safety in 3 transitions. |
| Lose the journal after choosing first use | The protected operation finishes in 5 states. Requiring another journal response causes a temporal failure. |

The decision count excludes staging, unused-credit reconciliation, checkpoint rotation, physical reads and bytes.
The candidate result therefore establishes a possible command-count gain, not an end-to-end performance gain.

## Amendments

Use [A368–A372](../amendments.md#study-93--2026-11-23) for the conditional fused path and its custody boundary.

## Acceptance programs

1. Prepare a valid credit, advance to a second covered ready root, then open.
   Choose the exact current capture and the paid first delivery together.
   Recover both after the original authorizer is lost and finish from the exact still-held borrow.
2. Advance to an uncovered root or exhaust delivery capacity.
   Refuse the fused open without consuming a logical read or delivery row.
3. Replace the original writer with an eligible successor, then order the unused fence with the installed owner and return the original charge.
   Refuse a delayed open or a replayed allocation at the same key.
4. Assign the credit before proposing an unused fence.
   Refuse unused credit return and retain the normal exact completion or stop path.

## Residue

The credit in the proof is an authenticated delegation, rather than a speculative token or a fresh provider contact.
Compose its physical allocation, coverage across window publication, original metadata retention, and replayable assignment or return certificate with the existing pool and handoff models before promoting the candidate.
A selected view that lacks delegated backing remains ineligible.
A progress claim under continuous rotation needs a separate proof that the advertised serving windows never outrun the paid coverage, that another demand does not repeatedly consume the exact key, and that both slots and scheduling are available.
The fixed-view temporal counterexample does not rule out a different protocol that certifies and reserves an earlier valid cut before choice, with corresponding API and protection semantics.

## Reproduction

From the Logkeeper checkout, use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 verification/93-atomic-read-capture/run.py
```

[run.py](run.py) saves the command lines, model configurations and raw output in .results/.
