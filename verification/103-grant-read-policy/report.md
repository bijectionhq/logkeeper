# Study 103 · Bind the selective window to its writer grant

2026-11-23

## Verdict

Packed bytes alone cannot establish a read-window width.
The one-slot and two-slot empty windows encode identically, and each can decode the same bytes.
The grant's exact scope and chosen width have to be part of the recovery evidence.
Resizing a live window is unsafe when it discards a spent bit outside the new width.

The installed journal inherits the existing width on ordinary work and writer replacement.
A width change requires a positive bounded width authorized for the exact successor and applied in the same decision that installs that grant.
The command uses the existing journal authority and keeps the actual read and delivery body.
At recovery, validate an older checkpoint against its own certified grant, width, and cut, then apply the new policy from the exact chosen suffix.
This keeps historical replay independent of the current policy offer.

## Evidence

Lean 4.35.0 checked thirteen theorems with standard axioms only.

| Finding | Theorems and premises |
| --- | --- |
| Equal packed bytes have two distinct valid policy interpretations. | `bare_packed_bytes_can_alias_distinct_policy_widths` and `an_unqualified_checkpoint_can_open_under_both_widths` use the actual codec from Study 102. |
| With no policy offer, the underlying installed operation runs with the inherited width. A width offer takes effect only on an actual newer grant and with an authentic statement of its exact lineage, writer and requested bound. | `work_and_writer_recovery_inherit_the_existing_width_without_an_offer`, `an_offer_cannot_change_the_policy_inside_the_same_grant`, and `a_changed_width_requires_its_exact_authenticated_successor`. The existing ordered reducer supplies grant legality and frame ordering. |
| Spent invocations remain spent, and the same grant cannot return with a different width under arbitrary finite replay. | `every_decision_preserves_spent_exact_invocations` and `the_same_grant_has_the_same_width_after_any_replay`. The invariant is either the same policy with a monotone spent set, or an advanced grant. |
| The named checkpoint opens with the verified historical scope, exact width and ordered cut. The old certified base plus exact suffix replays the same combined state as the full chosen history. | `a_historical_open_authenticates_the_exact_grant_and_width_at_its_cut` and `a_certified_old_selector_applies_the_new_grant_policy_from_its_suffix`. The prior exact base certification and authenticated catalog remain required. |

The Lean negative control compares signed policies by width alone.
It fails the exact-binding law at its declared proof step.

TLC 2.19 exhausts seven bounded reference configurations with one or two usable identities, two grants, and at most one recovery.
Weak fairness covers eligible open, restore and replacement actions.
The confirmed outcomes include an unchanged writer with the offer service unavailable, a replacement inheriting its width through that outage, and an authorized width change.

| Deliberate weakening | Counterexample |
| --- | --- |
| Infer the width from packed size | A width-one checkpoint opens with width two in one transition. |
| Shrink a live grant and trim fallen-out sparse bits | Admit nonce two, shrink, admit nonce one, and admit nonce two again in four transitions. |
| Use a genuine offer for another grant | An unauthorized successor takes effect in one transition. |
| Release the old delivery when installing a width change | The independent delivery obligation disappears in one transition. |
| Demand the current policy for an older selector | Recovery stays blocked even with the historical state and chosen suffix available. |
| Require a live policy offer on ordinary reads | The installed grant cannot serve while the optional service is unavailable. |
| Require a live policy offer on writer replacement | A stable reachable journal cannot complete replacement when its current width could be inherited. |

## Amendments

[A408–A411](../amendments.md#study-103--2026-11-23) bind the width to the exact writer scope and historical cut, protect earlier spent bits, and keep unchanged-width service independent of fresh policy offers.

## Limits

This is a model of the installed decision, replay, and checkpoint authentication boundary.
The policy projection is typed and read from the same named control body.
The actual grant proof encoding, signer binding, authenticated historical verification material, and physical persistence remain deployment obligations.
Keep the format maximum stable during replay or recover the exact historical format bound with the chosen cut.
A live operator setting is insufficient for checking a historical width.
The study does not choose which Bijection caller scopes permit independent requests to overtake.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/103-grant-read-policy/run.py
```

[run.py](run.py) records the build, finite configurations, traces and proof diagnostics under .results/.
