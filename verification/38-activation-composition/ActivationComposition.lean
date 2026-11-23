import IntentRetirement
import ObligationHome

set_option warningAsError true

namespace ActivationComposition

variable {Image : Type}

open IntentRetirement (CopyKey Store Evidence)

structure TargetCut (Image : Type) where
  gate : Reservation.Slot
  chosen : Nat → Option Image
  outcomes : Nat → Option Image
  serving : Nat → Option Image
  jobs : CopyKey → Option Image

def capture (store : Store Image) : TargetCut Image :=
  ⟨store.gate, store.chosen, store.outcomes, store.serving, store.jobs⟩

def restore (cut : TargetCut Image) (recorded : Nat → Option Image) : Store Image :=
  ⟨cut.gate, cut.chosen, cut.outcomes, recorded, cut.serving, cut.jobs⟩

abbrev Routing := ObligationHome.Home Unit Unit

structure State (Image : Type) where
  store : Store Image
  routing : Routing
  staged : Option (TargetCut Image)
  replies : Nat → Image → Prop
  fences : CopyKey → Image → Prop

def initial : State Image :=
  ⟨IntentRetirement.empty, ObligationHome.initial (fun _ => .absent),
    none, fun _ _ => False, fun _ _ => False⟩

def CanWrite (state : State Image) (owner : Nat) : Prop :=
  owner = state.routing.owner ∧ state.routing.sealed = false

def CopyRemovalsCertified (state : State Image) (after : Store Image) : Prop :=
  ∀ key image, state.store.jobs key = some image → after.jobs key ≠ some image → state.fences key image

def relocate (state : State Image) (cut : TargetCut Image) : State Image :=
  {state with
    store := restore cut state.store.recorded
    routing := ObligationHome.install state.routing state.routing.book
    staged := none}

def withSourceRecord (state : State Image) (id : Nat) (image : Image) : State Image :=
  {state with store := {state.store with recorded := IntentRetirement.update state.store.recorded id (some image)}}

inductive Step (evidence : Evidence Image) : State Image → State Image → Prop
  | target {state} (owner : Nat) (after : Store Image) (authority : CanWrite state owner)
      (valid : IntentRetirement.Step evidence state.store after)
      (leavesSource : after.recorded = state.store.recorded)
      (certifiedCleanup : CopyRemovalsCertified state after) :
      Step evidence state {state with store := after}
  | send {state} (id : Nat) (image : Image) (found : state.store.outcomes id = some image) :
      Step evidence state {state with replies := fun key value => (key = id ∧ value = image) ∨ state.replies key value}
  | sourceRecord {state} (id : Nat) (image : Image) (authentic : state.replies id image) :
      Step evidence state (withSourceRecord state id image)
  | providerFence {state} (key : CopyKey) (image : Image) (planned : state.store.jobs key = some image)
      (authentic : evidence.settledCopy key image) :
      Step evidence state {state with fences := fun oldKey oldImage =>
        (oldKey = key ∧ oldImage = image) ∨ state.fences oldKey oldImage}
  | sealOwner {state} (openBook : state.routing.sealed = false) (published : state.routing.locator = state.routing.owner) :
      Step evidence state {state with routing := {state.routing with sealed := true}}
  | stage {state} (sealed : state.routing.sealed = true) :
      Step evidence state {state with staged := some (capture state.store)}
  | install {state} (cut : TargetCut Image) (sealed : state.routing.sealed = true)
      (staged : state.staged = some cut) :
      Step evidence state (relocate state cut)
  | publish {state} (candidate : Nat) (installed : ObligationHome.CanPublish state.routing candidate) :
      Step evidence state {state with routing := ObligationHome.publish state.routing candidate}
  | stop {state} (owner : Nat) (covered : ObligationHome.CanStop state.routing owner) :
      Step evidence state {state with routing := ObligationHome.stop state.routing owner}

inductive Trace (evidence : Evidence Image) : State Image → State Image → Prop
  | same (state) : Trace evidence state state
  | next {first before after} : Trace evidence first before → Step evidence before after →
      Trace evidence first after

def StageSound (state : State Image) : Prop :=
  ∀ cut, state.staged = some cut → state.routing.sealed = true ∧ cut = capture state.store

def ReplySound (state : State Image) : Prop :=
  ∀ id image, state.replies id image → state.store.chosen id = some image

structure Sound (state : State Image) : Prop where
  activation : IntentRetirement.Sound state.store
  stage : StageSound state
  replies : ReplySound state
  route : ObligationHome.RouteSound state.routing

theorem initial_is_sound : Sound (initial : State Image) := by
  refine ⟨IntentRetirement.empty_is_sound, ?_, ?_, ObligationHome.initial_route_is_sound _⟩
  · intro cut impossible
    cases impossible
  · intro id image impossible
    cases impossible

theorem exact_target_cut_restores_against_the_live_source (store : Store Image) :
    restore (capture store) store.recorded = store := by
  exact Eq.refl store

private theorem duplicate_source_update (recorded : Nat → Option Image) {id : Nat} {image : Image}
    (known : recorded id = some image) : IntentRetirement.update recorded id (some image) = recorded := by
  funext observed
  by_cases matchesId : observed = id
  · subst observed
    simp [IntentRetirement.update, known]
  · simp [IntentRetirement.update, matchesId]

theorem every_step_projects_to_activation
    {evidence : Evidence Image} {before after : State Image}
    (sound : Sound before) (step : Step evidence before after) :
    IntentRetirement.Step evidence before.store after.store := by
  cases step with
  | target _ _ _ valid _ _ => exact valid
  | sourceRecord id image authentic =>
      have chosen := sound.replies id image authentic
      rcases sound.activation.preservesOutcome id image chosen with pending | recorded
      · exact .record id image pending
      · change IntentRetirement.Step evidence before.store
          {before.store with recorded := IntentRetirement.update before.store.recorded id (some image)}
        rw [duplicate_source_update before.store.recorded recorded]
        exact .restart
  | install cut _ staged =>
      have exactCut := (sound.stage cut staged).2
      change IntentRetirement.Step evidence before.store (restore cut before.store.recorded)
      rw [exactCut, exact_target_cut_restores_against_the_live_source]
      exact .restart
  | _ => exact .restart

def NoRoutingSettlement (_key _binding : Unit) : Prop := False

theorem every_step_projects_to_home_routing
    {evidence : Evidence Image} {before after : State Image}
    (step : Step evidence before after) :
    before.routing = after.routing ∨ ObligationHome.Step NoRoutingSettlement before.routing after.routing := by
  cases step with
  | sealOwner openBook published => exact Or.inr (.seal openBook published)
  | install _ sealed _ => exact Or.inr (.install before.routing.book sealed rfl)
  | publish candidate installed => exact Or.inr (.publish candidate installed)
  | stop owner covered => exact Or.inr (.stop owner covered)
  | _ => exact Or.inl rfl

theorem target_write_requires_current_revision
    {before : State Image} {owner : Nat} (authority : CanWrite before owner)
    (wrongOwner : owner ≠ before.routing.owner) : False := by
  exact wrongOwner authority.1

private theorem chosen_binding_persists
    {evidence : Evidence Image} {before after : Store Image} {id : Nat} {image : Image}
    (chosen : before.chosen id = some image) (step : IntentRetirement.Step evidence before after) :
    after.chosen id = some image := by
  cases step with
  | install fresh _ _ _ new _ =>
      by_cases matchesId : id = fresh
      · subst fresh
        rw [new] at chosen
        cases chosen
      · simpa [IntentRetirement.install, IntentRetirement.update, matchesId] using chosen
  | _ => exact chosen

private theorem stage_stays_exact
    {evidence : Evidence Image} {before after : State Image}
    (sound : StageSound before) (step : Step evidence before after) : StageSound after := by
  cases step with
  | target _ _ authority _ _ _ =>
      intro cut staged
      have closed : before.routing.sealed = true := (sound cut staged).1
      have openBook : before.routing.sealed = false := authority.2
      rw [closed] at openBook
      cases openBook
  | sealOwner _ _ =>
      intro cut staged
      exact ⟨rfl, (sound cut staged).2⟩
  | stage sealed =>
      intro cut staged
      exact ⟨sealed, (Option.some.inj staged).symm⟩
  | install _ _ _ =>
      intro cut impossible
      cases impossible
  | _ => exact sound

private theorem replies_stay_exact
    {evidence : Evidence Image} {before after : State Image}
    (sound : Sound before) (step : Step evidence before after)
    (projected : IntentRetirement.Step evidence before.store after.store) : ReplySound after := by
  cases step with
  | send id image found =>
      intro key value accepted
      rcases accepted with ⟨sameKey, sameValue⟩ | earlier
      · rw [sameKey, sameValue]
        exact sound.activation.outcomeExact id image found
      · exact sound.replies key value earlier
  | _ => exact fun id image accepted => chosen_binding_persists (sound.replies id image accepted) projected

theorem any_scope_preserves_both_reference_traces
    {evidence : Evidence Image} {first last : State Image}
    (sound : Sound first) (trace : Trace evidence first last) :
    Sound last ∧ IntentRetirement.Trace evidence first.store last.store ∧
      ObligationHome.Trace NoRoutingSettlement first.routing last.routing := by
  induction trace with
  | same => exact ⟨sound, .same _, .same _⟩
  | next _ step prior =>
      obtain ⟨priorSound, activation, routing⟩ := prior
      have projected := every_step_projects_to_activation priorSound step
      have routeStep := every_step_projects_to_home_routing step
      have routeSound := priorSound.route
      have routeProof := match routeStep with
        | .inl same => same ▸ routeSound
        | .inr routed => ObligationHome.step_preserves_route_soundness routeSound routed
      have routeTrace := match routeStep with
        | .inl same => same ▸ routing
        | .inr routed => ObligationHome.Trace.next routing routed
      exact ⟨⟨IntentRetirement.every_step_keeps_unacknowledged_exact_results priorSound.activation projected,
        stage_stays_exact priorSound.stage step, replies_stay_exact priorSound step projected, routeProof⟩,
        .next activation projected, routeTrace⟩

theorem a_chosen_unrecorded_result_survives_home_changes
    {evidence : Evidence Image} {first last : State Image} {id : Nat} {image : Image}
    (sound : Sound first) (trace : Trace evidence first last)
    (chosen : last.store.chosen id = some image) (unknown : last.store.recorded id ≠ some image) :
    last.store.outcomes id = some image := by
  have result := (any_scope_preserves_both_reference_traces sound trace).1.activation
  exact (result.preservesOutcome id image chosen).resolve_right unknown

theorem a_retired_handle_stays_closed_through_home_changes
    {evidence : Evidence Image} {first last : State Image} {id : Nat}
    (sound : Sound first) (trace : Trace evidence first last) (closed : Reservation.Stale id first.store.gate) :
    Reservation.Stale id last.store.gate :=
  IntentRetirement.a_retired_handle_cannot_reopen_after_any_trace closed
    (any_scope_preserves_both_reference_traces sound trace).2.1

private theorem activation_does_not_recreate_an_acknowledged_result
    {evidence : Evidence Image} {before after : Store Image} {id : Nat} {image : Image}
    (chosen : before.chosen id = some image) (cleared : before.outcomes id = none)
    (step : IntentRetirement.Step evidence before after) : after.outcomes id = none := by
  cases step with
  | install fresh _ _ _ notChosen _ =>
      by_cases matchesId : id = fresh
      · subst fresh
        rw [notChosen] at chosen
        cases chosen
      · simpa [IntentRetirement.install, IntentRetirement.update, matchesId] using cleared
  | acknowledge address _ _ _ =>
      by_cases matchesId : id = address <;> simp [IntentRetirement.update, matchesId, cleared]
  | _ => exact cleared

theorem an_acknowledged_result_stays_cleared
    {evidence : Evidence Image} {first last : State Image} {id : Nat} {image : Image}
    (sound : Sound first) (trace : Trace evidence first last)
    (chosen : first.store.chosen id = some image) (cleared : first.store.outcomes id = none) :
    last.store.chosen id = some image ∧ last.store.outcomes id = none := by
  induction trace with
  | same => exact ⟨chosen, cleared⟩
  | next prior step persistent =>
      have liveSound := (any_scope_preserves_both_reference_traces sound prior).1
      have projected := every_step_projects_to_activation liveSound step
      exact ⟨chosen_binding_persists persistent.1 projected,
        activation_does_not_recreate_an_acknowledged_result persistent.1 persistent.2 projected⟩

private theorem activation_keeps_durable_source_record
    {evidence : Evidence Image} {before after : Store Image} {id : Nat} {image : Image}
    (sound : IntentRetirement.Sound before) (recorded : before.recorded id = some image)
    (step : IntentRetirement.Step evidence before after) : after.recorded id = some image := by
  cases step with
  | record address value eligible =>
      by_cases matchesId : id = address
      · subst address
        have equal := Option.some.inj ((sound.outcomeExact id value eligible).symm.trans
          (sound.recordedExact id image recorded))
        subst value
        simp [IntentRetirement.update]
      · simpa [IntentRetirement.update, matchesId] using recorded
  | _ => exact recorded

theorem a_source_record_survives_every_later_home_change
    {evidence : Evidence Image} {first last : State Image} {id : Nat} {image : Image}
    (sound : Sound first) (trace : Trace evidence first last)
    (recorded : first.store.recorded id = some image) : last.store.recorded id = some image := by
  induction trace with
  | same => exact recorded
  | next prior step known =>
      have priorSound := (any_scope_preserves_both_reference_traces sound prior).1
      exact activation_keeps_durable_source_record priorSound.activation known
        (every_step_projects_to_activation priorSound step)

theorem provider_fences_survive_every_later_home_change
    {evidence : Evidence Image} {first last : State Image} {key : CopyKey} {image : Image}
    (trace : Trace evidence first last) (fenced : first.fences key image) : last.fences key image := by
  induction trace with
  | same => exact fenced
  | next _ step known =>
      cases step with
      | providerFence _ _ _ _ => exact Or.inr known
      | _ => exact known

theorem removing_a_live_copy_plan_requires_external_evidence
    {evidence : Evidence Image} {before after : State Image} {key : CopyKey} {image : Image}
    (sound : Sound before) (step : Step evidence before after)
    (planned : before.store.jobs key = some image) (changed : after.store.jobs key ≠ some image) :
    before.fences key image := by
  cases step with
  | target _ _ _ _ _ certifiedCleanup => exact certifiedCleanup key image planned changed
  | install cut _ staged =>
      have exactCut := (sound.stage cut staged).2
      change (restore cut before.store.recorded).jobs key ≠ some image at changed
      rw [exactCut, exact_target_cut_restores_against_the_live_source] at changed
      exact False.elim (changed planned)
  | _ => exact False.elim (changed planned)

theorem trace_preserves_exact_copy_plan_or_fence
    {evidence : Evidence Image} {first last : State Image} {key : CopyKey} {image : Image}
    (sound : Sound first) (trace : Trace evidence first last)
    (planned : first.store.jobs key = some image) :
    last.store.jobs key = some image ∨ last.fences key image := by
  have advance {before after : State Image} (valid : Sound before) (step : Step evidence before after)
      (pending : before.store.jobs key = some image) :
      after.store.jobs key = some image ∨ after.fences key image := by
    classical
    by_cases current : after.store.jobs key = some image
    · exact Or.inl current
    · have settled := removing_a_live_copy_plan_requires_external_evidence valid step pending current
      exact Or.inr (provider_fences_survive_every_later_home_change (.next (.same _) step) settled)
  induction trace with
  | same => exact Or.inl planned
  | next prior step known =>
      rcases known with pending | fenced
      · exact advance (any_scope_preserves_both_reference_traces sound prior).1 step pending
      · exact Or.inr (provider_fences_survive_every_later_home_change (.next (.same _) step) fenced)

theorem source_and_provider_can_finish_during_a_frozen_cut
    {evidence : Evidence Image} {before : State Image} {id : Nat} {key : CopyKey} {image copy : Image}
    (openBook : before.routing.sealed = false) (published : before.routing.locator = before.routing.owner)
    (result : before.store.outcomes id = some image) (planned : before.store.jobs key = some copy)
    (settlement : evidence.settledCopy key copy) :
    ∃ after, Trace evidence before after ∧ after.routing.stopped before.routing.owner ∧
      after.store.recorded id = some image ∧ after.fences key copy ∧
      after.store.outcomes id = some image ∧ after.store.jobs key = some copy := by
  let sent := {before with replies := fun address value =>
    (address = id ∧ value = image) ∨ before.replies address value}
  let sealed := {sent with routing := {sent.routing with sealed := true}}
  let staged := {sealed with staged := some (capture sealed.store)}
  let learned := withSourceRecord staged id image
  let fenced := {learned with fences := fun address value =>
    (address = key ∧ value = copy) ∨ learned.fences address value}
  let installed := relocate fenced (capture sealed.store)
  let located := {installed with routing := ObligationHome.publish installed.routing installed.routing.owner}
  let stopped := {located with routing := ObligationHome.stop located.routing before.routing.owner}
  have sentTrace : Trace evidence before sent := .next (.same _) (.send id image result)
  have stagedTrace : Trace evidence before staged :=
    .next (.next sentTrace (.sealOwner openBook published)) (.stage rfl)
  have externalTrace : Trace evidence before fenced :=
    .next (.next stagedTrace (.sourceRecord id image (.inl ⟨rfl, rfl⟩)))
      (.providerFence key copy planned settlement)
  have installedTrace : Trace evidence before installed := .next externalTrace (.install _ rfl rfl)
  have canPublish : ObligationHome.CanPublish installed.routing installed.routing.owner := by
    exact ⟨Nat.le_trans (Nat.le_of_eq published) (Nat.le_succ _), Nat.le_refl _⟩
  have canStop : ObligationHome.CanStop located.routing before.routing.owner := by
    exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _⟩
  have sealedCutStillExact : capture sealed.store = capture fenced.store := rfl
  have liveStore : installed.store = fenced.store := by
    change restore (capture sealed.store) fenced.store.recorded = fenced.store
    rw [sealedCutStillExact, exact_target_cut_restores_against_the_live_source]
  refine ⟨stopped, .next (.next installedTrace (.publish _ canPublish)) (.stop _ canStop),
    .inl rfl, ?_, .inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · change installed.store.recorded id = some image
    rw [liveStore]
    simp [fenced, learned, withSourceRecord, IntentRetirement.update]
  · change installed.store.outcomes id = some image
    rw [liveStore]
    exact result
  · change installed.store.jobs key = some copy
    rw [liveStore]
    exact planned

#print axioms initial_is_sound
#print axioms exact_target_cut_restores_against_the_live_source
#print axioms every_step_projects_to_activation
#print axioms every_step_projects_to_home_routing
#print axioms target_write_requires_current_revision
#print axioms any_scope_preserves_both_reference_traces
#print axioms a_chosen_unrecorded_result_survives_home_changes
#print axioms a_retired_handle_stays_closed_through_home_changes
#print axioms an_acknowledged_result_stays_cleared
#print axioms a_source_record_survives_every_later_home_change
#print axioms provider_fences_survive_every_later_home_change
#print axioms removing_a_live_copy_plan_requires_external_evidence
#print axioms trace_preserves_exact_copy_plan_or_fence
#print axioms source_and_provider_can_finish_during_a_frozen_cut

end ActivationComposition
