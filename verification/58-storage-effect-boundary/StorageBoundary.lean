import ProviderIOClosure

set_option warningAsError true

namespace StorageBoundary

variable {Location Payload Ticket : Type}

structure Binding (Location : Type) where
  location : Location
  serial : Nat

inductive Body (Payload : Type) where
  | vacant
  | armed
  | written (payload : Payload)
  | fenced (payload : Option Payload)

def Body.armedNow : Body Payload → Bool
  | .armed => true
  | _ => false

def Body.data : Body Payload → Option Payload
  | .written payload => some payload
  | .fenced payload => payload
  | _ => none

structure Slot (Location Payload : Type) where
  location : Location
  issued : Nat
  body : Body Payload

def MayMaterialize (slot : Slot Location Payload) (permit : Binding Location) : Prop :=
  permit.location = slot.location ∧ permit.serial = slot.issued ∧ slot.body.armedNow = true

def writeIfLive [DecidableEq Location] (slot : Slot Location Payload) (permit : Binding Location)
    (payload : Payload) : Option (Slot Location Payload) :=
  if permit.location = slot.location ∧ permit.serial = slot.issued ∧ slot.body.armedNow = true then
    some {slot with body := .written payload}
  else none

theorem a_successful_put_uses_the_live_scoped_permission [DecidableEq Location]
    {slot next : Slot Location Payload} {permit : Binding Location} {payload : Payload}
    (accepted : writeIfLive slot permit payload = some next) :
    MayMaterialize slot permit ∧ next = {slot with body := .written payload} := by
  unfold writeIfLive at accepted
  split at accepted
  next eligible =>
    cases accepted
    exact ⟨eligible, rfl⟩
  next => simp at accepted

inductive Step [DecidableEq Location] (funded closeAllowed : Binding Location → Prop) :
    Slot Location Payload → Slot Location Payload → Prop
  | arm {slot} (vacant : slot.body = .vacant) (paid : funded ⟨slot.location, slot.issued + 1⟩) :
      Step funded closeAllowed slot {slot with issued := slot.issued + 1, body := .armed}
  | put {slot next} (permit : Binding Location) (payload : Payload)
      (accepted : writeIfLive slot permit payload = some next) :
      Step funded closeAllowed slot next
  | fence {slot} (live : slot.body ≠ .vacant) (allowed : closeAllowed ⟨slot.location, slot.issued⟩) :
      Step funded closeAllowed slot {slot with body := .fenced slot.body.data}
  | clear {slot} (payload : Option Payload) (closed : slot.body = .fenced payload) :
      Step funded closeAllowed slot {slot with body := .vacant}
  | restart {slot} : Step funded closeAllowed slot slot

def Retired (slot : Slot Location Payload) (permit : Binding Location) : Prop :=
  permit.location = slot.location ∧ 0 < permit.serial ∧
    (permit.serial < slot.issued ∨ permit.serial = slot.issued ∧ slot.body = .vacant)

variable [DecidableEq Location] {funded closeAllowed : Binding Location → Prop}

theorem slot_changes_preserve_location_and_monotone_issuance {slot next : Slot Location Payload}
    (step : Step funded closeAllowed slot next) :
    next.location = slot.location ∧ slot.issued ≤ next.issued := by
  cases step with
  | arm => exact ⟨rfl, Nat.le_succ _⟩
  | put _ _ accepted =>
      obtain ⟨_, rfl⟩ := a_successful_put_uses_the_live_scoped_permission accepted
      exact ⟨rfl, Nat.le_refl _⟩
  | fence | clear | restart => exact ⟨rfl, Nat.le_refl _⟩

private theorem a_slot_change_preserves_retirement {slot next : Slot Location Payload}
    {permit : Binding Location} (closed : Retired slot permit) (step : Step funded closeAllowed slot next) :
    Retired next permit := by
  have shape := slot_changes_preserve_location_and_monotone_issuance step
  refine ⟨closed.1.trans shape.1.symm, closed.2.1, ?_⟩
  rcases closed.2.2 with older | ⟨same, vacant⟩
  · exact .inl (Nat.lt_of_lt_of_le older shape.2)
  · cases step with
    | arm => exact .inl (same ▸ Nat.lt_succ_self _)
    | put _ _ accepted =>
        have live := (a_successful_put_uses_the_live_scoped_permission accepted).1.2.2
        simp [vacant, Body.armedNow] at live
    | fence live _ => exact False.elim (live vacant)
    | clear _ stored => rw [vacant] at stored; cases stored
    | restart => exact .inr ⟨same, vacant⟩

inductive Trace (funded closeAllowed : Binding Location → Prop) :
    Slot Location Payload → Slot Location Payload → Prop
  | same (slot) : Trace funded closeAllowed slot slot
  | next {first before after} : Trace funded closeAllowed first before → Step funded closeAllowed before after →
      Trace funded closeAllowed first after

theorem retirement_stays_closed_across_clear_restart_and_reuse {first last : Slot Location Payload}
    {permit : Binding Location} (closed : Retired first permit) (trace : Trace funded closeAllowed first last) :
    Retired last permit := by
  induction trace with
  | same => exact closed
  | next _ step prior => exact a_slot_change_preserves_retirement prior step

theorem a_retired_permission_cannot_materialize {slot : Slot Location Payload}
    {permit : Binding Location} (closed : Retired slot permit) (payload : Payload) :
    writeIfLive slot permit payload = none := by
  have impossible : ¬ MayMaterialize slot permit := by
    intro admitted
    rcases closed.2.2 with older | ⟨_, vacant⟩
    · exact (Nat.ne_of_lt older) admitted.2.1
    · have armed := admitted.2.2
      simp [vacant, Body.armedNow] at armed
  cases applied : writeIfLive slot permit payload with
  | none => rfl
  | some _ => exact False.elim (impossible (a_successful_put_uses_the_live_scoped_permission applied).1)

def EffectClosed (slot : Slot Location Payload) (permit : Binding Location) : Prop :=
  Retired slot permit ∨
  permit.location = slot.location ∧ 0 < permit.serial ∧ permit.serial = slot.issued ∧
    ∃ payload, slot.body = .fenced payload

private theorem a_slot_change_preserves_effect_closure {slot next : Slot Location Payload}
    {permit : Binding Location} (closed : EffectClosed slot permit) (step : Step funded closeAllowed slot next) :
    EffectClosed next permit := by
  rcases closed with retired | ⟨location, known, serial, bytes, fenced⟩
  · exact .inl (a_slot_change_preserves_retirement retired step)
  · cases step with
    | arm vacant => rw [vacant] at fenced; cases fenced
    | put _ _ accepted =>
        have live := (a_successful_put_uses_the_live_scoped_permission accepted).1.2.2
        simp [fenced, Body.armedNow] at live
    | fence => exact .inr ⟨location, known, serial, _, rfl⟩
    | clear => exact .inl ⟨location, known, .inr ⟨serial, rfl⟩⟩
    | restart => exact .inr ⟨location, known, serial, bytes, fenced⟩

theorem a_fenced_permission_is_refused_after_any_trace {first last : Slot Location Payload}
    {permit : Binding Location} (closed : EffectClosed first permit) (trace : Trace funded closeAllowed first last)
    (payload : Payload) : writeIfLive last permit payload = none := by
  have result : EffectClosed last permit := by
    induction trace with
    | same => exact closed
    | next _ step prior => exact a_slot_change_preserves_effect_closure prior step
  rcases result with retired | ⟨_, _, _, _, fenced⟩
  · exact a_retired_permission_cannot_materialize retired payload
  · cases applied : writeIfLive last permit payload with
    | none => rfl
    | some _ =>
        have live := (a_successful_put_uses_the_live_scoped_permission applied).1.2.2
        simp [fenced, Body.armedNow] at live

def exactBody (slot : Slot Location Payload) (permit : Binding Location) : Body Payload :=
  if permit.location = slot.location ∧ permit.serial = slot.issued then slot.body else .vacant

private def blockedProvider (present : Bool) : ProviderIOClosure.State Unit :=
  ⟨false, true, fun _ => .unused, false, fun _ => False, present, false, true, none⟩

def provider (slot : Slot Location Payload) (permit : Binding Location) : ProviderIOClosure.State Unit :=
  match exactBody slot permit with
  | .vacant => blockedProvider false
  | .armed => ⟨true, false, fun _ => .pending, false, fun _ => False, false, false, true, none⟩
  | .written _ => ⟨true, false, fun _ => .done, false, fun _ => False, true, false, true, none⟩
  | .fenced payload => blockedProvider payload.isSome

theorem a_conditional_put_refines_the_atomic_provider_effect {slot next : Slot Location Payload}
    {permit : Binding Location} {payload : Payload}
    (accepted : writeIfLive slot permit payload = some next) :
    ProviderIOClosure.Step (fun _ => True) (provider slot permit) (provider next permit) := by
  obtain ⟨⟨location, serial, armed⟩, rfl⟩ := a_successful_put_uses_the_live_scoped_permission accepted
  have exact : slot.body = .armed := by
    cases body : slot.body <;> simp [body, Body.armedNow] at armed ⊢
  have canWrite : ProviderIOClosure.MayWrite (provider slot permit) () := by
    simp [ProviderIOClosure.MayWrite, provider, exactBody, location, serial, exact]
  have landed := ProviderIOClosure.Step.effect (reserve := fun _ => True) () canWrite
  have consumed : ProviderIOClosure.writeStatus (fun _ : Unit => .pending) () .done =
      (fun _ : Unit => ProviderIOClosure.Status.done) := by
    funext ticket
    cases ticket
    simp [ProviderIOClosure.writeStatus]
  simpa [provider, exactBody, location, serial, exact, consumed] using landed

theorem a_retired_slot_body_has_stable_absence {slot : Slot Location Payload} {permit : Binding Location}
    (closed : Retired slot permit) : ProviderIOClosure.StableAbsence (provider slot permit) := by
  have empty : exactBody slot permit = .vacant := by
    rcases closed.2.2 with older | ⟨_, vacant⟩
    · simp [exactBody, Nat.ne_of_lt older]
    · simp [exactBody, vacant]
  simp [ProviderIOClosure.StableAbsence, ProviderIOClosure.MayWrite, provider, empty, blockedProvider]

def CompleteDisposition {Auxiliary : Type} (slot : Slot Location Payload) (permit : Binding Location)
    (copies : Auxiliary → ProviderIOClosure.State Ticket) : Prop :=
  Retired slot permit ∧ ∀ copy, ProviderIOClosure.StableAbsence (copies copy)

omit [DecidableEq Location] in
theorem unsettled_staging_blocks_complete_disposition {Auxiliary : Type}
    {slot : Slot Location Payload} {permit : Binding Location}
    {copies : Auxiliary → ProviderIOClosure.State Ticket} (copy : Auxiliary) (ticket : Ticket)
    (pending : ProviderIOClosure.MayWrite (copies copy) ticket) :
    ¬ CompleteDisposition slot permit copies := by
  intro complete
  exact (complete.2 copy).2.2 ticket pending

omit [DecidableEq Location] in
theorem a_retained_copy_blocks_complete_disposition {Auxiliary : Type}
    {slot : Slot Location Payload} {permit : Binding Location}
    {copies : Auxiliary → ProviderIOClosure.State Ticket} (copy : Auxiliary)
    (present : (copies copy).present = true) :
    ¬ CompleteDisposition slot permit copies := by
  intro complete
  exact Bool.false_ne_true (((complete.2 copy).2.1).symm.trans present)

theorem a_vacant_slot_can_be_reused_with_the_old_permission_still_closed
    {slot : Slot Location Payload} {old : Binding Location}
    (vacant : slot.body = .vacant) (retired : Retired slot old)
    (paid : funded ⟨slot.location, slot.issued + 1⟩) :
    ∃ next, Step funded closeAllowed slot next ∧
      writeIfLive next ⟨slot.location, slot.issued + 1⟩ = (fun payload => some {next with body := .written payload}) ∧
      ∀ payload, writeIfLive next old payload = none := by
  let next : Slot Location Payload := {slot with issued := slot.issued + 1, body := .armed}
  have transition : Step funded closeAllowed slot next := .arm vacant paid
  refine ⟨next, transition, ?_, fun payload => a_retired_permission_cannot_materialize
    (a_slot_change_preserves_retirement retired transition) payload⟩
  funext payload
  simp [writeIfLive, next, Body.armedNow]

#print axioms a_successful_put_uses_the_live_scoped_permission
#print axioms slot_changes_preserve_location_and_monotone_issuance
#print axioms retirement_stays_closed_across_clear_restart_and_reuse
#print axioms a_retired_permission_cannot_materialize
#print axioms a_fenced_permission_is_refused_after_any_trace
#print axioms a_conditional_put_refines_the_atomic_provider_effect
#print axioms a_retired_slot_body_has_stable_absence
#print axioms unsettled_staging_blocks_complete_disposition
#print axioms a_retained_copy_blocks_complete_disposition
#print axioms a_vacant_slot_can_be_reused_with_the_old_permission_still_closed

end StorageBoundary
