import Reservation

set_option warningAsError true

namespace IntentRetirement

variable {Image : Type}

structure CopyKey where
  intent : Nat
  custodian : Nat
  attempt : Nat
  deriving DecidableEq

structure Store (Image : Type) where
  gate : Reservation.Slot
  chosen : Nat → Option Image
  outcomes : Nat → Option Image
  recorded : Nat → Option Image
  serving : Nat → Option Image
  jobs : CopyKey → Option Image

structure Evidence (Image : Type) where
  sealed : Nat → Option Image
  aborted : Nat → Prop
  abortExcludesSeal : ∀ id, aborted id → sealed id = none
  ready : Store Image → Nat → Image → Prop
  room : Store Image → Prop
  admittedCopy : CopyKey → Image → Prop
  settledCopy : CopyKey → Image → Prop
  adoptedElsewhere : Nat → Image → Prop

def empty : Store Image :=
  ⟨⟨0, none⟩, fun _ => none, fun _ => none, fun _ => none, fun _ => none, fun _ => none⟩

def update [DecidableEq Key] (store : Key → Value) (key : Key) (value : Value) : Key → Value :=
  fun observed => if observed = key then value else store observed

def mint (state : Store Image) : Store Image :=
  {state with gate := ⟨state.gate.issuedThrough + 1, some (state.gate.issuedThrough + 1)⟩}

def closeAdmission (state : Store Image) : Store Image :=
  {state with gate := {state.gate with live := none}}

def CanRetire (evidence : Evidence Image) (state : Store Image) (id : Nat) : Prop :=
  evidence.aborted id ∨ ∃ image, state.chosen id = some image

def SourceHasRecord (state : Store Image) (id : Nat) (image : Image) : Prop :=
  state.recorded id = some image

def install (state : Store Image) (id : Nat) (image : Image) : Store Image :=
  {state with
    chosen := update state.chosen id (some image)
    outcomes := update state.outcomes id (some image)
    serving := update state.serving id (some image)}

inductive Step (evidence : Evidence Image) : Store Image → Store Image → Prop
  | mint {state} (vacant : state.gate.live = none) (room : evidence.room state) :
      Step evidence state (mint state)
  | install {state} (id : Nat) (image : Image) (live : state.gate.live = some id)
      (certified : evidence.sealed id = some image) (notChosen : state.chosen id = none)
      (ready : evidence.ready state id image) :
      Step evidence state (install state id image)
  | retire {state} (id : Nat) (live : state.gate.live = some id) (terminal : CanRetire evidence state id) :
      Step evidence state (closeAdmission state)
  | plan {state} (key : CopyKey) (image : Image) (live : state.gate.live = some key.intent)
      (vacant : state.jobs key = none) (authorized : evidence.admittedCopy key image) :
      Step evidence state {state with jobs := update state.jobs key (some image)}
  | settle {state} (key : CopyKey) (image : Image) (planned : state.jobs key = some image)
      (settled : evidence.settledCopy key image) :
      Step evidence state {state with jobs := update state.jobs key none}
  | record {state} (id : Nat) (image : Image) (eligible : state.outcomes id = some image) :
      Step evidence state {state with recorded := update state.recorded id (some image)}
  | acknowledge {state} (id : Nat) (image : Image)
      (eligible : state.outcomes id = some image) (recorded : SourceHasRecord state id image) :
      Step evidence state {state with outcomes := update state.outcomes id none}
  | moveOn {state} (id : Nat) (image : Image) (current : state.serving id = some image)
      (authorized : evidence.adoptedElsewhere id image) :
      Step evidence state {state with serving := update state.serving id none}
  | restart {state} : Step evidence state state

inductive Trace (evidence : Evidence Image) : Store Image → Store Image → Prop
  | same (state : Store Image) : Trace evidence state state
  | next {first before after} : Trace evidence first before → Step evidence before after →
      Trace evidence first after

theorem closing_admission_keeps_result_records (state : Store Image) :
    (closeAdmission state).outcomes = state.outcomes := by
  exact Eq.refl state.outcomes

theorem closing_admission_keeps_physical_plans (state : Store Image) :
    (closeAdmission state).jobs = state.jobs := by
  exact Eq.refl state.jobs

theorem an_unresolved_seal_cannot_authorize_retirement
    {evidence : Evidence Image} {state : Store Image} {id : Nat} {image : Image}
    (sealed : evidence.sealed id = some image) (unresolved : state.chosen id = none) :
    ¬ CanRetire evidence state id := by
  intro allowed
  rcases allowed with aborted | ⟨_, installed⟩
  · have conflict := evidence.abortExcludesSeal id aborted
    rw [sealed] at conflict
    cases conflict
  · rw [unresolved] at installed
    cases installed

theorem steps_project_to_the_exact_admission_gate
    {evidence : Evidence Image} {before after : Store Image} (step : Step evidence before after) :
    before.gate = after.gate ∨ Reservation.Step before.gate after.gate := by
  cases step with
  | mint vacant _ => exact Or.inr (.prepare vacant)
  | retire _ live _ => exact Or.inr (.consume live)
  | _ => exact Or.inl rfl

theorem a_retired_handle_cannot_reopen_after_any_trace
    {evidence : Evidence Image} {first last : Store Image} {id : Nat}
    (closed : Reservation.Stale id first.gate) (trace : Trace evidence first last) :
    Reservation.Stale id last.gate := by
  induction trace with
  | same => exact closed
  | next _ step prior =>
      rcases steps_project_to_the_exact_admission_gate step with same | advance
      · exact same ▸ prior
      · exact Reservation.stale_preserved prior advance

structure Sound (state : Store Image) : Prop where
  outcomeExact : ∀ id image, state.outcomes id = some image → state.chosen id = some image
  recordedExact : ∀ id image, state.recorded id = some image → state.chosen id = some image
  preservesOutcome : ∀ id image, state.chosen id = some image →
    state.outcomes id = some image ∨ state.recorded id = some image

theorem empty_is_sound : Sound (empty : Store Image) := by
  constructor <;> simp [empty]

private theorem unchanged_results_keep_sound
    {before after : Store Image} (sound : Sound before)
    (chosen : after.chosen = before.chosen) (outcomes : after.outcomes = before.outcomes)
    (recorded : after.recorded = before.recorded) :
    Sound after := by
  constructor
  · rw [outcomes, chosen]
    exact sound.outcomeExact
  · rw [recorded, chosen]
    exact sound.recordedExact
  · rw [recorded, outcomes, chosen]
    exact sound.preservesOutcome

theorem every_step_keeps_unacknowledged_exact_results
    {evidence : Evidence Image} {before after : Store Image}
    (sound : Sound before) (step : Step evidence before after) : Sound after := by
  cases step with
  | install id image _ _ notChosen _ =>
      have noPrior : ∀ seed, before.recorded id ≠ some seed := by
        intro seed found
        have conflict := sound.recordedExact id seed found
        rw [notChosen] at conflict
        cases conflict
      constructor
      · intro key seed found
        by_cases matchesId : key = id
        · simpa [install, update, matchesId] using found
        · have old : before.outcomes key = some seed := by
            simpa [install, update, matchesId] using found
          simpa [install, update, matchesId] using sound.outcomeExact key seed old
      · intro key seed found
        by_cases matchesId : key = id
        · subst key
          exact False.elim (noPrior seed found)
        · simpa [install, update, matchesId] using sound.recordedExact key seed found
      · intro key seed chosen
        by_cases matchesId : key = id
        · exact Or.inl (by simpa [install, update, matchesId] using chosen)
        · have old : before.chosen key = some seed := by
            simpa [install, update, matchesId] using chosen
          simpa [install, update, matchesId] using sound.preservesOutcome key seed old
  | retire _ _ _ =>
      exact unchanged_results_keep_sound sound rfl (closing_admission_keeps_result_records before) rfl
  | record id image eligible =>
      refine ⟨sound.outcomeExact, ?_, ?_⟩
      · intro key seed found
        by_cases matchesId : key = id
        · have equal : image = seed := by simpa [update, matchesId] using found
          subst seed
          exact matchesId ▸ sound.outcomeExact id image eligible
        · have old : before.recorded key = some seed := by simpa [update, matchesId] using found
          exact sound.recordedExact key seed old
      · intro key seed chosen
        by_cases matchesId : key = id
        · subst key
          have equal := Option.some.inj ((sound.outcomeExact id image eligible).symm.trans chosen)
          subst seed
          exact Or.inl eligible
        · simpa [update, matchesId] using sound.preservesOutcome key seed chosen
  | acknowledge id image eligible durable =>
      have recorded : before.recorded id = some image := by
        exact durable
      refine ⟨?_, sound.recordedExact, ?_⟩
      · intro key seed found
        by_cases matchesId : key = id
        · simp [update, matchesId] at found
        · have old : before.outcomes key = some seed := by simpa [update, matchesId] using found
          exact sound.outcomeExact key seed old
      · intro key seed chosen
        by_cases matchesId : key = id
        · subst key
          have equal := Option.some.inj ((sound.outcomeExact id image eligible).symm.trans chosen)
          subst seed
          exact Or.inr recorded
        · simpa [update, matchesId] using sound.preservesOutcome key seed chosen
  | _ => exact unchanged_results_keep_sound sound rfl rfl rfl

theorem trace_keeps_unacknowledged_results
    {evidence : Evidence Image} {first last : Store Image} (sound : Sound first)
    (trace : Trace evidence first last) : Sound last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact every_step_keeps_unacknowledged_exact_results prior step

theorem a_restart_or_retirement_leaves_exact_reconciliation
    {evidence : Evidence Image} {first last : Store Image} (sound : Sound first)
    (trace : Trace evidence first last) (id : Nat) (image : Image)
    (chosen : last.chosen id = some image) (stillUnknown : last.recorded id ≠ some image) :
    last.outcomes id = some image := by
  have finalSound := trace_keeps_unacknowledged_results sound trace
  exact (finalSound.preservesOutcome id image chosen).resolve_right stillUnknown

theorem a_plan_stays_exact_until_its_own_settlement
    {evidence : Evidence Image} {before after : Store Image} {key : CopyKey} {image : Image}
    (existsPlan : before.jobs key = some image) (step : Step evidence before after) :
    after.jobs key = some image ∨ evidence.settledCopy key image := by
  cases step with
  | retire _ _ _ =>
      exact Or.inl (closing_admission_keeps_physical_plans before ▸ existsPlan)
  | plan planned _ _ vacant _ =>
      have different : key ≠ planned := by
        intro same
        subst planned
        rw [vacant] at existsPlan
        cases existsPlan
      exact Or.inl (by simpa [update, different] using existsPlan)
  | settle settledKey released prior settled =>
      by_cases matchesKey : key = settledKey
      · subst key
        have same := Option.some.inj (prior.symm.trans existsPlan)
        exact Or.inr (same ▸ settled)
      · exact Or.inl (by simpa [update, matchesKey] using existsPlan)
  | _ => exact Or.inl existsPlan

theorem old_cleanup_survives_retirement_and_fresh_admission
    {evidence : Evidence Image} {state : Store Image} {id : Nat} {key : CopyKey} {image : Image}
    (live : state.gate.live = some id) (terminal : CanRetire evidence state id)
    (charged : state.jobs key = some image) (room : evidence.room (closeAdmission state)) :
    ∃ after, Trace evidence state after ∧ after.gate.live = some (state.gate.issuedThrough + 1) ∧
      after.jobs key = some image := by
  let closed := closeAdmission state
  let reopened := mint closed
  refine ⟨reopened, .next (.next (.same _) (.retire id live terminal)) (.mint rfl room), rfl, ?_⟩
  show closed.jobs key = some image
  exact closing_admission_keeps_physical_plans state ▸ charged

#print axioms closing_admission_keeps_result_records
#print axioms closing_admission_keeps_physical_plans
#print axioms an_unresolved_seal_cannot_authorize_retirement
#print axioms steps_project_to_the_exact_admission_gate
#print axioms a_retired_handle_cannot_reopen_after_any_trace
#print axioms empty_is_sound
#print axioms every_step_keeps_unacknowledged_exact_results
#print axioms trace_keeps_unacknowledged_results
#print axioms a_restart_or_retirement_leaves_exact_reconciliation
#print axioms a_plan_stays_exact_until_its_own_settlement
#print axioms old_cleanup_survives_retirement_and_fresh_admission

end IntentRetirement
