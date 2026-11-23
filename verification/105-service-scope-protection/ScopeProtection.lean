set_option warningAsError true

namespace ScopeProtection

variable {Input Zone : Type}

-- A copy is exact and retained. If its AZ survives, it remains recoverable.
def Coverage (copies : Input → Zone → Prop) (input : Input) (lost : Zone) : Prop :=
  ∃ zone, zone ≠ lost ∧ copies input zone

def Protects (credibleLoss : Zone → Prop) (owed : Input → Prop)
    (copies : Input → Zone → Prop) : Prop :=
  ∀ input, owed input → ∀ zone, credibleLoss zone → Coverage copies input zone

def Acknowledge (owed : Input → Prop) (next : Input) : Input → Prop :=
  fun input => owed input ∨ input = next

def CanAcknowledge (ready : Prop) (credibleLoss : Zone → Prop)
    (copies : Input → Zone → Prop) (next : Input) : Prop :=
  ready ∧ (∀ zone, credibleLoss zone → Coverage copies next zone)

def CanWithdraw (credibleLoss : Zone → Prop) (owed : Input → Prop)
    (postCopies : Input → Zone → Prop) : Prop :=
  Protects credibleLoss owed postCopies

theorem protection_has_a_surviving_copy
    {credibleLoss : Zone → Prop} {owed : Input → Prop} {copies : Input → Zone → Prop}
    {input : Input} {lost : Zone} (preserved : Protects credibleLoss owed copies)
    (required : owed input) (credible : credibleLoss lost) :
    ∃ survivor, survivor ≠ lost ∧ copies input survivor :=
  preserved input required lost credible

theorem service_readiness_does_not_shrink_acknowledged_protection
    {ready : Prop} {credibleLoss : Zone → Prop} {owed : Input → Prop}
    {copies : Input → Zone → Prop} {next : Input}
    (before : Protects credibleLoss owed copies)
    (allow : CanAcknowledge ready credibleLoss copies next) :
    Protects credibleLoss (Acknowledge owed next) copies := by
  intro input required lost credible
  rcases required with old | new
  · exact before input old lost credible
  · cases new
    exact allow.2 lost credible

theorem guarded_withdrawal_preserves_the_original_promise
    {credibleLoss : Zone → Prop} {owed : Input → Prop}
    {postCopies : Input → Zone → Prop} {input : Input} {lost : Zone}
    (allow : CanWithdraw credibleLoss owed postCopies) (required : owed input)
    (credible : credibleLoss lost) :
    Coverage postCopies input lost :=
  allow input required lost credible

theorem two_distinct_copies_cover_any_single_loss
    {copies : Input → Zone → Prop} {input : Input} {first second : Zone}
    (distinct : first ≠ second) (holdsFirst : copies input first)
    (holdsSecond : copies input second) :
    ∀ lost, Coverage copies input lost := by
  classical
  intro lost
  by_cases firstLost : first = lost
  · exact ⟨second, fun secondLost => distinct (firstLost.trans secondLost.symm), holdsSecond⟩
  · exact ⟨first, firstLost, holdsFirst⟩

theorem one_copy_cannot_cover_the_loss_of_its_az
    {copies : Input → Zone → Prop} {input : Input} {only : Zone}
    (single : ∀ zone, copies input zone → zone = only) :
    ¬ Coverage copies input only := by
  intro ⟨zone, survives, holds⟩
  exact survives (single zone holds)

theorem confirmed_loss_can_use_one_copy_in_another_az
    {ready : Prop} {copies : Input → Zone → Prop} {input : Input}
    {lost survivor : Zone} (verified : ready) (different : survivor ≠ lost)
    (holds : copies input survivor) :
    ready ∧ (∀ candidate, candidate = lost → Coverage copies input candidate) := by
  refine ⟨verified, ?_⟩
  intro candidate evidence
  subst candidate
  exact ⟨survivor, different, holds⟩

theorem identical_observations_cannot_offer_single_copy_progress_and_protection
    {Observation World : Type} {copies : Input → Zone → Prop} {input : Input} {only : Zone}
    (decideAck : Observation → Bool) (observe : World → Observation)
    (failed slow : World) (same : observe failed = observe slow)
    (single : ∀ zone, copies input zone → zone = only) :
    ¬ (decideAck (observe failed) = true ∧
       (decideAck (observe slow) = true → Coverage copies input only)) := by
  intro ⟨progress, sound⟩
  exact one_copy_cannot_cover_the_loss_of_its_az single (sound (same ▸ progress))

def CanRenew (eligible : Zone → Prop) (owed : Input → Prop)
    (copies : Input → Zone → Prop) : Prop :=
  (∀ lost, eligible lost) ∧ Protects (fun _ => True) owed copies

theorem renewal_restores_both_readiness_and_protection
    {eligible : Zone → Prop} {owed : Input → Prop} {copies : Input → Zone → Prop}
    (renewed : CanRenew eligible owed copies) (lost : Zone) :
    eligible lost ∧ ∀ input, owed input → Coverage copies input lost :=
  ⟨renewed.1 lost, fun input required => renewed.2 input required lost trivial⟩

structure Assurance (Input Zone Scope : Type) where
  serving : Option Scope
  credibleLoss : Zone → Prop
  owed : Input → Prop
  copies : Input → Zone → Prop

def Assured {Scope : Type} (state : Assurance Input Zone Scope) : Prop :=
  Protects state.credibleLoss state.owed state.copies

inductive Step {Scope : Type} (currentReady : Scope → Prop) (diagnosed : Zone → Prop)
    (repairReady : Zone → Prop) : Assurance Input Zone Scope → Assurance Input Zone Scope → Prop where
  | choose (before : Assurance Input Zone Scope) (scope : Scope)
      (ready : currentReady scope) :
      Step currentReady diagnosed repairReady before { before with serving := some scope }
  | acknowledge (before : Assurance Input Zone Scope) (scope : Scope) (next : Input)
      (allow : CanAcknowledge (before.serving = some scope ∧ currentReady scope)
        before.credibleLoss before.copies next) :
      Step currentReady diagnosed repairReady before { before with owed := Acknowledge before.owed next }
  | changeCopies (before : Assurance Input Zone Scope) (postCopies : Input → Zone → Prop)
      (allow : CanWithdraw before.credibleLoss before.owed postCopies) :
      Step currentReady diagnosed repairReady before { before with copies := postCopies }
  | confirm (before : Assurance Input Zone Scope) (lost : Zone)
      (prior : before.credibleLoss lost) (witness : diagnosed lost) :
      Step currentReady diagnosed repairReady before { before with credibleLoss := (· = lost) }
  | renew (before : Assurance Input Zone Scope) (eligible : CanRenew repairReady before.owed before.copies) :
      Step currentReady diagnosed repairReady before { before with credibleLoss := fun _ => True }

theorem step_preserves_assurance {Scope : Type} {currentReady : Scope → Prop}
    {diagnosed repairReady : Zone → Prop} {before after : Assurance Input Zone Scope}
    (initial : Assured before) (step : Step currentReady diagnosed repairReady before after) :
    Assured after := by
  cases step with
  | choose => exact initial
  | acknowledge _ _ allow =>
    exact service_readiness_does_not_shrink_acknowledged_protection initial allow
  | changeCopies _ allow => exact allow
  | confirm _ prior _ =>
    intro input required lost equality
    subst lost
    exact initial input required _ prior
  | renew eligible => exact eligible.2

inductive Trace {State : Type} (step : State → State → Prop) : State → State → Prop where
  | nil (state : State) : Trace step state state
  | cons {first next last : State} :
      step first next → Trace step next last → Trace step first last

theorem every_authorized_trace_preserves_assurance {Scope : Type} {currentReady : Scope → Prop}
    {diagnosed repairReady : Zone → Prop} {first last : Assurance Input Zone Scope}
    (history : Trace (Step currentReady diagnosed repairReady) first last)
    (initial : Assured first) : Assured last := by
  induction history with
  | nil => exact initial
  | cons step _ ih => exact ih (step_preserves_assurance initial step)

#print axioms protection_has_a_surviving_copy
#print axioms service_readiness_does_not_shrink_acknowledged_protection
#print axioms guarded_withdrawal_preserves_the_original_promise
#print axioms two_distinct_copies_cover_any_single_loss
#print axioms one_copy_cannot_cover_the_loss_of_its_az
#print axioms confirmed_loss_can_use_one_copy_in_another_az
#print axioms identical_observations_cannot_offer_single_copy_progress_and_protection
#print axioms renewal_restores_both_readiness_and_protection

#print axioms step_preserves_assurance
#print axioms every_authorized_trace_preserves_assurance

end ScopeProtection
