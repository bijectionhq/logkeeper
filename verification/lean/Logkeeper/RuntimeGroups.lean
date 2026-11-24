namespace Logkeeper.RuntimeGroups

inductive InstallDecision where
  | persist
  | alreadyInstalled
  | refuse
  deriving DecidableEq

def installGroup (existing : Option Bool) (expectedAbsent : Bool) : InstallDecision :=
  match existing with
  | some true => .alreadyInstalled
  | some false => .refuse
  | none => if expectedAbsent then .persist else .refuse

def mayServe (persisted retired : Bool) : Bool :=
  persisted && !retired

def retireGroup (selected head final : Nat) (vacant drained noPreparation : Bool)
    (observed chosen : Nat) : Prop :=
  selected = final ∧ head = final ∧ vacant = true ∧ drained = true ∧ noPreparation = true ∧
    chosen = observed + 1

theorem conflictingDefinitionIsRefused (expectedAbsent : Bool) :
    installGroup (some false) expectedAbsent = .refuse := by rfl

theorem identicalDefinitionIsIdempotent (expectedAbsent : Bool) :
    installGroup (some true) expectedAbsent = .alreadyInstalled := by
  rfl

theorem unpersistedGroupIsNeverServed (retired : Bool) :
    mayServe false retired = false := by rfl

theorem retirementRequiresTheExactFinalCheckpoint
    (selected head final observed chosen : Nat) (vacant drained noPreparation : Bool)
    (accepted : retireGroup selected head final vacant drained noPreparation observed chosen) :
    selected = final ∧ head = final := by
  exact ⟨accepted.1, accepted.2.1⟩

theorem interveningDecisionPreventsRetirement
    (observed chosen : Nat) (intervening : observed + 1 < chosen) :
    ¬ retireGroup 0 0 0 true true true observed chosen := by
  intro accepted
  have exactNext := accepted.2.2.2.2.2
  omega

theorem emptyGroupCanRetire :
    retireGroup 0 0 0 true true true 0 1 := by
  simp [retireGroup]

#print axioms conflictingDefinitionIsRefused
#print axioms identicalDefinitionIsIdempotent
#print axioms unpersistedGroupIsNeverServed
#print axioms retirementRequiresTheExactFinalCheckpoint
#print axioms interveningDecisionPreventsRetirement
#print axioms emptyGroupCanRetire

end Logkeeper.RuntimeGroups
