import Std

set_option warningAsError true

namespace Handoff

structure State (Record : Type) where
  sourceSealed : Bool := false
  activeTarget : Bool := false
  installed : Option (List Record) := none
  source : List Record := []
  target : List Record := []

def Prefix {Record : Type} (before after : List Record) : Prop :=
  ∃ suffix, after = before ++ suffix

def Valid {Record : Type} (state : State Record) : Prop :=
  (state.activeTarget = true → ∃ cut, state.installed = some cut) ∧
  (∀ cut, state.installed = some cut →
    state.sourceSealed = true ∧ cut = state.source ∧ Prefix cut state.target)

inductive Step {Record : Type} : State Record → State Record → Prop
  | appendSource {state} (record : Record) (writable : state.sourceSealed = false) :
      Step state {state with source := state.source ++ [record]}
  | freeze {state} :
      Step state {state with sourceSealed := true}
  | install {state} (sealed : state.sourceSealed = true) (uninstalled : state.installed = none) :
      Step state {state with installed := some state.source, target := state.source}
  | activate {state} (installed : ∃ cut, state.installed = some cut) :
      Step state {state with activeTarget := true}
  | appendTarget {state} (record : Record) (active : state.activeTarget = true) :
      Step state {state with target := state.target ++ [record]}

theorem step_preserves_valid {Record : Type} {before after : State Record}
    (prior : Valid before) (step : Step before after) : Valid after := by
  rcases prior with ⟨activeImpliesInstalled, installedExact⟩
  cases step with
  | appendSource record writable =>
      refine ⟨activeImpliesInstalled, ?_⟩
      intro cut installed
      have sealed := (installedExact cut installed).1
      simp [writable] at sealed
  | freeze =>
      refine ⟨activeImpliesInstalled, ?_⟩
      intro cut installed
      obtain ⟨_, exactCut, prefixProof⟩ := installedExact cut installed
      exact ⟨rfl, exactCut, prefixProof⟩
  | install sealed _ =>
      refine ⟨fun _ => ⟨before.source, rfl⟩, ?_⟩
      intro cut installed
      have sameCut : before.source = cut := Option.some.inj installed
      subst cut
      exact ⟨sealed, rfl, ⟨[], by simp⟩⟩
  | activate installed =>
      exact ⟨fun _ => installed, installedExact⟩
  | appendTarget record _ =>
      refine ⟨activeImpliesInstalled, ?_⟩
      intro cut installed
      obtain ⟨sealed, exactCut, suffix, target⟩ := installedExact cut installed
      exact ⟨sealed, exactCut, suffix ++ [record], by simp [target, List.append_assoc]⟩

inductive Reachable {Record : Type} : State Record → Prop
  | init : Reachable {}
  | step {before after} : Reachable before → Step before after → Reachable after

theorem reachable_valid {Record : Type} {state : State Record} (trace : Reachable state) :
    Valid state := by
  induction trace with
  | init => simp [Valid]
  | step _ step prior => exact step_preserves_valid prior step

theorem unique_authority {Record : Type} {state : State Record} (trace : Reachable state)
    (targetActive : state.activeTarget = true) : state.sourceSealed = true := by
  have valid := reachable_valid trace
  obtain ⟨cut, installed⟩ := valid.1 targetActive
  exact (valid.2 cut installed).1

theorem exact_source_prefix {Record : Type} {state : State Record} (trace : Reachable state)
    (targetActive : state.activeTarget = true) : Prefix state.source state.target := by
  have valid := reachable_valid trace
  obtain ⟨cut, installed⟩ := valid.1 targetActive
  obtain ⟨_, rfl, prefixProof⟩ := valid.2 cut installed
  exact prefixProof

theorem authorized_handoff_extends {Record : Type} (source : List Record)
    (trace : Reachable {source := source}) (entry : Record) :
    Reachable {sourceSealed := true, activeTarget := true, installed := some source,
               source := source, target := source ++ [entry]} := by
  have sealed : Reachable ({sourceSealed := true, source := source} : State Record) :=
    .step trace .freeze
  have installed : Reachable
      {sourceSealed := true, installed := some source, source := source, target := source} :=
    .step sealed (.install rfl rfl)
  have active : Reachable
      {sourceSealed := true, activeTarget := true, installed := some source,
       source := source, target := source} :=
    .step installed (.activate ⟨source, rfl⟩)
  exact .step active (.appendTarget entry rfl)

theorem cannot_fail_over_without_evidence {View : Type} (activate : View → Bool)
    (sourceWritable sourceSealed : View) (indistinguishable : sourceWritable = sourceSealed)
    (safety : activate sourceWritable = false) :
    activate sourceSealed = false := by
  rw [← indistinguishable, safety]

theorem distinguishable_evidence_allows_failover :
    ∃ activate : Bool → Bool, activate false = false ∧ activate true = true :=
  ⟨id, rfl, rfl⟩

#print axioms unique_authority
#print axioms exact_source_prefix
#print axioms authorized_handoff_extends
#print axioms cannot_fail_over_without_evidence
#print axioms distinguishable_evidence_allows_failover

end Handoff
