set_option warningAsError true

namespace Logkeeper.ObjectWithdrawal

inductive Role where
  | root | preparation | suffix | hold
  deriving DecidableEq

/-- A reference is indexed by object, role and the identity of the owning
root, preparation, record or hold. Several owners may reference one object. -/
structure State (Object Version : Type) where
  references : Object → Role → Nat → Prop
  fence : Object → Option Version
  hasOpaqueReferences : Prop
  image : Nat
  cohort : Nat

def referenced (s : State Object Version) (name : Object) : Prop :=
  ∃ role owner, s.references name role owner

def fenced (s : State Object Version) (name : Object) : Prop :=
  s.fence name ≠ none

def canAdmitReferences (s : State Object Version) : Option (List Object) → Prop
  | none => ∀ name, ¬ fenced s name
  | some names => ∀ name ∈ names, ¬ fenced s name

def canWithdraw (s : State Object Version) (name : Object) : Prop :=
  ¬ s.hasOpaqueReferences ∧ ¬ referenced s name

def Safe (s : State Object Version) : Prop :=
  ∀ name, fenced s name → canWithdraw s name

/-- Compaction and certified repair carry the selected logical state. Their
physical images may differ, but the reference and fence projections agree. -/
structure Carries (source target : State Object Version) : Prop where
  references : ∀ name role owner,
    target.references name role owner ↔ source.references name role owner
  fence : ∀ name, target.fence name = source.fence name
  hasOpaqueReferences : target.hasOpaqueReferences ↔ source.hasOpaqueReferences

inductive Step [DecidableEq Object] : State Object Version → State Object Version → Prop where
  | acquire (s : State Object Version) (names : List Object) (role : Role) (owner : Nat)
      (canAdmit : canAdmitReferences s (some names)) :
      Step s { s with references := fun n r o =>
        (n ∈ names ∧ r = role ∧ o = owner) ∨ s.references n r o }
  | acquireOpaque (s : State Object Version) (canAdmit : canAdmitReferences s none) :
      Step s { s with hasOpaqueReferences := True }
  | release (s : State Object Version) (keep : Object → Role → Nat → Prop)
      (stillOpaque : Prop) (weakens : stillOpaque → s.hasOpaqueReferences) :
      Step s { s with
        references := fun n r o => s.references n r o ∧ keep n r o
        hasOpaqueReferences := stillOpaque }
  | withdraw (s : State Object Version) (name : Object) (version : Version)
      (available : canWithdraw s name) (fresh : ¬ fenced s name) :
      Step s { s with fence := fun other => if other = name then some version else s.fence other }
  | compact {source target : State Object Version} (image : Carries source target) :
      Step source target
  | repair {source target : State Object Version} (installed : Carries source target) :
      Step source target

theorem carried_separation {source target : State Object Version}
    (safe : Safe source) (carry : Carries source target) : Safe target := by
  intro name isFenced
  have openSafe := safe name (by simpa [fenced, carry.fence name] using isFenced)
  exact ⟨fun unknown => openSafe.1 (carry.hasOpaqueReferences.mp unknown),
    fun ⟨role, owner, held⟩ => openSafe.2 ⟨role, owner, (carry.references name role owner).mp held⟩⟩

theorem order_preserves_separation [DecidableEq Object] {before after : State Object Version}
    (safe : Safe before) (step : Step before after) : Safe after := by
  cases step with
  | acquire names role owner allowed =>
    intro name isFenced
    have prior := safe name isFenced
    exact ⟨prior.1, fun ⟨r, o, held⟩ => held.elim
      (fun added => allowed name added.1 isFenced) (fun old => prior.2 ⟨r, o, old⟩)⟩
  | acquireOpaque allowed =>
    intro name isFenced
    exact False.elim (allowed name isFenced)
  | release _ _ weakens =>
    intro name isFenced
    have prior := safe name isFenced
    exact ⟨fun unknown => prior.1 (weakens unknown), fun ⟨r, o, held⟩ => prior.2 ⟨r, o, held.1⟩⟩
  | withdraw name version available _ =>
    intro other isFenced
    by_cases same : other = name
    · subst other
      exact available
    · exact safe other (by simpa [fenced, same] using isFenced)
  | compact image => exact carried_separation safe image
  | repair installed => exact carried_separation safe installed

theorem order_preserves_fence [DecidableEq Object] {before after : State Object Version}
    (step : Step before after) (atFence : before.fence name = some version) :
    after.fence name = some version := by
  cases step with
  | acquire | acquireOpaque | release => exact atFence
  | withdraw target _ _ fresh =>
    have distinct : name ≠ target := by
      intro same
      subst target
      exact fresh (by simp [fenced, atFence])
    simpa [distinct] using atFence
  | compact carry | repair carry => rw [carry.fence name, atFence]

inductive Trace [DecidableEq Object] : State Object Version → State Object Version → Prop where
  | empty (s : State Object Version) : Trace s s
  | next {start here after : State Object Version} (earlier : Trace start here)
      (step : Step here after) : Trace start after

theorem trace_preserves_separation [DecidableEq Object] {start finish : State Object Version}
    (safe : Safe start) (trace : Trace start finish) : Safe finish := by
  induction trace with
  | empty => exact safe
  | next _ step preceding => exact order_preserves_separation preceding step

theorem trace_preserves_fence [DecidableEq Object] {start finish : State Object Version}
    (trace : Trace start finish) (atFence : start.fence name = some version) :
    finish.fence name = some version := by
  induction trace with
  | empty => exact atFence
  | next _ step preceding => exact order_preserves_fence step preceding

theorem referenced_refuses_withdrawal {s : State Object Version} (held : referenced s name) :
    ¬ canWithdraw s name := fun available => available.2 held

theorem fenced_refuses_reference {s : State Object Version} (closed : fenced s name)
    (member : name ∈ names) : ¬ canAdmitReferences s (some names) :=
  fun allowed => allowed name member closed

private def empty : State Nat Nat := ⟨fun _ _ _ => False, fun _ => none, False, 0, 0⟩
private def withdrawn : State Nat Nat :=
  { empty with fence := fun name => if name = 0 then some 7 else none }
private def held : State Nat Nat :=
  { withdrawn with references := fun n r o => (n ∈ [1] ∧ r = .hold ∧ o = 4) ∨ False }

theorem reachable_fence : Step empty withdrawn :=
  Step.withdraw empty 0 7 ⟨id, fun ⟨_, _, h⟩ => h⟩ (by simp [fenced, empty])

theorem reachable_hold : Step withdrawn held :=
  Step.acquire withdrawn [1] .hold 4 (by simp [canAdmitReferences, fenced, withdrawn])

private def compacted : State Nat Nat := { held with image := 1 }
private def repaired : State Nat Nat := { compacted with cohort := 1 }

private theorem held_reference : referenced held 1 :=
  ⟨.hold, 4, Or.inl ⟨by simp, rfl, rfl⟩⟩

theorem reachable_compacted_and_repaired :
    Trace empty repaired ∧ repaired.image = 1 ∧ repaired.cohort = 1 ∧
      repaired.fence 0 = some 7 ∧ referenced repaired 1 :=
  ⟨.next (.next (.next (.next (.empty _) reachable_fence) reachable_hold)
      (.compact ⟨fun _ _ _ => Iff.rfl, fun _ => rfl, Iff.rfl⟩))
      (.repair ⟨fun _ _ _ => Iff.rfl, fun _ => rfl, Iff.rfl⟩),
    rfl, rfl, rfl, held_reference⟩

theorem unchecked_acquire_violates_separation :
    ¬ Safe { withdrawn with references := fun n r _ => n = 0 ∧ r = .suffix } := by
  intro safe
  exact (safe 0 (by simp [fenced, withdrawn])).2 ⟨.suffix, 0, rfl, rfl⟩

theorem unchecked_withdrawal_violates_separation :
    ¬ Safe { held with fence := fun n => if n = 1 then some 8 else held.fence n } := by
  intro safe
  exact (safe 1 (by simp [fenced])).2 held_reference

/-- A compactor that omits fences makes a delayed reference eligible again. -/
theorem compaction_without_fences_reopens_name :
    canAdmitReferences { held with fence := fun _ => (none : Option Nat) } (some [0]) ∧
    ¬ Carries held { held with fence := fun _ => none } := by
  refine ⟨by simp [canAdmitReferences, fenced], fun carry => ?_⟩
  have atZero := carry.fence 0
  simp [held, withdrawn] at atZero

/-- A repair that drops reference rows can then authorize their withdrawal. -/
theorem repair_without_references_authorizes_withdrawal :
    canWithdraw { held with references := fun _ _ _ => False } 1 ∧
    ¬ Carries held { held with references := fun _ _ _ => False } := by
  refine ⟨⟨id, fun ⟨_, _, h⟩ => h⟩, fun carry => ?_⟩
  obtain ⟨role, owner, h⟩ := held_reference
  exact (carry.references 1 role owner).mpr h

#print axioms trace_preserves_separation
#print axioms trace_preserves_fence
#print axioms referenced_refuses_withdrawal
#print axioms fenced_refuses_reference
#print axioms reachable_compacted_and_repaired
#print axioms unchecked_acquire_violates_separation
#print axioms unchecked_withdrawal_violates_separation
#print axioms compaction_without_fences_reopens_name
#print axioms repair_without_references_authorizes_withdrawal

end Logkeeper.ObjectWithdrawal
