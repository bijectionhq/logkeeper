import Std

set_option warningAsError true

namespace Retirement

structure State (Location : Type) where
  closed : Prop
  complete : Prop
  known : Location → Prop
  queued : Location → Prop
  resident : Location → Prop
  fenced : Location → Prop

def initial {Location : Type} (origin : Location) : State Location :=
  ⟨False, False, (· = origin), (fun _ => False), (· = origin), (fun _ => False)⟩

def Valid {Location : Type} (state : State Location) : Prop :=
  (∀ location, state.queued location ∨ state.resident location → state.known location) ∧
  (state.complete → state.closed ∧
    ∀ location, state.known location → state.fenced location ∧ ¬ state.resident location)

inductive Step {Location : Type} : State Location → State Location → Prop
  | reserve {state} (location : Location) (openStream : ¬ state.closed) :
      Step state {state with
        known := fun found => found = location ∨ state.known found
        queued := fun found => found = location ∨ state.queued found}
  | deliver {state} (location : Location) (issued : state.queued location)
      (unfenced : ¬ state.fenced location) :
      Step state {state with resident := fun found => found = location ∨ state.resident found}
  | retire {state} :
      Step state {state with closed := True}
  | fence {state} (location : Location) :
      Step state {state with fenced := fun found => found = location ∨ state.fenced found}
  | erase {state} (location : Location) :
      Step state {state with resident := fun found => state.resident found ∧ found ≠ location}
  | complete {state} (closed : state.closed)
      (evidence : ∀ location, state.known location →
                  state.fenced location ∧ ¬ state.resident location) :
      Step state {state with complete := True}

theorem step_preserves_valid {Location : Type} {before after : State Location}
    (valid : Valid before) (step : Step before after) : Valid after := by
  obtain ⟨known, evidence⟩ := valid
  cases step with
  | reserve location openStream =>
      constructor
      · intro found copy
        rcases copy with (same | queued) | resident
        · exact Or.inl same
        · exact Or.inr (known found (Or.inl queued))
        · exact Or.inr (known found (Or.inr resident))
      · intro complete
        exact False.elim (openStream (evidence complete).1)
  | deliver location issued unfenced =>
      constructor
      · intro found copy
        rcases copy with queued | (rfl | resident)
        · exact known found (Or.inl queued)
        · exact known found (Or.inl issued)
        · exact known found (Or.inr resident)
      · intro complete
        exact False.elim (unfenced ((evidence complete).2 location (known location (Or.inl issued))).1)
  | retire =>
      exact ⟨known, fun done => ⟨True.intro, (evidence done).2⟩⟩
  | fence location =>
      refine ⟨known, ?_⟩
      intro done
      obtain ⟨closed, proofFor⟩ := evidence done
      refine ⟨closed, fun found inventoried => ?_⟩
      obtain ⟨fenced, absent⟩ := proofFor found inventoried
      exact ⟨Or.inr fenced, absent⟩
  | erase location =>
      constructor
      · intro found copy
        rcases copy with queued | ⟨resident, _⟩
        · exact known found (Or.inl queued)
        · exact known found (Or.inr resident)
      · intro done
        obtain ⟨closed, proofFor⟩ := evidence done
        refine ⟨closed, fun found inventoried => ?_⟩
        obtain ⟨fenced, absent⟩ := proofFor found inventoried
        exact ⟨fenced, fun stillResident => absent stillResident.1⟩
  | complete closed proofFor =>
      exact ⟨known, fun _ => ⟨closed, proofFor⟩⟩

inductive Reachable {Location : Type} (origin : Location) : State Location → Prop
  | initial : Reachable origin (initial origin)
  | step {before after} : Reachable origin before → Step before after → Reachable origin after

theorem reachable_valid {Location : Type} {origin : Location} {state : State Location}
    (trace : Reachable origin state) : Valid state := by
  induction trace with
  | initial => simp [Valid, Retirement.initial]
  | step _ step prior => exact step_preserves_valid prior step

theorem completed_erasure_has_no_resident_copy {Location : Type}
    {origin : Location} {state : State Location} (trace : Reachable origin state)
    (complete : state.complete) (location : Location) : ¬ state.resident location := by
  intro resident
  obtain ⟨known, evidence⟩ := reachable_valid trace
  exact ((evidence complete).2 location (known location (Or.inr resident))).2 resident

theorem cannot_deliver_after_erasure {Location : Type}
    {origin : Location} {state : State Location} (trace : Reachable origin state)
    (complete : state.complete) (location : Location) (queued : state.queued location) :
    state.fenced location := by
  obtain ⟨known, evidence⟩ := reachable_valid trace
  exact ((evidence complete).2 location (known location (Or.inl queued))).1

#print axioms completed_erasure_has_no_resident_copy
#print axioms cannot_deliver_after_erasure

end Retirement
