set_option warningAsError true

namespace MaintenanceBound

inductive Phase where
  | idle | boundary | uploaded
  deriving DecidableEq

structure Lane where
  used : Nat
  phase : Phase
  grant : Nat
  deriving DecidableEq

/-- Grant-fenced maintenance: a crash installs a new grant without a record. -/
inductive Step : Lane → Lane → Prop where
  | regrant (lane : Lane) : Step lane { lane with grant := lane.grant + 1 }
  | boundary (lane : Lane) : lane.phase = .idle → Step lane { lane with used := lane.used + 1, phase := .boundary }
  | upload (lane : Lane) : lane.phase = .boundary → Step lane { lane with used := lane.used + 1, phase := .uploaded }
  | publishAndTrim (lane : Lane) : lane.phase = .uploaded → Step lane { lane with used := 1, phase := .idle }

inductive Reaches : Lane → Prop where
  | start : Reaches ⟨1, .idle, 1⟩
  | step {lane next : Lane} : Reaches lane → Step lane next → Reaches next

def Shape (lane : Lane) : Prop :=
  (lane.phase = .idle ∧ lane.used = 1) ∨ (lane.phase = .boundary ∧ lane.used = 2) ∨
    (lane.phase = .uploaded ∧ lane.used = 3)

theorem every_reachable_lane_has_its_phase_shape {lane : Lane} (reached : Reaches lane) : Shape lane := by
  induction reached with
  | start => exact .inl ⟨rfl, rfl⟩
  | step _ step shape =>
    cases step with
    | regrant => exact shape
    | boundary idle =>
      rcases shape with ⟨_, used⟩ | ⟨phase, _⟩ | ⟨phase, _⟩
      · exact .inr (.inl ⟨rfl, by simp [used]⟩)
      · simp_all
      · simp_all
    | upload pending =>
      rcases shape with ⟨phase, _⟩ | ⟨_, used⟩ | ⟨phase, _⟩
      · simp_all
      · exact .inr (.inr ⟨rfl, by simp [used]⟩)
      · simp_all
    | publishAndTrim => exact .inl ⟨rfl, rfl⟩

/-- Any number of writer replacements keeps maintenance within three records. -/
theorem grant_fencing_bounds_maintenance_by_three {lane : Lane} (reached : Reaches lane) : lane.used ≤ 3 := by
  rcases every_reachable_lane_has_its_phase_shape reached with ⟨_, used⟩ | ⟨_, used⟩ | ⟨_, used⟩ <;> omega

/-- A three-record reserve always admits the next progress record. -/
theorem a_three_record_reserve_always_admits_progress {lane : Lane} (reached : Reaches lane) :
    lane.phase = .uploaded ∨ lane.used + 1 ≤ 3 := by
  rcases every_reachable_lane_has_its_phase_shape reached with ⟨_, used⟩ | ⟨_, used⟩ | ⟨phase, _⟩
  · exact .inr (by omega)
  · exact .inr (by omega)
  · exact .inl phase

/-- The per-term claim design grows with the number of terms before a checkpoint. -/
def claimsAfter (crashes : Nat) : Nat := 1 + crashes

theorem per_term_claims_exceed_any_fixed_reserve (reserve : Nat) :
    ∃ crashes, reserve < claimsAfter crashes :=
  ⟨reserve, by simp [claimsAfter]⟩

#print axioms every_reachable_lane_has_its_phase_shape
#print axioms grant_fencing_bounds_maintenance_by_three
#print axioms a_three_record_reserve_always_admits_progress
#print axioms per_term_claims_exceed_any_fixed_reserve

end MaintenanceBound
