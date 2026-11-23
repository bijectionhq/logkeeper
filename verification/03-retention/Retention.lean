import Std

set_option warningAsError true

namespace Retention

def DebtBound (possibleHead : Nat → Prop) (covered cap : Nat) : Prop :=
  ∀ head, possibleHead head → head - covered ≤ cap

def UnboundedProgress (possibleHead : Nat → Prop) : Prop :=
  ∀ after, ∃ head, possibleHead head ∧ after < head

theorem checkpoint_stall_forces_backpressure (possibleHead : Nat → Prop) (covered cap : Nat)
    (boundedRecovery : DebtBound possibleHead covered cap) :
    ¬ UnboundedProgress possibleHead := by
  intro progress
  obtain ⟨head, reachable, beyond⟩ := progress (covered + cap)
  have bounded := boundedRecovery head reachable
  omega

theorem exact_cursor_caps_head (head floor cursor cap : Nat)
    (retainedBound : head - floor ≤ cap) (exactResume : floor ≤ cursor) :
    head ≤ cursor + cap := by
  omega

theorem indefinite_pin_forces_backpressure (possibleHead : Nat → Prop) (cursor cap : Nat)
    (canResume : ∀ head, possibleHead head → ∃ floor, head - floor ≤ cap ∧ floor ≤ cursor) :
    ¬ UnboundedProgress possibleHead := by
  intro progress
  obtain ⟨head, reachable, beyond⟩ := progress (cursor + cap)
  obtain ⟨floor, retainedBound, exactResume⟩ := canResume head reachable
  have bounded := exact_cursor_caps_head head floor cursor cap retainedBound exactResume
  omega

theorem full_budget_excludes_positive_control (used hard charge : Nat)
    (full : used = hard) (costsSpace : 0 < charge) :
    ¬ used + charge ≤ hard := by
  omega

theorem reserved_capacity_admits_control (used hard reserve charge : Nat)
    (ordinaryAdmission : used + reserve ≤ hard) (fitsReserve : charge ≤ reserve) :
    used + charge ≤ hard := by
  omega

#print axioms checkpoint_stall_forces_backpressure
#print axioms exact_cursor_caps_head
#print axioms indefinite_pin_forces_backpressure
#print axioms full_budget_excludes_positive_control
#print axioms reserved_capacity_admits_control

end Retention
