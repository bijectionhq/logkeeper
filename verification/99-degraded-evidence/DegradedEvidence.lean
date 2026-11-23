import Std

set_option warningAsError true

namespace DegradedEvidence

variable {World Evidence : Type}

structure Guarantees (observes : World → Evidence) (failed : World → Prop)
    (enter : Evidence → Bool) : Prop where
  soundDiagnosis : ∀ world, enter (observes world) = true → failed world
  servesFailure : ∀ world, failed world → enter (observes world) = true

theorem identical_observations_do_not_decide_actual_failure
    (observes : World → Evidence) (failed : World → Prop) (enter : Evidence → Bool)
    (slow unavailable : World) (same : observes slow = observes unavailable)
    (alive : ¬ failed slow) (down : failed unavailable) :
    ¬ Guarantees observes failed enter := by
  intro both
  exact alive (both.soundDiagnosis slow (same.symm ▸ both.servesFailure unavailable down))

theorem a_decision_about_exclusion_depends_on_its_own_evidence
    (observes : World → Evidence) (approved ready : Evidence → Bool)
    (world : World) (admitted : (approved (observes world) && ready (observes world)) = true) :
    approved (observes world) = true ∧ ready (observes world) = true := by
  exact Bool.and_eq_true_iff.mp admitted

#print axioms identical_observations_do_not_decide_actual_failure
#print axioms a_decision_about_exclusion_depends_on_its_own_evidence

end DegradedEvidence
