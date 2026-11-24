import Lean

namespace HoldsVsGrace

def collectibleAfter (now retirement grace stampError checkError : Int) : Prop :=
  retirement + stampError + grace ≤ now + checkError

def strictGrace (grace delay epsilon : Int) : Prop :=
  delay + 2 * epsilon < grace

theorem grace_excludes_a_late_effect
    (now retirement grace delay epsilon stampError checkError : Int)
    (margin : strictGrace grace delay epsilon)
    (stampLower : -epsilon ≤ stampError) (checkUpper : checkError ≤ epsilon)
    (eligible : collectibleAfter now retirement grace stampError checkError) :
    retirement + delay < now := by
  unfold strictGrace at margin
  unfold collectibleAfter at eligible
  omega

theorem weak_grace_allows_collection_at_last_effect
    (retirement grace delay epsilon : Int)
    (nonnegative : 0 ≤ epsilon) (margin : grace ≤ delay + 2 * epsilon) :
    ∃ stampError checkError : Int,
      -epsilon ≤ stampError ∧ stampError ≤ epsilon ∧
      -epsilon ≤ checkError ∧ checkError ≤ epsilon ∧
      collectibleAfter (retirement + delay) retirement grace stampError checkError := by
  refine ⟨-epsilon, epsilon, by omega, by omega, by omega, by omega, ?_⟩
  unfold collectibleAfter
  omega

def collectibleVersion {Version : Type} (durableRoots pinnedRoots : Version → Prop)
    (victim : Version) : Prop :=
  ¬durableRoots victim ∧ ¬pinnedRoots victim

theorem collection_preserves_pinned_closure
    {Version : Type} (durableRoots pinnedRoots present : Version → Prop) (victim : Version)
    (backed : ∀ v, durableRoots v ∨ pinnedRoots v → present v)
    (allowed : collectibleVersion durableRoots pinnedRoots victim) :
    ∀ v, durableRoots v ∨ pinnedRoots v → present v ∧ v ≠ victim := by
  intro v reached
  refine ⟨backed v reached, ?_⟩
  intro same
  subst v
  exact reached.elim allowed.1 allowed.2

def completesBeforeTrim (observe work cadence : Nat) : Prop :=
  observe + work < cadence

theorem aligned_attempt_finishes_before_next_trim
    (observe work cadence : Nat)
    (window : completesBeforeTrim observe work cadence)
    (start finish : Nat) (admitted : start ≤ observe) (budget : finish ≤ start + work) :
    finish < cadence := by
  unfold completesBeforeTrim at window
  omega

theorem conservative_arm_expires_by_deadline
    (deadline arm epsilon stampError checkError : Int)
    (margin : arm + 2 * epsilon ≤ deadline)
    (stampUpper : stampError ≤ epsilon) (checkLower : -epsilon ≤ checkError) :
    collectibleAfter deadline 0 arm stampError checkError := by
  unfold collectibleAfter
  omega

theorem one_threshold_cannot_make_an_exact_window_with_nonzero_drift
    (deadline arm epsilon : Int) (nonzero : 0 < epsilon)
    (noEarly : ¬collectibleAfter (deadline - 1) 0 arm (-epsilon) epsilon)
    (noLate : collectibleAfter deadline 0 arm epsilon (-epsilon)) : False := by
  unfold collectibleAfter at noEarly noLate
  omega

#print axioms grace_excludes_a_late_effect
#print axioms weak_grace_allows_collection_at_last_effect
#print axioms collection_preserves_pinned_closure
#print axioms aligned_attempt_finishes_before_next_trim
#print axioms conservative_arm_expires_by_deadline
#print axioms one_threshold_cannot_make_an_exact_window_with_nonzero_drift

end HoldsVsGrace
