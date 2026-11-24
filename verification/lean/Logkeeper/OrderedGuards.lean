import Logkeeper.JournalRefinement

set_option warningAsError true

namespace Logkeeper.OrderedCohort

def accept_quorum (accepted members : Nat) : Prop := members < 2 * accepted

theorem accept_quorum_is_majority (members : List Nat) (accepted : Nat → Bool) :
    accept_quorum (members.countP accepted) members.length ↔
      JournalRefinement.Majority members accepted := Iff.rfl

def has_paid_repair_quorum (paid quorum : Nat) : Prop := quorum ≤ paid

theorem seal_requires_paid_successor_quorum (paid members : Nat) :
    has_paid_repair_quorum paid (members / 2 + 1) ↔ accept_quorum paid members := by
  unfold has_paid_repair_quorum accept_quorum
  omega

def may_extend {Group : Type} (successor : Option Group) : Prop := successor = none

def matches_chosen_seal {Group : Type} (successor : Option Group) (destination : Group) :
    Prop := successor = some destination

theorem sealed_cohort_refuses_new_decisions {Group : Type} (destination : Group) :
    ¬ may_extend (some destination) := by simp [may_extend]

theorem repair_requires_the_chosen_destination {Group : Type} {chosen offered : Group}
    (same : matches_chosen_seal (some chosen) offered) : chosen = offered :=
  Option.some.inj same

namespace Controls

-- A single matching response or paid ticket meets the weakened threshold.
example : (1 : Nat) ≤ 1 ∧ ¬ accept_quorum 1 3 ∧ ¬ has_paid_repair_quorum 1 2 := by
  simp [accept_quorum, has_paid_repair_quorum]

example : ¬ may_extend (some 4) := by simp [may_extend]

-- Treat any seal as sufficient, or accept an ordinary unsealed sample.
example : (some 4 : Option Nat).isSome = true ∧ ¬ matches_chosen_seal (some 4) 5 := by
  simp [matches_chosen_seal]
example : (none : Option Nat).isNone = true ∧ ¬ matches_chosen_seal none 5 := by
  simp [matches_chosen_seal]

example : accept_quorum 2 3 ∧ has_paid_repair_quorum 2 2 ∧
    matches_chosen_seal (some 4) 4 := by
  simp [accept_quorum, has_paid_repair_quorum, matches_chosen_seal]

end Controls

#print axioms accept_quorum_is_majority
#print axioms seal_requires_paid_successor_quorum
#print axioms sealed_cohort_refuses_new_decisions
#print axioms repair_requires_the_chosen_destination

end Logkeeper.OrderedCohort

namespace Logkeeper.OrderedCheckpoint

def matches_preparation {Custody : Type} (prepared published : Custody) : Prop :=
  prepared = published

def next_revision (current offered : Nat) : Prop := offered = current + 1

def may_close (sourceOfPreparation held : Bool) : Prop :=
  sourceOfPreparation = false ∧ held = false

def may_acquire (aboveErasureFloor retained closed : Bool) : Prop :=
  aboveErasureFloor = true ∧ retained = true ∧ closed = false

theorem publication_keeps_prepared_custody {Custody : Type} {prepared published : Custody}
    (same : matches_preparation prepared published) : prepared = published := same

theorem preparation_revision_advances {current offered : Nat}
    (valid : next_revision current offered) : current < offered := by
  unfold next_revision at valid
  omega

theorem a_held_checkpoint_cannot_close (sourceOfPreparation : Bool) :
    ¬ may_close sourceOfPreparation true := fun h => Bool.noConfusion h.2

theorem a_closed_checkpoint_refuses_new_acquisition (aboveErasureFloor retained : Bool) :
    ¬ may_acquire aboveErasureFloor retained true := fun h => Bool.noConfusion h.2.2

namespace Controls

-- A weaker match compares allocation and revision and omits the provider.
def same_allocation_and_revision (left right : Nat × Nat × Nat) : Prop :=
  left.1 = right.1 ∧ left.2.1 = right.2.1

example : same_allocation_and_revision (3, 2, 10) (3, 2, 11) ∧
    ¬ matches_preparation (3, 2, 10) (3, 2, 11) := by
  simp [same_allocation_and_revision, matches_preparation]

example : ((2 : Nat) = 2 ∨ next_revision 2 2) ∧ ¬ next_revision 2 2 := by
  simp [next_revision]

-- Closure without the hold check permits this root, and admission without
-- the closure check permits this delayed acquisition.
example : (false = false) ∧ ¬ may_close false true := by simp [may_close]
example : (true = true ∧ true = true) ∧ ¬ may_acquire true true true := by
  simp [may_acquire]

example : matches_preparation (3, 2, 10) (3, 2, 10) ∧ next_revision 1 2 ∧
    may_close false false ∧ may_acquire true true false := by
  simp [matches_preparation, next_revision, may_close, may_acquire]

end Controls

#print axioms publication_keeps_prepared_custody
#print axioms preparation_revision_advances
#print axioms a_held_checkpoint_cannot_close
#print axioms a_closed_checkpoint_refuses_new_acquisition

end Logkeeper.OrderedCheckpoint
