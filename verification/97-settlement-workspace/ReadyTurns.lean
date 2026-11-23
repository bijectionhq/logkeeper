import Std

set_option warningAsError true

namespace ReadyTurns

def distance {slots : Nat} (cursor target : Fin slots) : Nat :=
  if cursor.val < target.val then target.val - cursor.val else slots - cursor.val + target.val

theorem a_full_turn_is_positive {slots : Nat} (cursor target : Fin slots) :
    0 < distance cursor target := by
  unfold distance
  have bounded := cursor.isLt
  split <;> omega

theorem the_scheduler_considers_at_most_one_full_turn {slots : Nat} (cursor target : Fin slots) :
    distance cursor target ≤ slots := by
  unfold distance
  have beforeLimit := cursor.isLt
  have targetInRange := target.isLt
  split <;> omega

def Selects {slots : Nat} (ready : Fin slots → Prop) (cursor selected : Fin slots) : Prop :=
  ready selected ∧ ∀ other, ready other → distance cursor selected ≤ distance cursor other

theorem a_selected_slot_is_no_farther_than_any_ready_slot {slots : Nat}
    (ready : Fin slots → Prop) (cursor selected target : Fin slots)
    (selectedNext : Selects ready cursor selected) (stillReady : ready target) :
    distance cursor selected ≤ distance cursor target := by
  exact selectedNext.2 target stillReady

private theorem exists_least_natural (property : Nat → Prop) (bound : Nat)
    (witness : ∃ candidate, candidate ≤ bound ∧ property candidate) :
    ∃ least, property least ∧ ∀ other, property other → least ≤ other := by
  induction bound with
  | zero =>
      obtain ⟨candidate, atZero, valid⟩ := witness
      exact ⟨candidate, valid, fun other _ => by omega⟩
  | succ bound prior =>
      by_cases lower : ∃ candidate, candidate ≤ bound ∧ property candidate
      · exact prior lower
      · obtain ⟨candidate, within, valid⟩ := witness
        refine ⟨candidate, valid, ?_⟩
        intro other available
        by_cases tooLow : other ≤ bound
        · exact False.elim (lower ⟨other, tooLow, available⟩)
        · omega

theorem every_nonempty_ready_set_has_a_next_slot {slots : Nat} (ready : Fin slots → Prop)
    (cursor target : Fin slots) (available : ready target) :
    ∃ selected, Selects ready cursor selected := by
  let rankIsReady := fun rank => ∃ slot, ready slot ∧ distance cursor slot = rank
  obtain ⟨least, ⟨selected, eligible, atLeast⟩, minimal⟩ :=
    exists_least_natural rankIsReady (distance cursor target) ⟨_, Nat.le_refl _, target, available, rfl⟩
  exact ⟨selected, eligible, fun other canUse =>
    atLeast.symm ▸ minimal (distance cursor other) ⟨other, canUse, rfl⟩⟩

theorem when_a_ready_target_is_bypassed_the_distance_falls {slots : Nat}
    (ready : Fin slots → Prop) (cursor selected target : Fin slots)
    (selectedNext : Selects ready cursor selected) (stillReady : ready target) (other : selected ≠ target) :
    distance selected target < distance cursor target := by
  have ordered := a_selected_slot_is_no_farther_than_any_ready_slot ready cursor selected target
    selectedNext stillReady
  have priorBound := cursor.isLt
  have selectedBound := selected.isLt
  have targetBound := target.isLt
  have distinct : selected.val ≠ target.val := fun same => other (Fin.ext same)
  unfold distance at *
  split at ordered <;> split at ordered <;> split <;> omega

inductive Skipped {slots : Nat} (target : Fin slots) : Fin slots → Fin slots → Nat → Prop
  | zero (cursor : Fin slots) : Skipped target cursor cursor 0
  | next {first cursor next : Fin slots} {count : Nat} (ready : Fin slots → Prop)
      (history : Skipped target first cursor count) (qualified : ready target) (distinct : next ≠ target)
      (choice : Selects ready cursor next) : Skipped target first next (count + 1)

theorem a_persistently_ready_slot_can_be_bypassed_at_most_one_turn
    {slots : Nat} {target start cursor : Fin slots} {count : Nat}
    (run : Skipped target start cursor count) :
    count + distance cursor target ≤ distance start target := by
  induction run with
  | zero => simp
  | next ready _ qualified distinct choice prior =>
      have closer := when_a_ready_target_is_bypassed_the_distance_falls ready _ _ target choice qualified distinct
      omega

theorem a_persistently_ready_slot_cannot_be_bypassed_slots_times
    {slots : Nat} {target start cursor : Fin slots} {count : Nat}
    (run : Skipped target start cursor count) :
    count < slots := by
  have rank := a_persistently_ready_slot_can_be_bypassed_at_most_one_turn run
  have cap := the_scheduler_considers_at_most_one_full_turn start target
  have positive := a_full_turn_is_positive cursor target
  omega

#print axioms a_full_turn_is_positive
#print axioms the_scheduler_considers_at_most_one_full_turn
#print axioms a_selected_slot_is_no_farther_than_any_ready_slot
#print axioms every_nonempty_ready_set_has_a_next_slot
#print axioms when_a_ready_target_is_bypassed_the_distance_falls
#print axioms a_persistently_ready_slot_can_be_bypassed_at_most_one_turn
#print axioms a_persistently_ready_slot_cannot_be_bypassed_slots_times

end ReadyTurns
