import Std

set_option warningAsError true

namespace SelectiveReadWindow

structure Window (width : Nat) where
  floor : Nat
  bits : Fin width → Bool

def initial (width : Nat) : Window width :=
  ⟨0, fun _ => false⟩

def Spent (state : Window width) (nonce : Nat) : Prop :=
  nonce ≤ state.floor ∨
    ∃ slot : Fin width, nonce = state.floor + slot.val + 1 ∧ state.bits slot = true

def nonceAt (state : Window width) (slot : Fin width) : Nat :=
  state.floor + slot.val + 1

def mark (state : Window width) (slot : Fin width) : Window width :=
  {state with bits := fun bit => if bit = slot then true else state.bits bit}

theorem marking_spends_exactly_its_original_nonce (state : Window width) (slot : Fin width) (nonce : Nat) :
    Spent (mark state slot) nonce ↔ Spent state nonce ∨ nonce = nonceAt state slot := by
  constructor
  · intro spent
    rcases spent with below | ⟨bit, bound, marked⟩
    · exact .inl (.inl below)
    · by_cases same : bit = slot
      · subst bit
        exact .inr bound
      · exact .inl (.inr ⟨bit, bound, by simpa [mark, same] using marked⟩)
  · intro either
    rcases either with prior | own
    · rcases prior with below | ⟨bit, bound, marked⟩
      · exact .inl below
      · exact .inr ⟨bit, bound, by simp [mark, marked]⟩
    · exact .inr ⟨slot, own, by simp [mark]⟩

noncomputable def consume (limit : Nat) (state : Window width) (nonce : Nat) : Option (Window width) := by
  classical
  exact if ready : state.floor < nonce ∧ nonce ≤ state.floor + width ∧ nonce ≤ limit ∧ ¬ Spent state nonce then
    some (mark state ⟨nonce - (state.floor + 1), by omega⟩)
  else none

theorem a_successful_consume_is_in_range_unspent_and_exact
    (limit : Nat) (state after : Window width) (nonce : Nat)
    (accepted : consume limit state nonce = some after) :
    ¬ Spent state nonce ∧ nonce ≤ limit ∧ ∀ other, Spent after other ↔ Spent state other ∨ other = nonce := by
  unfold consume at accepted
  split at accepted
  · next ready =>
    cases accepted
    refine ⟨ready.2.2.2, ready.2.2.1, fun other => ?_⟩
    let slot : Fin width := ⟨nonce - (state.floor + 1), by omega⟩
    change Spent (mark state slot) other ↔ _
    have names : nonceAt state slot = nonce := by
      simp only [nonceAt, slot]
      have lower := ready.1
      omega
    rw [marking_spends_exactly_its_original_nonce, names]
  · cases accepted

def advance (state : Window width) : Window width :=
  ⟨state.floor + 1, fun slot =>
    if next : slot.val + 1 < width then state.bits ⟨slot.val + 1, next⟩ else false⟩

theorem compacting_one_resolved_head_preserves_all_spent_identities
    (state : Window width) (head : Spent state (state.floor + 1)) (nonce : Nat) :
    Spent (advance state) nonce ↔ Spent state nonce := by
  constructor
  · intro spent
    rcases spent with below | ⟨slot, names, set⟩
    · change nonce ≤ state.floor + 1 at below
      by_cases old : nonce ≤ state.floor
      · exact .inl old
      · have isHead : nonce = state.floor + 1 := by omega
        exact isHead.symm ▸ head
    · change (if next : slot.val + 1 < width then state.bits ⟨slot.val + 1, next⟩ else false) = true at set
      split at set
      · next next =>
        refine .inr ⟨⟨slot.val + 1, next⟩, ?_, set⟩
        change nonce = state.floor + 1 + slot.val + 1 at names
        change nonce = state.floor + (slot.val + 1) + 1
        omega
      · simp at set
  · intro spent
    rcases spent with below | ⟨slot, names, set⟩
    · exact .inl (by change nonce ≤ state.floor + 1; omega)
    · by_cases first : slot.val = 0
      · exact .inl (by change nonce ≤ state.floor + 1; omega)
      · have within := slot.isLt
        let previous : Fin width := ⟨slot.val - 1, by omega⟩
        have shifted : previous.val + 1 < width := by simp [previous]; omega
        have oldSlot : (⟨previous.val + 1, shifted⟩ : Fin width) = slot := by
          apply Fin.ext
          simp only [previous]
          omega
        refine .inr ⟨previous, ?_, ?_⟩
        · change nonce = state.floor + 1 + previous.val + 1
          simp only [previous]
          omega
        · change (if next : previous.val + 1 < width then state.bits ⟨previous.val + 1, next⟩ else false) = true
          rw [dite_eq_left shifted, oldSlot]
          exact set

inductive Step (limit : Nat) : Window width → Window width → Prop
  | consume {before after} (nonce : Nat) (accepted : consume limit before nonce = some after) :
      Step limit before after
  | compact {before} (head : Spent before (before.floor + 1)) :
      Step limit before (advance before)

inductive Trace (limit : Nat) : Window width → Window width → Prop
  | same (state : Window width) : Trace limit state state
  | next {first before after : Window width} :
      Trace limit first before → Step limit before after → Trace limit first after

theorem every_trace_preserves_past_decisions_and_the_issuance_limit
    (limit : Nat) (first after : Window width) (bounded : ∀ nonce, Spent first nonce → nonce ≤ limit)
    (history : Trace limit first after) :
    (∀ nonce, Spent first nonce → Spent after nonce) ∧ (∀ nonce, Spent after nonce → nonce ≤ limit) := by
  induction history with
  | same => exact ⟨fun _ prior => prior, bounded⟩
  | next _ event prior =>
    cases event with
    | consume nonce accepted =>
      obtain ⟨_, newFits, exact⟩ := a_successful_consume_is_in_range_unspent_and_exact limit _ _ nonce accepted
      refine ⟨fun old spent => (exact old).mpr (.inl (prior.1 old spent)), ?_⟩
      intro other spent
      rcases (exact other).mp spent with older | new
      · exact prior.2 other older
      · exact new.symm ▸ newFits
    | compact head =>
      have same := compacting_one_resolved_head_preserves_all_spent_identities _ head
      exact ⟨fun nonce spent => (same nonce).mpr (prior.1 nonce spent),
        fun nonce spent => prior.2 nonce ((same nonce).mp spent)⟩

noncomputable def normalizeFuel (state : Window width) : Nat → Window width
  | 0 => state
  | fuel + 1 => by
      classical
      exact if Spent state (state.floor + 1) then normalizeFuel (advance state) fuel else state

private theorem normalization_preserves_spent_and_finds_a_gap (state : Window width) (fuel : Nat) :
    let after := normalizeFuel state fuel
    (∀ nonce, Spent after nonce ↔ Spent state nonce) ∧
      (¬ Spent after (after.floor + 1) ∨ after.floor = state.floor + fuel) := by
  induction fuel generalizing state with
  | zero => exact ⟨fun _ => Iff.rfl, .inr (Nat.add_zero _).symm⟩
  | succ fuel prior =>
    classical
    by_cases head : Spent state (state.floor + 1)
    · simp only [normalizeFuel, ite_eq_left head]
      have normalized := prior (advance state)
      refine ⟨fun nonce => (normalized.1 nonce).trans
        (compacting_one_resolved_head_preserves_all_spent_identities state head nonce), ?_⟩
      rcases normalized.2 with gap | advanced
      · exact .inl gap
      · apply Or.inr
        change (normalizeFuel (advance state) fuel).floor = state.floor + (fuel + 1)
        change (normalizeFuel (advance state) fuel).floor = state.floor + 1 + fuel at advanced
        omega
    · simp [normalizeFuel, head]

noncomputable def normalize (state : Window width) : Window width :=
  normalizeFuel state width

theorem normalization_preserves_every_mark_and_has_an_unresolved_head
    (state : Window width) :
    (∀ nonce, Spent (normalize state) nonce ↔ Spent state nonce) ∧
      ¬ Spent (normalize state) ((normalize state).floor + 1) := by
  have evidence := normalization_preserves_spent_and_finds_a_gap state width
  refine ⟨evidence.1, ?_⟩
  intro resolved
  rcases evidence.2 with gap | advanced
  · exact gap resolved
  · have prior := (evidence.1 _).mp resolved
    rcases prior with below | ⟨slot, names, _⟩
    · change (normalizeFuel state width).floor + 1 ≤ state.floor at below
      omega
    · change (normalizeFuel state width).floor + 1 = state.floor + slot.val + 1 at names
      have within := slot.isLt
      omega

theorem equal_spent_sets_have_the_same_normalized_checkpoint
    (left right : Window width) (sameSpent : ∀ nonce, Spent left nonce ↔ Spent right nonce) :
    normalize left = normalize right := by
  let first := normalize left
  let second := normalize right
  have leftSpec := normalization_preserves_every_mark_and_has_an_unresolved_head left
  have rightSpec := normalization_preserves_every_mark_and_has_an_unresolved_head right
  have equivalent (nonce : Nat) : Spent first nonce ↔ Spent second nonce :=
    (leftSpec.1 nonce).trans ((sameSpent nonce).trans (rightSpec.1 nonce).symm)
  have floors : first.floor = second.floor := by
    rcases Nat.lt_trichotomy first.floor second.floor with before | equal | after
    · have covered : first.floor + 1 ≤ second.floor := by omega
      exact False.elim (leftSpec.2 ((equivalent (first.floor + 1)).mpr (.inl covered)))
    · exact equal
    · have covered : second.floor + 1 ≤ first.floor := by omega
      exact False.elim (rightSpec.2 ((equivalent (second.floor + 1)).mp (.inl covered)))
  have bitIsSpent (state : Window width) (slot : Fin width) :
      state.bits slot = true ↔ Spent state (nonceAt state slot) := by
    constructor
    · exact fun bit => .inr ⟨slot, rfl, bit⟩
    · intro resolved
      rcases resolved with below | ⟨other, names, set⟩
      · simp only [nonceAt] at below
        omega
      · have equal : other = slot := by
          apply Fin.ext
          simp only [nonceAt] at names
          omega
        exact equal ▸ set
  have bits : first.bits = second.bits := by
    funext slot
    have sameNonce : nonceAt first slot = nonceAt second slot := by simp [nonceAt, floors]
    have sameBit := (bitIsSpent first slot).trans
      ((equivalent (nonceAt first slot)).trans (sameNonce ▸ (bitIsSpent second slot).symm))
    exact Bool.eq_iff_iff.mpr sameBit
  exact Window.mk.injEq _ _ _ _ |>.mpr ⟨floors, bits⟩

noncomputable def choose (limit : Nat) (state : Window width) (nonce : Nat) : Option (Window width) :=
  (consume limit state nonce).map normalize

theorem a_normalized_decision_records_one_nonce_and_keeps_the_next_gap
    (limit : Nat) (state after : Window width) (nonce : Nat)
    (accepted : choose limit state nonce = some after) :
    (∀ other, Spent after other ↔ Spent state other ∨ other = nonce) ∧
      ¬ Spent after (after.floor + 1) := by
  unfold choose at accepted
  cases consumed : consume limit state nonce with
  | none => simp [consumed] at accepted
  | some intermediate =>
    simp [consumed] at accepted
    subst after
    let normalized := normalization_preserves_every_mark_and_has_an_unresolved_head intermediate
    let exact := a_successful_consume_is_in_range_unspent_and_exact limit state intermediate nonce consumed
    exact ⟨fun other => (normalized.1 other).trans (exact.2.2 other), normalized.2⟩

theorem width_one_preserves_next_only_admission
    (limit : Nat) (state : Window 1) (nonce : Nat)
    (gap : ¬ Spent state (state.floor + 1)) :
    (∃ after, choose limit state nonce = some after) ↔ nonce = state.floor + 1 ∧ nonce ≤ limit := by
  constructor
  · rintro ⟨after, accepted⟩
    simp only [choose, consume] at accepted
    split at accepted
    · next ready =>
      obtain ⟨lower, upper, bounded, _⟩ := ready
      exact ⟨by omega, bounded⟩
    · cases accepted
  · rintro ⟨rfl, bounded⟩
    have eligible : state.floor < state.floor + 1 ∧ state.floor + 1 ≤ state.floor + 1 ∧
        state.floor + 1 ≤ limit ∧ ¬ Spent state (state.floor + 1) :=
      ⟨by omega, by omega, bounded, gap⟩
    simp [choose, consume, eligible]

theorem independent_second_nonce_can_finish_while_the_first_stays_eligible
    (width limit : Nat) (twoSlots : 2 ≤ width) (twoNonces : 2 ≤ limit) :
    ∃ second first, consume limit (initial width) 2 = some second ∧
      Spent second 2 ∧ ¬ Spent second 1 ∧ consume limit second 1 = some first ∧
      Spent first 1 ∧ Spent first 2 := by
  have emptyPositive (nonce : Nat) (positive : 0 < nonce) : ¬ Spent (initial width) nonce := by
    simpa [initial, Spent] using (Nat.ne_of_gt positive)
  have canSecond : ∃ second, consume limit (initial width) 2 = some second := by
    unfold consume
    split
    · exact ⟨_, rfl⟩
    · next withheld =>
      exact False.elim (withheld ⟨by change 0 < 2; decide,
        by simpa [initial] using twoSlots, twoNonces, emptyPositive 2 (by decide)⟩)
  obtain ⟨second, acceptedSecond⟩ := canSecond
  have spentExactly := (a_successful_consume_is_in_range_unspent_and_exact limit _ _ 2 acceptedSecond).2.2
  have spentSecond := (spentExactly 2).mpr (.inr rfl)
  have fitsFirst : ¬ Spent second 1 := by
    rw [spentExactly 1]
    exact fun other => other.elim (emptyPositive 1 (by decide)) (by decide)
  have floorUnchanged : second.floor = 0 := by
    unfold consume at acceptedSecond
    split at acceptedSecond
    · cases acceptedSecond; rfl
    · cases acceptedSecond
  have canFirst : ∃ first, consume limit second 1 = some first := by
    unfold consume
    split
    · exact ⟨_, rfl⟩
    · next withheld =>
      exact False.elim (withheld ⟨by omega, by omega, by omega, fitsFirst⟩)
  obtain ⟨first, acceptedFirst⟩ := canFirst
  have firstExact := (a_successful_consume_is_in_range_unspent_and_exact limit _ _ 1 acceptedFirst).2.2
  exact ⟨second, first, acceptedSecond, spentSecond, fitsFirst, acceptedFirst,
    (firstExact 1).mpr (.inr rfl), (firstExact 2).mpr (.inl spentSecond)⟩

#print axioms marking_spends_exactly_its_original_nonce
#print axioms a_successful_consume_is_in_range_unspent_and_exact
#print axioms compacting_one_resolved_head_preserves_all_spent_identities
#print axioms every_trace_preserves_past_decisions_and_the_issuance_limit
#print axioms normalization_preserves_every_mark_and_has_an_unresolved_head
#print axioms equal_spent_sets_have_the_same_normalized_checkpoint
#print axioms a_normalized_decision_records_one_nonce_and_keeps_the_next_gap
#print axioms width_one_preserves_next_only_admission
#print axioms independent_second_nonce_can_finish_while_the_first_stays_eligible

end SelectiveReadWindow
