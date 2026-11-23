import Std

set_option warningAsError true

namespace Reservation

structure Slot where
  issuedThrough : Nat
  live : Option Nat

inductive Step : Slot → Slot → Prop
  | prepare {slot} (empty : slot.live = none) :
      Step slot ⟨slot.issuedThrough + 1, some (slot.issuedThrough + 1)⟩
  | consume {slot nonce} (_matches : slot.live = some nonce) :
      Step slot {slot with live := none}

def Stale (nonce : Nat) (slot : Slot) : Prop :=
  nonce ≤ slot.issuedThrough ∧ slot.live ≠ some nonce

inductive Trace : Slot → Slot → Prop
  | same (slot : Slot) : Trace slot slot
  | next {first before after} : Trace first before → Step before after → Trace first after

theorem stale_preserved {nonce : Nat} {before after : Slot}
    (stale : Stale nonce before) (step : Step before after) : Stale nonce after := by
  obtain ⟨issued, _⟩ := stale
  cases step with
  | prepare _ =>
      constructor
      · change nonce ≤ before.issuedThrough + 1
        omega
      · intro matchesNonce
        have sameNonce : before.issuedThrough + 1 = nonce := Option.some.inj matchesNonce
        omega
  | consume _ => exact ⟨issued, by simp⟩

theorem consumed_certificate_cannot_install
    {nonce : Nat} {justConsumed later : Slot}
    (stale : Stale nonce justConsumed) (trace : Trace justConsumed later) :
    later.live ≠ some nonce := by
  have staysStale : Stale nonce later := by
    induction trace with
    | same => exact stale
    | next _ step prior => exact stale_preserved prior step
  exact staysStale.2

theorem live_nonce_was_issued {first later : Slot} (empty : first.live = none)
    (trace : Trace first later) :
    ∀ nonce, later.live = some nonce → nonce ≤ later.issuedThrough := by
  induction trace with
  | same =>
      intro nonce present
      rw [empty] at present
      simp at present
  | next _ step _ =>
      cases step with
      | prepare _ =>
          intro nonce present
          exact Nat.le_of_eq (Option.some.inj present).symm
      | consume _ =>
          intro nonce present
          simp at present

theorem prepared_nonce_is_consumable (issuedThrough : Nat) :
    ∃ slot, Trace ⟨issuedThrough, none⟩ slot ∧ slot.live = some (issuedThrough + 1) :=
  ⟨_, .next (.same _) (.prepare rfl), rfl⟩

#print axioms consumed_certificate_cannot_install
#print axioms live_nonce_was_issued
#print axioms prepared_nonce_is_consumable

end Reservation
