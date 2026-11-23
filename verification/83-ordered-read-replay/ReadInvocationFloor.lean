import Kernel
import EnvelopeCodec

set_option warningAsError true

namespace ReadInvocationFloor

open Kernel (Authority Writer)
open EnvelopeCodec (wordLimit)

def grant : Authority → Option Writer
  | .active writer | .vacant writer | .sealed _ writer => some writer
  | .retired => none

def Newer (before after : Writer) : Prop :=
  before.placement.generation < after.placement.generation ∨
    (before.placement = after.placement ∧ before.epoch < after.epoch)

def Advances : Option Writer → Option Writer → Prop
  | some before, some after => Newer before after
  | some _, none => True
  | none, _ => False

def Preserves (before after : Authority) (oldFloor newFloor : Nat) : Prop :=
  (grant before = grant after ∧ oldFloor ≤ newFloor) ∨ Advances (grant before) (grant after)

def Spent (current : Authority) (floor : Nat) (writer : Writer) (nonce : Nat) : Prop :=
  (grant current = some writer ∧ nonce ≤ floor) ∨ Advances (some writer) (grant current)

def Fresh (width : Nat) (current : Authority) (floor : Nat) (writer : Writer) (nonce : Nat) : Prop :=
  current = .active writer ∧ nonce = floor + 1 ∧ nonce < wordLimit width

noncomputable def carry (before after : Authority) (floor : Nat) : Nat := by
  classical
  exact if grant before = grant after then floor else 0

def CanCarry (before after : Authority) : Prop :=
  grant before = grant after ∨ Advances (grant before) (grant after)

private theorem newer_trans {first middle last : Writer} (early : Newer first middle)
    (late : Newer middle last) : Newer first last := by
  rcases early with generation | ⟨placement, epoch⟩ <;>
    rcases late with laterGeneration | ⟨laterPlacement, laterEpoch⟩
  · exact Or.inl (Nat.lt_trans generation laterGeneration)
  · exact Or.inl (laterPlacement ▸ generation)
  · exact Or.inl (placement.symm ▸ laterGeneration)
  · exact Or.inr ⟨placement.trans laterPlacement, Nat.lt_trans epoch laterEpoch⟩

theorem advances_trans {first middle last : Option Writer}
    (early : Advances first middle) (late : Advances middle last) : Advances first last := by
  cases first <;> cases middle <;> cases last <;> simp_all [Advances]
  exact newer_trans early late

theorem a_carried_floor_preserves_consumption (before after : Authority) (floor : Nat)
    (valid : CanCarry before after) : Preserves before after floor (carry before after floor) := by
  rcases valid with same | newer
  · exact Or.inl ⟨same, by simp [carry, same]⟩
  · exact Or.inr newer

theorem spent_survives_monotone_scope_and_floor {before after : Authority} {oldFloor newFloor : Nat}
    {writer : Writer} {nonce : Nat} (spent : Spent before oldFloor writer nonce)
    (change : Preserves before after oldFloor newFloor) : Spent after newFloor writer nonce := by
  rcases change with ⟨same, floor⟩ | advances
  · rcases spent with ⟨exactWriter, beforeFloor⟩ | newer
    · exact Or.inl ⟨same.symm.trans exactWriter, Nat.le_trans beforeFloor floor⟩
    · exact Or.inr (same ▸ newer)
  · rcases spent with ⟨exactWriter, _⟩ | newer
    · exact Or.inr (exactWriter ▸ advances)
    · exact Or.inr (advances_trans newer advances)

theorem a_spent_invocation_is_never_fresh {width floor nonce : Nat} {current : Authority} {writer : Writer}
    (spent : Spent current floor writer nonce) : ¬ Fresh width current floor writer nonce := by
  rintro ⟨active, next, _⟩
  rw [active] at spent
  rcases spent with ⟨_, earlier⟩ | later
  · omega
  · simp [Advances, grant, Newer] at later

theorem after_consumption_the_exact_invocation_is_spent {width floor nonce : Nat}
    {current : Authority} {writer : Writer} (fresh : Fresh width current floor writer nonce) :
    Spent current nonce writer nonce := by
  exact Or.inl ⟨by simp [fresh.1, grant], Nat.le_refl nonce⟩

theorem a_fresh_invocation_cannot_pass_the_next_nonce {width floor nonce : Nat}
    {current : Authority} {writer : Writer} (fresh : Fresh width current floor writer nonce) :
    nonce ≤ floor + 1 := by
  exact Nat.le_of_eq fresh.2.1

theorem at_width_exhaustion_no_nonce_can_be_admitted {width floor : Nat}
    (current : Authority) (writer : Writer) (nonce : Nat) (atLimit : wordLimit width ≤ floor + 1) :
    ¬ Fresh width current floor writer nonce := by
  rintro ⟨_, next, fits⟩
  omega

theorem a_root_scope_change_preserves_spent_without_old_per_grant_rows (old new : Writer)
    (newer : Newer old new) (nonce : Nat) :
    Spent (.active new) 0 old nonce ∧ CanCarry (.active old) (.active new) := by
  exact ⟨Or.inr newer, Or.inr newer⟩

end ReadInvocationFloor
