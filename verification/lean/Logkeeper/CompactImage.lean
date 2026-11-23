import Std

namespace Logkeeper.CompactImage

def generationInRange (epoch generation : Nat) : Prop :=
  0 < generation ∧ generation ≤ max 1 epoch

structure Writer where
  epoch : Nat
  keyGeneration : Nat
  holder : Option Nat
  deriving DecidableEq

def vacateWriter (writer : Writer) : Writer := { writer with holder := none }

def snapshotGeneration (writer : Writer) : Nat := writer.keyGeneration

theorem vacancy_preserves_generation (writer : Writer) :
    snapshotGeneration (vacateWriter writer) = snapshotGeneration writer := by
  rfl

theorem vacant_generation_obeys_epoch (epoch generation : Nat)
    (accepted : generationInRange epoch generation) :
    generation ≠ 0 ∧ (epoch = 0 → generation = 1) := by
  rcases accepted with ⟨positive, bounded⟩
  refine ⟨by omega, ?_⟩
  intro zero
  rw [zero] at bounded
  simp at bounded
  omega

def leaseRowValid
    (serial lastSerial : Nat) (retained : Bool) (leaseEnd duration time : Nat)
    (keyIncreases : Bool) : Prop :=
  0 < serial ∧ serial ≤ lastSerial ∧ retained = true ∧
    duration ≤ leaseEnd ∧ leaseEnd ≤ time + duration ∧ keyIncreases = true

theorem accepted_lease_has_retained_owner_and_bounds
    (serial lastSerial : Nat) (retained : Bool) (leaseEnd duration time : Nat)
    (keyIncreases : Bool) (accepted : leaseRowValid serial lastSerial retained leaseEnd duration time keyIncreases) :
    retained = true ∧ duration ≤ leaseEnd ∧ leaseEnd ≤ time + duration := by
  exact ⟨accepted.2.2.1, accepted.2.2.2.1, accepted.2.2.2.2.1⟩

def fenceRowValid (position lastPosition time lastTime : Nat) (keyIncreases : Bool) : Prop :=
  0 < position ∧ position ≤ lastPosition ∧ time ≤ lastTime ∧ keyIncreases = true

theorem accepted_fence_has_bounded_coordinates
    (position lastPosition time lastTime : Nat) (keyIncreases : Bool)
    (accepted : fenceRowValid position lastPosition time lastTime keyIncreases) :
    position ≤ lastPosition ∧ time ≤ lastTime := by
  exact ⟨accepted.2.1, accepted.2.2.1⟩

def holdReceiptMatches (admittedAt : Nat) (receiptPosition : Option Nat) : Prop :=
  receiptPosition = some admittedAt

theorem every_checked_hold_has_a_matching_receipt (holds : List (Nat × Option Nat))
    (checked : ∀ row ∈ holds, holdReceiptMatches row.1 row.2) :
    ∀ row ∈ holds, ∃ position, row.2 = some position ∧ position = row.1 := by
  intro row member
  exact ⟨row.1, checked row member, rfl⟩

def objectNameCountFits (count maximum remaining : Nat) : Prop :=
  count ≤ maximum ∧ 32 * count ≤ remaining

theorem bounded_object_name_count_exact (count maximum remaining : Nat) :
    (count ≤ maximum ∧ count ≤ remaining / 32) ↔ objectNameCountFits count maximum remaining := by
  unfold objectNameCountFits
  omega

def rootReferenceRowValid (revision : Nat) (previous : Option Nat) (known : Bool) : Prop :=
  known = true ∧ match previous with
  | some key => key < revision
  | none => True

theorem accepted_reference_has_known_root_and_increasing_key
    (revision previous : Nat) (known : Bool)
    (accepted : rootReferenceRowValid revision (some previous) known) :
    known = true ∧ previous < revision :=
  accepted

def strictlyIncreasingKeys (keys : List Nat) : Prop := keys.Pairwise (· < ·)

theorem strictly_increasing_keys_are_unique (keys : List Nat) (ordered : strictlyIncreasingKeys keys) :
    keys.Nodup :=
  ordered.imp Nat.ne_of_lt

#print axioms vacancy_preserves_generation
#print axioms vacant_generation_obeys_epoch
#print axioms accepted_lease_has_retained_owner_and_bounds
#print axioms accepted_fence_has_bounded_coordinates
#print axioms every_checked_hold_has_a_matching_receipt
#print axioms bounded_object_name_count_exact
#print axioms accepted_reference_has_known_root_and_increasing_key
#print axioms strictly_increasing_keys_are_unique

end Logkeeper.CompactImage
