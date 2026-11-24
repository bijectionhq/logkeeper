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

def allSnapshotRowsValid (rows : List α) (check : α → Prop) : Prop :=
  ∀ row ∈ rows, check row

theorem one_invalid_hold_prevents_recovery (rows : List α) (check : α → Prop)
    (row : α) (member : row ∈ rows) (invalid : ¬ check row) :
    ¬ allSnapshotRowsValid rows check := by
  intro accepted
  exact invalid (accepted row member)

def boundedMap (keys : List Nat) (limit : Nat) : Prop :=
  keys.length ≤ limit ∧ strictlyIncreasingKeys keys

def receiptPositionsUnique (positions : List Nat) : Prop := positions.Nodup

structure ReducerImage where
  position : Nat
  time : Nat
  epoch : Nat
  generation : Nat
  enrollmentSerial : Nat
  leaseDuration : Nat
  currentGrant : Option (Nat × Nat × Bool)
  rosterKeys : List Nat
  oldRootKeys : List Nat
  holdKeys : List Nat
  receiptKeys : List Nat
  leaseKeys : List Nat
  rootReferenceKeys : List Nat
  fenceKeys : List Nat
  rosterLimit : Nat
  oldRootLimit : Nat
  ordinaryHoldLimit : Nat
  activationHoldLimit : Nat
  retryHorizon : Nat
  leaseLimit : Nat
  rootReferenceLimit : Nat
  fenceLimit : Nat
  ordinaryHolds : Nat
  activationHolds : Nat
  holdReceipts : List (Nat × Option Nat)
  receiptPositions : List Nat
  leases : List (Nat × Nat × Bool)
  knownRootReferences : List Bool
  fences : List (Nat × Nat)
  completeReferences : Bool
  withdrawalReceiptsMatch : Bool
  references : List (List Nat)
  objectControlUsed : Nat
  objectControlCapacity : Nat

def reducerInvariant (image : ReducerImage) : Prop :=
  receiptPositionsUnique image.receiptPositions ∧
  generationInRange image.epoch image.generation ∧
  (match image.currentGrant with
    | some (epoch, generation, enrolled) =>
        enrolled = true ∧ 0 < epoch ∧ epoch = image.epoch ∧ generation = image.generation
    | none => True) ∧
  boundedMap image.rosterKeys image.rosterLimit ∧
  boundedMap image.oldRootKeys image.oldRootLimit ∧
  boundedMap image.holdKeys (image.ordinaryHoldLimit + image.activationHoldLimit) ∧
  image.ordinaryHolds ≤ image.ordinaryHoldLimit ∧
  image.activationHolds ≤ image.activationHoldLimit ∧
  image.holdKeys.length = image.ordinaryHolds + image.activationHolds ∧
  boundedMap image.receiptKeys (image.retryHorizon + image.ordinaryHoldLimit + image.activationHoldLimit) ∧
  boundedMap image.leaseKeys image.leaseLimit ∧
  boundedMap image.rootReferenceKeys image.rootReferenceLimit ∧
  boundedMap image.fenceKeys image.fenceLimit ∧
  image.holdReceipts.length = image.holdKeys.length ∧
  allSnapshotRowsValid image.holdReceipts (fun row => holdReceiptMatches row.1 row.2) ∧
  image.receiptPositions.length = image.receiptKeys.length ∧
  image.leases.length = image.leaseKeys.length ∧
  allSnapshotRowsValid image.leases (fun (serial, leaseEnd, retained) =>
    leaseRowValid serial image.enrollmentSerial retained leaseEnd image.leaseDuration image.time true) ∧
  image.knownRootReferences.length = image.rootReferenceKeys.length ∧
  allSnapshotRowsValid image.knownRootReferences (· = true) ∧
  image.fences.length = image.fenceKeys.length ∧
  allSnapshotRowsValid image.fences (fun row =>
    fenceRowValid row.1 image.position row.2 image.time true) ∧
  image.objectControlUsed ≤ image.objectControlCapacity ∧
  image.withdrawalReceiptsMatch = true ∧
  (0 < image.fenceKeys.length → image.completeReferences = true) ∧
  allSnapshotRowsValid image.references (fun names =>
    boundedMap names 16384 ∧ ∀ name ∈ names, name ≠ 0 ∧ name ∉ image.fenceKeys)

theorem the_reducer_invariant_excludes_reused_receipt_positions (image : ReducerImage)
    (valid : reducerInvariant image) : receiptPositionsUnique image.receiptPositions := by
  exact valid.1

#print axioms one_invalid_hold_prevents_recovery
#print axioms the_reducer_invariant_excludes_reused_receipt_positions
#print axioms vacancy_preserves_generation
#print axioms vacant_generation_obeys_epoch
#print axioms accepted_lease_has_retained_owner_and_bounds
#print axioms accepted_fence_has_bounded_coordinates
#print axioms every_checked_hold_has_a_matching_receipt
#print axioms bounded_object_name_count_exact
#print axioms accepted_reference_has_known_root_and_increasing_key
#print axioms strictly_increasing_keys_are_unique

end Logkeeper.CompactImage
