import Logkeeper.Codec
import Logkeeper.CompactImage

namespace Logkeeper.Codec

open Logkeeper.CompactImage

def optionalObjectNamesAdmissible (names : Option (List ObjectName)) : Prop :=
  match names with
  | none => True
  | some names => objectNamesCanonical names

def withdrawalIdentityAdmissible (name version : ObjectName) : Prop :=
  name ≠ zeroName ∧ version ≠ zeroName

/-- Projects the command variants whose fields impose a codec constraint. -/
inductive CommandAdmission where
  | fixedFields
  | append (names : Option (List ObjectName))
  | prepareCheckpoint (names : Option (List ObjectName))
  | withdrawObject (name version : ObjectName)

def commandAdmissible (command : CommandAdmission) : Prop :=
  match command with
  | .fixedFields => True
  | .append names | .prepareCheckpoint names => optionalObjectNamesAdmissible names
  | .withdrawObject name version => withdrawalIdentityAdmissible name version

def decisionBodyAdmissible (time : Bytes) (command : CommandAdmission) : Prop :=
  time.length = 8 ∧ commandAdmissible command

def decisionRequestBytes (frame : Bytes) : Bytes := frame.take 1 ++ frame.drop 9

def readFixedField (frame : Bytes) (width : Nat) : Option Bytes :=
  if width ≤ frame.length then some (frame.take width) else none

theorem fixed_field_round_trips_with_suffix (field suffix : Bytes) :
    readFixedField (field ++ suffix) field.length = some field := by
  simp [readFixedField]

inductive OperationAdmission where
  | fixedFields
  | execute (command : CommandAdmission)
  | reconcile (original : CommandAdmission)

def serviceOperationAdmissible (operation : OperationAdmission) : Prop :=
  match operation with
  | .fixedFields => True
  | .execute command | .reconcile command => commandAdmissible command

def recordAdmissible (payloadBytes : Nat) (names : Option (List ObjectName)) : Prop :=
  payloadBytes < 2^63 ∧ optionalObjectNamesAdmissible names

def withdrawnWorkerCountBounded (count : Nat) : Prop := count ≤ 64

inductive DecisionAdmission where
  | plain (isBarrier : Bool)
  | barrier (exactReceipt canonicalClaim : Bool)
  | rotation (hasBarrier coversReceipt : Bool)

def serviceDecisionAdmissible (decision : DecisionAdmission) : Prop :=
  match decision with
  | .plain isBarrier => isBarrier = false
  | .barrier exactReceipt canonicalClaim => exactReceipt = true ∧ canonicalClaim = true
  | .rotation hasBarrier coversReceipt => hasBarrier = false ∧ coversReceipt = true

inductive ReplyAdmission where
  | fixedFields
  | decision (withdrawal : Option (ObjectName × ObjectName)) (evidence : DecisionAdmission)
  | replay (records : List (Nat × Option (List ObjectName)))
  | withdrawnWorkers (count : Nat)

def serviceReplyAdmissible (reply : ReplyAdmission) : Prop :=
  match reply with
  | .fixedFields => True
  | .decision withdrawal evidence =>
      (match withdrawal with
       | none => True
       | some (name, version) => withdrawalIdentityAdmissible name version) ∧
      serviceDecisionAdmissible evidence
  | .replay records => ∀ row ∈ records, recordAdmissible row.1 row.2
  | .withdrawnWorkers count => withdrawnWorkerCountBounded count

theorem admitted_withdrawn_worker_count_fits_its_byte (count : Nat)
    (good : serviceReplyAdmissible (.withdrawnWorkers count)) :
    count.toUInt8.toNat = count := by
  simp only [serviceReplyAdmissible, withdrawnWorkerCountBounded] at good
  have fits : count < 256 := by omega
  simp [Nat.mod_eq_of_lt fits]

theorem service_rotation_round_trip_requires_absent_barrier (covers : Bool)
    (good : serviceDecisionAdmissible (.rotation true covers)) : False := by
  exact Bool.noConfusion good.1

theorem decision_body_round_trips_over_command_codec
    {Command : Type} (encodeCommand : Command → Bytes) (decodeCommand : Bytes → Option Command)
    (time : Bytes) (command : Command) (projection : CommandAdmission)
    (good : decisionBodyAdmissible time projection)
    (wire : ∃ rest, encodeCommand command = commandVersion :: rest)
    (bodyRoundTrip : decodeCommand (encodeCommand command) = some command) :
    let frame := decisionHeader time ++ (encodeCommand command).drop 1
    readDecisionTime frame = some time ∧
      decodeCommand (decisionRequestBytes frame) = some command := by
  obtain ⟨rest, wire⟩ := wire
  have width := good.1
  simp only [wire, List.drop_succ_cons, List.drop_zero]
  refine ⟨decision_time_round_trips time rest width, ?_⟩
  rw [wire] at bodyRoundTrip
  simpa [decisionRequestBytes, decisionHeader, List.drop_append, width] using bodyRoundTrip

#print axioms admitted_withdrawn_worker_count_fits_its_byte
#print axioms service_rotation_round_trip_requires_absent_barrier
#print axioms decision_body_round_trips_over_command_codec
#print axioms fixed_field_round_trips_with_suffix

end Logkeeper.Codec

namespace Logkeeper.CompactImage

open Logkeeper.Codec (Bytes)

def oldRootKeyIncreases (revision : Nat) (previous : Option Nat) : Prop :=
  match previous with
  | none => True
  | some key => key < revision

def objectControlTrailerCanonical (present : Bool) (roots fences : Nat) : Prop :=
  present = true ↔ roots ≠ 0 ∨ fences ≠ 0

theorem present_object_control_has_rows (roots fences : Nat)
    (accepted : objectControlTrailerCanonical true roots fences) : roots ≠ 0 ∨ fences ≠ 0 := by
  exact accepted.mp rfl

def receiptPositionFresh (positions : List Nat) (position : Nat) : Prop :=
  position ∉ positions

def receiptRowValid
    (snapshotPosition decisionPosition expiresAt retryHorizon : Nat) (noncePresent ownsLiveHold : Bool) :
    Prop :=
  noncePresent = true ∧ 0 < decisionPosition ∧ decisionPosition ≤ snapshotPosition ∧
  decisionPosition < expiresAt ∧ expiresAt - decisionPosition ≤ retryHorizon ∧
  (snapshotPosition < expiresAt ∨ ownsLiveHold = true)

theorem unexpired_receipt_is_within_retry_horizon
    (now position expires horizon : Nat) (liveHold : Bool)
    (valid : receiptRowValid now position expires horizon true liveHold) (future : now < expires) :
    0 < position ∧ position ≤ now ∧ now < position + horizon := by
  obtain ⟨_, positive, past, beforeExpiry, withinHorizon, _⟩ := valid
  exact ⟨positive, past, by omega⟩

theorem unexpired_receipt_count_bounded
    (positions : List Nat) (now horizon : Nat) (unique : receiptPositionsUnique positions)
    (inside : ∀ p ∈ positions, 0 < p ∧ p ≤ now ∧ now < p + horizon) :
    positions.length ≤ horizon := by
  have subset : positions ⊆ List.range' (now + 1 - horizon) horizon := by
    intro p member
    obtain ⟨positive, past, withinHorizon⟩ := inside p member
    apply List.mem_range'_1.mpr
    omega
  simpa using List.Nodup.length_le_of_subset unique subset

structure RetryRow where
  issuer : Nat
  nonce : Nat
  expiresAt : Nat
  decisionPosition : Nat
  deriving DecidableEq

def retryKey (row : RetryRow) : Nat × Nat × Nat :=
  (row.issuer, row.nonce, row.expiresAt)

def receiptPartition (rows : List RetryRow) (seen : List Nat) : Prop :=
  (rows.map retryKey).Nodup ∧
  receiptPositionsUnique (rows.map (·.decisionPosition)) ∧
  ∀ position, position ∈ seen ↔ position ∈ rows.map (·.decisionPosition)

def receiptExpiryPartition (rows : List RetryRow) (now : Nat) (entry : Nat × (Nat × Nat × Nat)) : Prop :=
  ∃ row ∈ rows, entry = (row.expiresAt, retryKey row) ∧ now < row.expiresAt

theorem fresh_receipt_preserves_partition (rows : List RetryRow) (seen : List Nat) (row : RetryRow)
    (partition : receiptPartition rows seen)
    (keyFresh : retryKey row ∉ rows.map retryKey)
    (fresh : receiptPositionFresh seen row.decisionPosition) :
    receiptPartition (row :: rows) (row.decisionPosition :: seen) := by
  obtain ⟨keys, positions, seenPositions⟩ := partition
  have newPosition : row.decisionPosition ∉ rows.map (·.decisionPosition) :=
    fun member => fresh ((seenPositions _).mpr member)
  refine ⟨List.nodup_cons.mpr ⟨keyFresh, keys⟩, List.nodup_cons.mpr ⟨newPosition, positions⟩, ?_⟩
  intro position
  simp [seenPositions]

theorem insertion_schedules_exactly_future_expiry (rows : List RetryRow) (row : RetryRow) (now : Nat)
    (entry : Nat × (Nat × Nat × Nat)) :
    receiptExpiryPartition (row :: rows) now entry ↔
      (entry = (row.expiresAt, retryKey row) ∧ now < row.expiresAt) ∨
        receiptExpiryPartition rows now entry := by
  simp only [receiptExpiryPartition, List.mem_cons]
  constructor
  · rintro ⟨candidate, equal | member, bound⟩
    · exact Or.inl (equal ▸ bound)
    · exact Or.inr ⟨candidate, member, bound⟩
  · rintro (bound | ⟨candidate, member, bound⟩)
    · exact ⟨row, Or.inl rfl, bound⟩
    · exact ⟨candidate, Or.inr member, bound⟩

/-- Conditions whose projections require the full Rust snapshot parser or reducer. -/
structure CompactImageAdmission where
  sameInitialConfiguration : Bool
  headerValid : Bool
  recordsValid : Bool
  checkpointAndHoldCutsValid : Bool
  receiptsValid : Bool
  derivedStateExact : Bool

def compactImageAdmissible (image : ReducerImage) (checks : CompactImageAdmission) : Prop :=
  reducerInvariant image ∧ checks.sameInitialConfiguration = true ∧ checks.headerValid = true ∧
  checks.recordsValid = true ∧ checks.checkpointAndHoldCutsValid = true ∧
  checks.receiptsValid = true ∧ checks.derivedStateExact = true

structure ObjectControlTrailer where
  roots : Nat
  fences : Nat
  bytes : Bytes

/-- Captures consumed bytes up to and including the old-root count, the old-root
row extents, the remainder through the leases, and any object-control trailer. -/
structure CompactImageLayout where
  header : Bytes
  oldRoots : List (Nat × Bytes)
  body : Bytes
  trailer : Option ObjectControlTrailer
  receiptPositions : List Nat

def compactImageBytesAdmissible (layout : CompactImageLayout) : Prop :=
  layout.oldRoots.Pairwise (fun a b => oldRootKeyIncreases b.1 (some a.1)) ∧
  (match layout.trailer with
   | none => objectControlTrailerCanonical false 0 0
   | some trailer => objectControlTrailerCanonical true trailer.roots trailer.fences) ∧
  receiptPositionsUnique layout.receiptPositions

def compactImageLayoutBytes (layout : CompactImageLayout) : Bytes :=
  layout.header ++ layout.oldRoots.flatMap Prod.snd ++ layout.body ++
    (layout.trailer.map ObjectControlTrailer.bytes).getD []

def canonicalCompactImageLayout (layout : CompactImageLayout) : CompactImageLayout :=
  { layout with
    oldRoots := layout.oldRoots.mergeSort (fun left right => left.1 ≤ right.1)
    trailer := layout.trailer.filter (fun t => t.roots ≠ 0 ∨ t.fences ≠ 0) }

theorem compact_image_layout_round_trips (layout : CompactImageLayout)
    (accepted : compactImageBytesAdmissible layout) :
    canonicalCompactImageLayout layout = layout := by
  have ordered : layout.oldRoots.Pairwise (fun a b => decide (a.1 ≤ b.1) = true) :=
    accepted.1.imp (fun lt => decide_eq_true (Nat.le_of_lt lt))
  have sorted := List.mergeSort_of_pairwise ordered
  have trailer : layout.trailer.filter (fun t => t.roots ≠ 0 ∨ t.fences ≠ 0) = layout.trailer := by
    have spelling := accepted.2.1
    cases h : layout.trailer with
    | none => rfl
    | some t =>
      simp only [h] at spelling
      have nonempty := present_object_control_has_rows _ _ spelling
      simp [nonempty]
  cases layout
  simp_all [canonicalCompactImageLayout]

theorem accepted_compact_image_bytes_reencode_exactly
    (bytes : Bytes) (decoded : CompactImageLayout)
    (accepted : compactImageBytesAdmissible decoded)
    (consumed : compactImageLayoutBytes decoded = bytes) :
    compactImageLayoutBytes (canonicalCompactImageLayout decoded) = bytes := by
  simpa [compact_image_layout_round_trips decoded accepted] using consumed

#print axioms fresh_receipt_preserves_partition
#print axioms insertion_schedules_exactly_future_expiry
#print axioms compact_image_layout_round_trips
#print axioms accepted_compact_image_bytes_reencode_exactly
#print axioms present_object_control_has_rows
#print axioms unexpired_receipt_is_within_retry_horizon
#print axioms unexpired_receipt_count_bounded

end Logkeeper.CompactImage
