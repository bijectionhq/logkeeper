import Logkeeper.Generated.Verus

set_option warningAsError true
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Logkeeper.Generated

private theorem indexed_members {T : Type} [Nonempty T] (xs : List T) (p : T → Prop) :
    (∀ i : Int, (0 ≤ i ∧ i < (↑xs.length : Int)) → p (seqIndex xs i)) ↔
      ∀ x ∈ xs, p x := by
  constructor
  · intro all x mem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mem
    have within := List.getElem?_eq_some_iff.mp hi
    obtain ⟨bounds, _⟩ := within
    simpa [seqIndex, hi] using all (i : Int) ⟨by omega, by omega⟩
  · intro all i ⟨nonnegative, bounds⟩
    have hi : i.toNat < xs.length := by omega
    have mem := List.getElem_mem (l := xs) hi
    simpa [seqIndex, nonnegative, List.getElem?_eq_getElem hi] using all _ mem

private theorem indexed_pairs {T : Type} [Nonempty T] (xs : List T) (p : T → T → Prop) :
    (∀ i j : Int, (0 ≤ i ∧ i < j ∧ j < (xs.length : Int)) → p (seqIndex xs i) (seqIndex xs j)) ↔
      xs.Pairwise p := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro all i j hi hj order
    simpa [seqIndex, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using
      all (i : Int) (j : Int) ⟨by omega, by omega, by omega⟩
  · intro all i j ⟨lower, order, upper⟩
    have hi : i.toNat < xs.length := by omega
    have hj : j.toNat < xs.length := by omega
    have nonneg : 0 ≤ j := by omega
    simpa [seqIndex, lower, nonneg, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using
      all i.toNat j.toNat hi hj (by omega)


-- Natural coordinates are embedded in Int. The codec's machine bounds and
-- fixed-width carriers are additional domains of its Verus call sites.
namespace compact_image
open Logkeeper.CompactImage

theorem link_generationInRange (epoch generation : Nat) :
    generationInRange epoch generation ↔ Logkeeper.CompactImage.generationInRange epoch generation := by
  unfold generationInRange Logkeeper.CompactImage.generationInRange
  split <;> omega

theorem link_leaseRowValid (serial lastSerial leaseEnd duration time : Nat) (retained increases : Bool) :
    leaseRowValid serial lastSerial retained leaseEnd duration time increases ↔
      Logkeeper.CompactImage.leaseRowValid serial lastSerial retained leaseEnd duration time increases := by
  simp [leaseRowValid, Logkeeper.CompactImage.leaseRowValid, ← Int.natCast_add, and_assoc]

theorem link_fenceRowValid (position lastPosition time lastTime : Nat) (increases : Bool) :
    fenceRowValid position lastPosition time lastTime increases ↔
      Logkeeper.CompactImage.fenceRowValid position lastPosition time lastTime increases := by
  simp [fenceRowValid, Logkeeper.CompactImage.fenceRowValid, and_assoc]

theorem link_holdReceiptMatches (position : Nat) (receipt : Option Nat) :
    holdReceiptMatches position receipt ↔ Logkeeper.CompactImage.holdReceiptMatches position receipt := by
  rfl

theorem link_rootReferenceRowValid (revision : Nat) (previous : Option Nat) (known : Bool) :
    rootReferenceRowValid revision previous known ↔
      Logkeeper.CompactImage.rootReferenceRowValid revision previous known := by
  cases previous <;> simp [rootReferenceRowValid, oldRootKeyIncreases, Logkeeper.CompactImage.rootReferenceRowValid]


theorem link_allSnapshotRowsValid {R : Type} [Nonempty R] (rows : List R) (passing : R → Prop) :
    allSnapshotRowsValid (seqSet rows) passing ↔ Logkeeper.CompactImage.allSnapshotRowsValid rows passing := by
  rfl

theorem link_strictlyIncreasingKeys (keys : List Nat) :
    strictlyIncreasingKeys (intKeys keys) ↔ Logkeeper.CompactImage.strictlyIncreasingKeys keys := by
  unfold strictlyIncreasingKeys
  simp only [and_assoc, indexed_pairs, intKeys, List.pairwise_map,
    Logkeeper.CompactImage.strictlyIncreasingKeys]
  exact ⟨fun h => h.imp (fun order => Int.ofNat_lt.mp order),
    fun h => h.imp (fun order => Int.ofNat_lt.mpr order)⟩

theorem link_boundedMap (keys : List Nat) (limit : Nat) :
    boundedMap (intKeys keys) limit ↔ Logkeeper.CompactImage.boundedMap keys limit := by
  rw [boundedMap, link_strictlyIncreasingKeys]
  simp [Logkeeper.CompactImage.boundedMap, intKeys]

theorem link_receiptPositionsUnique (positions : List Nat) :
    receiptPositionsUnique positions ↔ Logkeeper.CompactImage.receiptPositionsUnique positions := by
  simp only [receiptPositionsUnique, and_assoc, indexed_pairs,
    Logkeeper.CompactImage.receiptPositionsUnique, List.nodup_iff_pairwise_ne]

theorem link_reducerInvariant (image : Logkeeper.CompactImage.ReducerImage) :
    reducerInvariant image ↔ Logkeeper.CompactImage.reducerInvariant image := by
  have grant :
      (match image.currentGrant with
        | some (epoch, generation, enrolled) => (((enrolled = true ∧ 0 < epoch) ∧ epoch = image.epoch) ∧ generation = image.generation)
        | none => true = true) ↔
      (match image.currentGrant with
        | some (epoch, generation, enrolled) => enrolled = true ∧ 0 < epoch ∧ epoch = image.epoch ∧ generation = image.generation
        | none => True) := by
    cases image.currentGrant <;> simp [and_assoc]
  have length (keys : List Nat) : (intKeys keys).length = keys.length := by simp [intKeys]
  have mem (key : Nat) : (key : Int) ∈ intKeys image.fenceKeys ↔ key ∈ image.fenceKeys := by
    rw [intKeys, List.mem_map]
    constructor
    · rintro ⟨x, inside, same⟩
      exact Int.ofNat.inj same ▸ inside
    · exact fun inside => ⟨key, inside, rfl⟩
  let validName := fun name : Int => name ≠ 0 ∧ name ∉ intKeys image.fenceKeys
  let validNames := fun keys : List Int => keys.length ≤ 16384 ∧ strictlyIncreasingKeys keys ∧
    ∀ name ∈ keys, validName name
  have refs (keys : List Nat) : validNames (intKeys keys) ↔
      (Logkeeper.CompactImage.boundedMap keys 16384 ∧ ∀ name ∈ keys, name ≠ 0 ∧ name ∉ image.fenceKeys) := by
    simp only [validNames, length, link_strictlyIncreasingKeys, Logkeeper.CompactImage.boundedMap, and_assoc]
    have row : (∀ name ∈ intKeys keys, validName name) ↔ ∀ name ∈ keys, name ≠ 0 ∧ name ∉ image.fenceKeys := by
      rw [intKeys, List.forall_mem_map]
      simp [validName, mem]
    rw [row]
  have holds := indexed_members image.holdReceipts
    (fun row => Logkeeper.CompactImage.holdReceiptMatches row.1 row.2)
  have leases := indexed_members image.leases (fun row =>
    Logkeeper.CompactImage.leaseRowValid row.1 image.enrollmentSerial row.2.2 row.2.1 image.leaseDuration image.time true)
  have known := indexed_members image.knownRootReferences (· = true)
  have fences := indexed_members image.fences (fun row =>
    Logkeeper.CompactImage.fenceRowValid row.1 image.position row.2 image.time true)
  have names (keys : List Int) :
      (∀ j : Int, (0 ≤ j ∧ j < (keys.length : Int)) →
        seqIndex keys j ≠ 0 ∧ ¬ List.Mem (seqIndex keys j) (intKeys image.fenceKeys)) ↔
      ∀ name ∈ keys, validName name :=
    indexed_members keys validName
  have lists := indexed_members (intReferences image.references) validNames
  have references :
      (∀ i : Int, (0 ≤ i ∧ i < ((intReferences image.references).length : Int)) →
        validNames (seqIndex (intReferences image.references) i)) ↔
      ∀ row ∈ image.references, Logkeeper.CompactImage.boundedMap row 16384 ∧
        ∀ name ∈ row, name ≠ 0 ∧ name ∉ image.fenceKeys := by
    rw [lists, intReferences, List.forall_mem_map]
    simp only [refs]
  simp only [reducerInvariant, Logkeeper.CompactImage.reducerInvariant, link_generationInRange,
    link_boundedMap, link_receiptPositionsUnique, length, and_assoc, grant,
    link_holdReceiptMatches, link_leaseRowValid, link_fenceRowValid, Logkeeper.CompactImage.allSnapshotRowsValid]
  rw [holds, leases, known, fences]
  simp only [names]
  rw [references]
  grind only



theorem link_oldRootKeyIncreases (revision : Nat) (previous : Option Nat) :
    oldRootKeyIncreases revision previous ↔ Logkeeper.CompactImage.oldRootKeyIncreases revision previous := by
  cases previous <;> simp [oldRootKeyIncreases, Logkeeper.CompactImage.oldRootKeyIncreases]

theorem link_objectControlTrailerCanonical (present : Bool) (roots fences : Nat) :
    objectControlTrailerCanonical present roots fences ↔
      Logkeeper.CompactImage.objectControlTrailerCanonical present roots fences := by
  rfl

theorem link_receiptPositionFresh (positions : List Nat) (position : Nat) :
    receiptPositionFresh (seqSet positions) position ↔ Logkeeper.CompactImage.receiptPositionFresh positions position := by
  rfl

theorem link_receiptRowValid (now position expiry horizon : Nat) (nonce hold : Bool) :
    receiptRowValid now position expiry horizon nonce hold ↔
      Logkeeper.CompactImage.receiptRowValid now position expiry horizon nonce hold := by
  have horizonBound : ((expiry : Int) - (position : Int) ≤ (horizon : Int)) ↔
      expiry - position ≤ horizon := by omega
  simp only [receiptRowValid, Logkeeper.CompactImage.receiptRowValid, horizonBound, and_assoc]

end compact_image

namespace ordered_admission

theorem link_debit (used charge ceiling : Nat) :
    debit used charge ceiling = Logkeeper.OrderedAdmission.debit used charge ceiling := by
  rfl

theorem link_pinsSuffix (start stop floor : Nat) :
    pinsSuffix start stop floor ↔ Logkeeper.OrderedAdmission.pinsSuffix start stop floor := by
  rfl

theorem link_retainsReceipt (position expiresAt : Nat) (owns : Bool) :
    retainsReceipt position expiresAt owns ↔ Logkeeper.OrderedAdmission.retainsReceipt position expiresAt owns := by
  rfl

theorem link_matchesFingerprint (stored presented : List UInt8) :
    matchesFingerprint stored presented ↔ Logkeeper.OrderedAdmission.matchesFingerprint stored presented := by
  rfl

end ordered_admission

namespace ordered_budgets

theorem link_referenceCharge (references : Option Nat) :
    referenceCharge references = Int.ofNat (Logkeeper.OrderedBudgets.referenceCharge references) := by
  cases references <;> simp [referenceCharge, Logkeeper.OrderedBudgets.referenceCharge]

theorem link_recordCharge (payload : Nat) (references : Option Nat) :
    recordCharge payload references = Int.ofNat (Logkeeper.OrderedBudgets.recordCharge payload references) := by
  simp [recordCharge, Logkeeper.OrderedBudgets.recordCharge, link_referenceCharge]

theorem link_fundedBudget (budget : Logkeeper.OrderedBudgets.Budget) (window capacity reserve : Nat) :
    fundedBudget budget.spent budget.ordinary budget.maintenance window capacity reserve ↔
      Logkeeper.OrderedBudgets.fundedBudget budget window capacity reserve := by
  unfold fundedBudget Logkeeper.OrderedBudgets.fundedBudget
  omega

end ordered_budgets

namespace ordered_codec

theorem link_commandVersion : commandVersion = Logkeeper.Codec.commandVersion := by
  rfl

theorem link_decisionHeader (time : List UInt8) :
    decisionHeader time = Logkeeper.Codec.decisionHeader time := by
  rfl

theorem link_decisionHeaderMatches (frame time : List UInt8) :
    decisionHeaderMatches frame time ↔ Logkeeper.Codec.decisionHeaderMatches frame time := by
  cases frame with
  | nil => simp [decisionHeaderMatches, Logkeeper.Codec.decisionHeaderMatches, Logkeeper.Codec.decisionHeader]
  | cons tag rest =>
    have slice (size : 8 ≤ rest.length) : seqSubrange (tag :: rest) 1 9 = rest.take 8 := by
      have inside : (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 9 ∧ (9 : Int) ≤ ↑(tag :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [seqSubrange, ite_eq_left inside]
      rfl
    unfold decisionHeaderMatches Logkeeper.Codec.decisionHeaderMatches
    simp only [Logkeeper.Codec.decisionHeader, ← link_commandVersion, List.take_succ_cons, List.cons.injEq]
    constructor
    · rintro ⟨⟨size, same⟩, equal⟩
      have width : 8 ≤ rest.length := by simpa using size
      rw [slice width] at equal
      have extent : time.length = 8 := by rw [equal, List.length_take, Nat.min_eq_left width]
      exact ⟨extent, by simpa [seqIndex] using same, equal.symm⟩
    · rintro ⟨extent, same, equal⟩
      have length := congrArg List.length equal
      rw [List.length_take, extent] at length
      have width : 8 ≤ rest.length := by omega
      rw [slice width]
      exact ⟨⟨by simpa using width, by simpa [seqIndex] using same⟩, equal.symm⟩

theorem link_flagByte (value : Bool) : flagByte value = Logkeeper.Codec.flagByte value := by
  rfl

theorem link_readFlag (tag : UInt8) : readFlag tag = Logkeeper.Codec.readFlag tag := by
  rfl

theorem link_bodyLengthBounded (declared minimum maximum : Nat) :
    bodyLengthBounded declared minimum maximum ↔ Logkeeper.Codec.bodyLengthBounded declared minimum maximum := by
  simp [bodyLengthBounded, Logkeeper.Codec.bodyLengthBounded]

theorem link_objectNameCountFits (count maximum remaining : Nat) :
    objectNameCountFits count maximum remaining ↔ Logkeeper.CompactImage.objectNameCountFits count maximum remaining := by
  unfold objectNameCountFits Logkeeper.CompactImage.objectNameCountFits
  omega


private theorem bounded_take (frame : List UInt8) (width : Nat) (fits : width ≤ frame.length) :
    seqTake frame (width : Int) = frame.take width := by
  unfold seqTake seqSubrange
  rw [ite_eq_left (by omega)]
  simp

private theorem bounded_drop (frame : List UInt8) (width : Nat) (fits : width ≤ frame.length) :
    seqDrop frame (width : Int) = frame.drop width := by
  unfold seqDrop seqSubrange
  rw [ite_eq_left (by omega)]
  have remaining : ((frame.length : Int) - (width : Int)).toNat = frame.length - width := by omega
  rw [remaining]
  simp [List.take_of_length_le]

theorem link_decisionRequestBytes (frame : List UInt8) (header : 9 ≤ frame.length) :
    decisionRequestBytes frame = Logkeeper.Codec.decisionRequestBytes frame := by
  rw [decisionRequestBytes, Logkeeper.Codec.decisionRequestBytes]
  rw [show (1 : Int) = ((1 : Nat) : Int) by rfl, bounded_take frame 1 (by omega)]
  rw [show (9 : Int) = ((9 : Nat) : Int) by rfl, bounded_drop frame 9 header]

theorem link_withdrawalIdentityAdmissible (name version : List UInt8) :
    withdrawalIdentityAdmissible name version ↔ Logkeeper.Codec.withdrawalIdentityAdmissible name version := by
  rfl

theorem link_withdrawnWorkerCountBounded (count : Nat) :
    withdrawnWorkerCountBounded count ↔ Logkeeper.Codec.withdrawnWorkerCountBounded count := by
  unfold withdrawnWorkerCountBounded Logkeeper.Codec.withdrawnWorkerCountBounded
  omega

theorem link_readFixedField (frame : List UInt8) (width : Nat) :
    readFixedField frame width = Logkeeper.Codec.readFixedField frame width := by
  unfold readFixedField Logkeeper.Codec.readFixedField
  split
  · rename_i fits
    rw [bounded_take frame width fits]
  · rfl

end ordered_codec

namespace object_withdrawal

open Logkeeper.ObjectWithdrawal (State)


theorem link_fenced {K F : Type} [Nonempty K] [Nonempty F] (s : State K F) (name : K) :
    fenced s.fence name ↔ Logkeeper.ObjectWithdrawal.fenced s name := by
  rfl

theorem link_canAdmitReferences {K F : Type} [Nonempty K] [Nonempty F]
    (s : State K F) (names : List K) :
    canAdmitReferences s.fence names ↔ Logkeeper.ObjectWithdrawal.canAdmitReferences s (some names) := by
  exact indexed_members names (fun name => ¬ fenced s.fence name)

theorem link_canWithdraw {K F : Type} (s : State K F) (name : K) (known present : Bool)
    (complete : (known = true) ↔ ¬ s.hasOpaqueReferences)
    (live : (present = true) ↔ Logkeeper.ObjectWithdrawal.referenced s name) :
    canWithdraw known present ↔ Logkeeper.ObjectWithdrawal.canWithdraw s name := by
  simp [canWithdraw, Logkeeper.ObjectWithdrawal.canWithdraw, complete, live]

end object_withdrawal

namespace ordered_receipt

open Logkeeper.Protocol.Ordered (RetainedReceipt)

theorem link_abstract_book {K R : Type} [Nonempty K] [Nonempty R]
    (book : K → Option (RetainedReceipt (List UInt8) R)) (key : K) :
    abstract_book book key = Logkeeper.Protocol.Ordered.abstract_book book key := by
  cases h : book key <;> simp [abstract_book, Logkeeper.Protocol.Ordered.abstract_book, mapContains, mapIndex, h]

theorem link_replay_mutation {R : Type} [Nonempty R] (stored presented : List UInt8) (original : R) :
    replay_mutation stored presented original =
      Logkeeper.Protocol.Ordered.replay_mutation stored presented original := by
  rfl

theorem link_replay {R : Type} [Nonempty R] (reading : Bool) (stored presented : List UInt8) (original : R) :
    replay reading stored presented original = Logkeeper.Protocol.Ordered.replay reading stored presented original := by
  rfl

theorem link_record_after_apply {O E : Type} [Nonempty O] [Nonempty E] (reading : Bool) (applied : Except E O) :
    record_after_apply reading applied ↔ Logkeeper.Protocol.Ordered.record_after_apply reading applied = true := by
  cases reading <;> cases applied <;> simp [record_after_apply, Logkeeper.Protocol.Ordered.record_after_apply]

theorem link_retain_applied {O E : Type} [Nonempty O] [Nonempty E] (reading : Bool) (applied : Except E O) :
    retain_applied reading applied = Logkeeper.Protocol.Ordered.retain_applied reading applied := by
  simp [retain_applied, Logkeeper.Protocol.Ordered.retain_applied, link_record_after_apply]

theorem link_retains_receipt (pos expiry : Nat) (hold : Bool) :
    retains_receipt pos expiry hold ↔ Logkeeper.Protocol.Ordered.retains_receipt pos expiry hold = true := by
  simp [retains_receipt, Logkeeper.Protocol.Ordered.retains_receipt]

end ordered_receipt

namespace ordered_writer

open Logkeeper.Kernel (Authority Entry Placement State Writer)
open Logkeeper.Kernel.Ordered (Image)

deriving instance Nonempty for Placement, Writer, Entry

theorem link_authorize_writer {E : Type} [Nonempty E] [DecidableEq E]
    (principal : Option E) (current : Option (E × Nat × Nat)) (presented : E × Nat × Nat) :
    authorize_writer principal current presented ↔
      Logkeeper.Kernel.Ordered.authorize_writer principal current presented = true := by
  simp [authorize_writer, Logkeeper.Kernel.Ordered.authorize_writer]

theorem link_append_next_lsn (head expected limit : Nat) :
    append_next_lsn head expected limit =
      (Logkeeper.Kernel.Ordered.append_next_lsn head expected limit).map Int.ofNat := by
  by_cases h : head = expected ∧ expected < limit <;>
    simp [append_next_lsn, Logkeeper.Kernel.Ordered.append_next_lsn, h, Int.natCast_inj]

theorem link_next_writer_epoch (epoch limit : Nat) :
    next_writer_epoch epoch limit = (Logkeeper.Kernel.Ordered.next_writer_epoch epoch limit).map Int.ofNat := by
  simp [next_writer_epoch, Logkeeper.Kernel.Ordered.next_writer_epoch, apply_ite]

theorem link_withdraw_grant {G : Type} [Nonempty G] (grant : Option G) (holderMatches : Bool) :
    withdraw_grant grant holderMatches = Logkeeper.Kernel.Ordered.withdraw_grant grant holderMatches := by
  rfl

private def authority : AbstractAuthority Writer → Authority
  | .active grant => .active grant
  | .vacant previous => .vacant previous

theorem link_abstract_authority (grant : Option Writer) (previous : Writer) :
    authority (abstract_authority grant previous) = Logkeeper.Kernel.Ordered.abstract_authority grant previous := by
  cases grant <;> rfl

theorem link_abstract_history {P : Type} [Nonempty P] (compacted records : List (Entry P)) :
    abstract_history compacted records = Logkeeper.Kernel.Ordered.abstract_history compacted records := by
  rfl

theorem link_abstract_state {P : Type} [Nonempty P] (image : Image P) :
    let view := abstract_state (if image.active then some image.writer else none) image.writer
      image.compacted image.records
    ({ authority := authority view.1, history := view.2 } : State P) = Logkeeper.Kernel.Ordered.abstract_state image := by
  simp [abstract_state, Logkeeper.Kernel.Ordered.abstract_state, link_abstract_authority, link_abstract_history]

end ordered_writer

namespace ordered_rotation

private theorem cutEq (head cut : Cut) : head = cut ↔ head.nextLsn = cut.nextLsn ∧ head.history = cut.history := by
  cases head <;> cases cut <;> simp

theorem link_rotation_head {G C : Type} [Nonempty G] [Nonempty C] [DecidableEq G] [DecidableEq C]
    (custodian : Bool) (current : Option G) (grant : G) (head cut : Cut) (published requested : C) :
    rotation_head custodian current grant head cut published requested ↔
      ErasureCommit.rotation_head custodian current grant head cut published requested = true := by
  simp [rotation_head, ErasureCommit.rotation_head, cutEq, and_assoc]

theorem link_exact_preparation {C : Type} [Nonempty C] [DecidableEq C]
    (preparedCut cut : Cut) (preparedRoot root : List UInt8) (preparedCustody custody : C)
    (manifestPresent : Bool) (observed : Option Cut) :
    exact_preparation preparedCut cut preparedRoot root preparedCustody custody manifestPresent observed ↔
      ErasureCommit.exact_preparation preparedCut cut preparedRoot root preparedCustody custody manifestPresent observed = true := by
  cases observed <;> simp [exact_preparation, ErasureCommit.exact_preparation, cutEq, and_assoc]

theorem link_successor_generation {G C : Type} [Nonempty G] [Nonempty C] [DecidableEq G] [DecidableEq C]
    (erasure : Bool) (source grant : G) (base published : C) (generation : Nat) :
    successor_generation erasure source grant base published generation =
      ErasureCommit.successor_generation erasure source grant base published generation (2 ^ 64 - 1) := by
  have maxValue : (2 : Nat) ^ 64 - 1 = 18446744073709551615 := by decide
  unfold successor_generation ErasureCommit.successor_generation Logkeeper.Kernel.Ordered.next_writer_epoch
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, ← maxValue]
  by_cases enough : generation < 2 ^ 64 - 1
  · have fits : generation + 1 < 2 ^ 64 := by omega
    have sum : (generation : Int) + 1 = ((generation + 1 : Nat) : Int) := by omega
    rw [sum, clipUnsigned_nat 64 _ fits]
    simp [enough]
  · simp [enough]

theorem link_erasure_floor (previous cut : Nat) (closes : Bool) :
    erasure_floor previous cut closes = ErasureCommit.erasure_floor previous cut closes := by
  rfl

theorem link_admits_history (floor start : Nat) :
    admits_history floor start ↔ ErasureCommit.admits_history floor start = true := by
  simp [admits_history, ErasureCommit.admits_history]

end ordered_rotation

namespace ordered_serving_lease

theorem link_decision_time (previous incoming : Nat) :
    decision_time previous incoming = DisposalLease.decision_time previous incoming := by
  rfl

theorem link_lease_end {E : Type} [Nonempty E] [DecidableEq E]
    (principal enrolled : Option E) (current : Option (E × Nat × Nat)) (grant : E × Nat × Nat)
    (now duration : Nat) :
    lease_end principal current grant enrolled now duration =
      DisposalLease.lease_end principal current grant enrolled now duration (2 ^ 64 - 1) := by
  have test : ((now : Int) + (duration : Int) ≤ ((18446744073709551615 : Nat) : Int)) ↔
      now + duration ≤ (2 : Nat) ^ 64 - 1 := by omega
  unfold lease_end DisposalLease.lease_end
  simp only [test, Logkeeper.Kernel.Ordered.authorize_writer, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  split
  · rename_i admitted
    rw [← Int.natCast_add, clipUnsigned_nat]
    have fits := admitted.2.2.2
    omega
  · rfl

theorem link_withdrawn (serial last : Nat) (enrolled : Bool) :
    withdrawn serial last enrolled ↔ DisposalLease.withdrawn serial last enrolled = true := by
  simp [withdrawn, DisposalLease.withdrawn, and_assoc]

theorem link_may_dispose (stop drift now : Nat) :
    may_dispose stop drift now ↔ DisposalLease.MayDispose stop drift now := by
  simp [may_dispose, DisposalLease.MayDispose, ← Int.natCast_add]

theorem link_admits (stop workerClock : Nat) :
    admits stop workerClock ↔ DisposalLease.Admits stop workerClock := by
  rfl

theorem link_withdrawn_owners {H W E : Type} [Nonempty H] [Nonempty W] [Nonempty E]
    [Ord E] [LT E] (order : ∀ a b : E, compare a b = .lt ↔ a < b)
    (witnesses : List H) (roster : W → Option E) (project : H → E × W) (after : Option E) (owner : E) :
    withdrawn_owners (seqSet witnesses) roster project after owner ↔
      DisposalLease.qualifying_owners (witnesses.map project) roster after owner := by
  simp only [withdrawn_owners, DisposalLease.qualifying_owners, DisposalLease.eligible_owner,
    setContains, seqSet, id_eq]
  constructor
  · rintro ⟨entry, ⟨⟨mem, same⟩, withdrawn⟩, later⟩
    refine ⟨(project entry).2, List.mem_map.mpr ⟨entry, mem, Prod.ext same.symm rfl⟩, ?_, withdrawn⟩
    cases after with
    | none => trivial
    | some cursor =>
      apply (order cursor owner).mp
      cases h : compare cursor owner <;> simp_all
  · rintro ⟨worker, member, later, withdrawn⟩
    obtain ⟨entry, mem, equal⟩ := List.mem_map.mp member
    have ownerEq := congrArg Prod.fst equal
    have workerEq := congrArg Prod.snd equal
    refine ⟨entry, ⟨⟨mem, ownerEq.symm⟩, ?_⟩, ?_⟩
    · rwa [workerEq]
    · cases after with
      | none => trivial
      | some cursor =>
        have h := (order cursor owner).mpr later
        simp [h]

end ordered_serving_lease

namespace ordered_trim

theorem link_pinsSuffix (start stop floor : Nat) :
    pinsSuffix start stop floor ↔ Logkeeper.Protocol.pinsSuffix start stop floor := by
  rfl

theorem link_trimPrefixSafe (floor through checkpoint start stop : Nat) :
    trimPrefixSafe floor through checkpoint start stop ↔
      Logkeeper.Protocol.trimPrefixSafe floor through checkpoint [(start, stop)] := by
  unfold trimPrefixSafe between Logkeeper.Protocol.trimPrefixSafe
  constructor
  · intro safe lsn lower upper
    have available :=  safe lsn ⟨by omega, by omega⟩
    simpa using available
  · intro safe lsn ⟨lower, upper⟩
    have projected : (lsn.toNat : Int) = lsn := by omega
    obtain ⟨within, outside⟩ := safe lsn.toNat (by omega) (by omega)
    have pin := outside (start, stop) (by simp)
    exact ⟨by omega, fun ⟨p, q⟩ => pin ⟨by omega, by omega⟩⟩

open Logkeeper.Protocol (Append ChargeClass Credit Debit Decision)

private def debitOf (raw : ChargeClass × Nat × Nat) : Debit :=
  ⟨raw.1, raw.2.2 - raw.2.1⟩

theorem link_recordCredit (raw : ChargeClass × Nat × Nat) (ordered : raw.2.1 ≤ raw.2.2) :
    recordCredit raw = let c := Credit.addDebit ⟨0, 0⟩ (debitOf raw); (c.ordinary, c.maintenance) := by
  rcases raw with ⟨lane, start, stop⟩
  change start ≤ stop at ordered
  have nonnegative : 0 ≤ (stop : Int) - (start : Int) := by omega
  cases lane <;> simp [recordCredit, asNatural_of_nonneg _ nonnegative, debitOf, Credit.addDebit] <;> omega

private theorem credit_on_queue {R : Type} [Nonempty R]
    (book : PartialMap R (ChargeClass × Nat × Nat)) (project : R → Append)
    (records : List R) (count : Nat)
    (same : ∀ r ∈ records, ∃ raw, book r = some raw ∧ raw.2.1 ≤ raw.2.2 ∧ (project r).debit = debitOf raw) :
    trimCredit records count book =
      (Logkeeper.Protocol.creditFor .ordinary ((records.take count).map project),
       Logkeeper.Protocol.creditFor .maintenance ((records.take count).map project)) := by
  induction count generalizing records with
  | zero => simp [trimCredit, Logkeeper.Protocol.creditFor]
  | succ count ih =>
    cases records with
    | nil => simp [trimCredit, Logkeeper.Protocol.creditFor]
    | cons head tail =>
      obtain ⟨raw, row, ordered, charge⟩ := same head (by simp)
      have tailSame : ∀ r ∈ tail, ∃ raw, book r = some raw ∧ raw.2.1 ≤ raw.2.2 ∧ (project r).debit = debitOf raw :=
        fun r mem => same r (by simp [mem])
      rw [trimCredit]
      have smaller : asNatural (((count + 1 : Nat) : Int) - 1) = count := by
        rw [asNatural_of_nonneg _ (by omega)]
        omega
      simp only [List.length_cons, Nat.succ_ne_zero, or_self, ite_false, List.drop_succ_cons, List.drop_zero,
        smaller, List.take_succ_cons, List.map_cons]
      rw [ih tail tailSame]
      simp only [seqIndex, Int.le_refl, ite_true, Int.toNat_zero, List.getElem?_cons_zero,
        Option.getD_some, mapIndex, row, link_recordCredit raw ordered, Logkeeper.Protocol.creditFor,
        List.map_cons, List.sum_cons, charge]
      cases lane : raw.1 <;> simp [debitOf, Credit.addDebit, lane]

theorem link_trimCredit {R : Type} [Nonempty R] (book : PartialMap R (ChargeClass × Nat × Nat))
    (project : R → Append) (records : List R) (decisions : List Decision) (floor through : Nat)
    (projection : records.map project = (Logkeeper.Protocol.application decisions).drop floor)
    (same : ∀ r ∈ records, ∃ raw, book r = some raw ∧ raw.2.1 ≤ raw.2.2 ∧ (project r).debit = debitOf raw) :
    trimCredit records (through - floor) book =
      let c := Logkeeper.Protocol.trimCredit decisions floor through
      (c.ordinary, c.maintenance) := by
  rw [credit_on_queue book project records _ same, Logkeeper.Protocol.trim_credit_matches_removed_records]
  rw [List.map_take, projection]

end ordered_trim


namespace ordered_checkpoint
theorem link_matches_preparation {C : Type} [Nonempty C] (prepared published : C) :
    matches_preparation prepared published ↔ Logkeeper.OrderedCheckpoint.matches_preparation prepared published := by
  rfl

theorem link_next_revision (current offered : Nat) :
    next_revision current offered ↔ Logkeeper.OrderedCheckpoint.next_revision current offered := by
  unfold next_revision Logkeeper.OrderedCheckpoint.next_revision
  omega

theorem link_may_close (source held : Bool) :
    may_close source held ↔ Logkeeper.OrderedCheckpoint.may_close source held := by
  cases source <;> cases held <;> simp [may_close, Logkeeper.OrderedCheckpoint.may_close]

theorem link_may_acquire (above retained closed : Bool) :
    may_acquire above retained closed ↔ Logkeeper.OrderedCheckpoint.may_acquire above retained closed := by
  cases closed <;> simp [may_acquire, Logkeeper.OrderedCheckpoint.may_acquire, and_assoc]
end ordered_checkpoint

namespace ordered_cohort
theorem link_accept_quorum (accepted members : Nat) :
    accept_quorum accepted members ↔ Logkeeper.OrderedCohort.accept_quorum accepted members := by
  unfold accept_quorum Logkeeper.OrderedCohort.accept_quorum
  omega

theorem link_has_paid_repair_quorum (paid quorum : Nat) :
    has_paid_repair_quorum paid quorum ↔ Logkeeper.OrderedCohort.has_paid_repair_quorum paid quorum := by
  simp [has_paid_repair_quorum, Logkeeper.OrderedCohort.has_paid_repair_quorum]

theorem link_may_extend {G : Type} [Nonempty G] (successor : Option G) :
    may_extend successor ↔ Logkeeper.OrderedCohort.may_extend successor := by
  cases successor <;> simp [may_extend, Logkeeper.OrderedCohort.may_extend]

theorem link_matches_chosen_seal (successor : Option (List UInt8)) (destination : List UInt8) :
    matches_chosen_seal successor destination ↔ Logkeeper.OrderedCohort.matches_chosen_seal successor destination := by
  cases successor <;> simp [matches_chosen_seal, Logkeeper.OrderedCohort.matches_chosen_seal]
end ordered_cohort

namespace ordered_receipt
theorem link_original_placement_matches {P : Type} [Nonempty P] (original installed : P) :
    original_placement_matches original installed ↔ Logkeeper.Protocol.Ordered.original_placement_matches original installed := by
  rfl

theorem link_fresh_request_expired (position expiry : Nat) :
    fresh_request_expired position expiry ↔ Logkeeper.Protocol.Ordered.fresh_request_expired position expiry := by
  simp [fresh_request_expired, Logkeeper.Protocol.Ordered.fresh_request_expired]
end ordered_receipt

namespace ordered_writer
theorem link_is_current_enrollment {E : Type} [Nonempty E] (installed : Option E) (presented : E) :
    is_current_enrollment installed presented ↔ Logkeeper.Kernel.Ordered.is_current_enrollment installed presented := by
  rfl
end ordered_writer


namespace mirrored_voter_media

open Logkeeper.SelectionFence (Image)
open Logkeeper.PrefixAgreement (ballotRank ballot_rank_order)

private def rank (ballot : Ballot) : Nat := ballotRank ballot.round ballot.nonce

theorem link_ballot_le (a b : Ballot) (ha : a.nonce < 2^128) (hb : b.nonce < 2^128) :
    ballot_le a b ↔ ballotRank a.round a.nonce ≤ ballotRank b.round b.nonce := by
  have strict := ballot_rank_order (a := b.round) (b := a.round) hb ha
  unfold ballot_le
  omega

private def promiseRank (p : Option Ballot) : Nat :=
  match p with
  | none => 0
  | some b => rank b + 1

private def boundedBallot (b : Ballot) : Prop := b.nonce < 2^128
private def boundedPromise (p : Option Ballot) : Prop := ∀ b, p = some b → boundedBallot b

theorem link_promise_le (a b : Option Ballot) (ha : boundedPromise a) (hb : boundedPromise b) :
    promise_le a b ↔ promiseRank a ≤ promiseRank b := by
  cases a with
  | none => cases b <;> simp [promise_le, promiseRank]
  | some a =>
    cases b with
    | none => simp [promise_le, promiseRank]
    | some b => simpa [promise_le, promiseRank, rank] using link_ballot_le a b (ha a rfl) (hb b rfl)

private def boundedState (s : VoterState) : Prop :=
  boundedPromise s.promised ∧ ∀ b len, s.accepted = some (b, len) → boundedBallot b

private def projectImage (s : VoterState) : Image Unit :=
  ⟨promiseRank s.promised, s.accepted.map fun (b, size) => ⟨rank b, List.replicate size ()⟩⟩

private theorem rank_eq (a b : Ballot) (ha : boundedBallot a) (hb : boundedBallot b) :
    rank a = rank b ↔ a = b := by
  constructor
  · intro h
    have lower := (link_ballot_le a b ha hb).mpr (Nat.le_of_eq h)
    have upper := (link_ballot_le b a hb ha).mpr (Nat.le_of_eq h.symm)
    unfold ballot_le at lower upper
    have round : a.round = b.round := by omega
    have nonce : a.nonce = b.nonce := by omega
    cases a <;> cases b <;> simp_all
  · exact congrArg rank

theorem link_dominates (later earlier : VoterState)
    (hl : boundedState later) (he : boundedState earlier) :
    dominates later earlier ↔ (projectImage later).Dominates (projectImage earlier) := by
  unfold dominates Logkeeper.SelectionFence.Image.Dominates
  rw [link_promise_le earlier.promised later.promised he.1 hl.1]
  cases eh : earlier.accepted with
  | none => simp [projectImage, eh, promiseRank]
  | some prior =>
    obtain ⟨a, n⟩ := prior
    cases lh : later.accepted with
    | none => simp [projectImage, eh, lh, promiseRank]
    | some next =>
      obtain ⟨b, m⟩ := next
      have ranks : ballotRank a.round a.nonce = ballotRank b.round b.nonce ↔ a = b :=
        rank_eq a b (he.2 a n eh) (hl.2 b m lh)
      simp [projectImage, eh, lh, Logkeeper.PrefixAgreement.RankLE,
        link_ballot_le a b (he.2 a n eh) (hl.2 b m lh), ranks, rank]

theorem link_keeps (floor : VoterState) (a b : Option VoterState)
    (hf : boundedState floor)
    (ha : ∀ image, a = some image → boundedState image)
    (hb : ∀ image, b = some image → boundedState image) :
    keeps floor [a, b] ↔
      Logkeeper.SelectionFence.Keeps (projectImage floor) (fun slot => (if slot then b else a).map projectImage) := by
  have atA : seqIndex [a, b] 0 = a := by simp [seqIndex]
  have atB : seqIndex [a, b] 1 = b := by simp [seqIndex]
  unfold keeps Logkeeper.SelectionFence.Keeps
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, true_and]
  constructor
  · intro stable slot selected eq
    cases slot
    · cases h : a with
      | none => simp [h] at eq
      | some image =>
        have eq' : projectImage image = selected := by simpa [h] using eq
        subst selected
        have atZero := stable 0
        rw [atA, h] at atZero
        exact (link_dominates image floor (ha image h) hf).mp (by
          simpa [optionSome, optionValue] using atZero)
    · cases h : b with
      | none => simp [h] at eq
      | some image =>
        have eq' : projectImage image = selected := by simpa [h] using eq
        subst selected
        have atOne := stable 1
        rw [atB, h] at atOne
        exact (link_dominates image floor (hb image h) hf).mp (by
          simpa [optionSome, optionValue] using atOne)
  · intro stable i ⟨⟨lower, upper⟩, present⟩
    have index : i = 0 ∨ i = 1 := by omega
    rcases index with rfl | rfl
    · rw [atA] at present ⊢
      cases h : a with
      | none => simp [h, optionSome] at present
      | some image =>
        simpa [optionValue] using
          (link_dominates image floor (ha image h) hf).mpr (stable false _ (by simp [h]))
    · rw [atB] at present ⊢
      cases h : b with
      | none => simp [h, optionSome] at present
      | some image =>
        simpa [optionValue] using
          (link_dominates image floor (hb image h) hf).mpr (stable true _ (by simp [h]))

end mirrored_voter_media

namespace receipt_signatures

open Logkeeper.Premises.BarrierKeys (KeyRoster)

-- The Rust active roster is keyed by voter. Lean observes its values as a list.
theorem link_verificationKeys (rust : ReceiptKeys) (active : List Fingerprint)
    (membership : ∀ key, mapValues rust.active key ↔ key ∈ active) (key : Fingerprint) :
    verificationKeys rust key ↔
      key ∈ Logkeeper.Premises.BarrierKeys.verificationKeys ⟨active, rust.predecessor, rust.retained⟩ := by
  simp [verificationKeys, Logkeeper.Premises.BarrierKeys.verificationKeys, setUnion, seqSet, membership, or_assoc]

theorem link_repairAuthority (rust : ReceiptKeys) (active : List Fingerprint) (key : Fingerprint) :
    repairAuthority rust key ↔
      Logkeeper.Premises.BarrierKeys.repairAuthority ⟨active, rust.predecessor, rust.retained⟩ key := by
  rfl

theorem link_validSuccessorKeys (source target : ReceiptKeys) (oldKeys newKeys : List Fingerprint)
    (sourceKeys : ∀ key, mapValues source.active key ↔ key ∈ oldKeys)
    (targetKeys : ∀ key, mapValues target.active key ↔ key ∈ newKeys) :
    validSuccessorKeys source target ↔ Logkeeper.Premises.BarrierKeys.validSuccessorKeys
      ⟨oldKeys, source.predecessor, source.retained⟩ ⟨newKeys, target.predecessor, target.retained⟩ := by
  simp [validSuccessorKeys, Logkeeper.Premises.BarrierKeys.validSuccessorKeys,
    setSubset, seqSet, sourceKeys, link_verificationKeys source oldKeys sourceKeys,
    link_verificationKeys target newKeys targetKeys]

end receipt_signatures


namespace prefix_agreement
open Logkeeper.PrefixAgreement (ballotRank ballot_rank_order)

theorem link_ballot_lt (left right : Nat × Nat) (hl : left.2 < 2^128) (hr : right.2 < 2^128) :
    ballot_lt left right ↔ ballotRank left.1 left.2 < ballotRank right.1 right.2 := by
  exact (ballot_rank_order hl hr).symm
end prefix_agreement

namespace voter_slot_header
theorem link_voterSlotMagic : voterSlotMagic.map UInt8.toBitVec = Logkeeper.VoterSlotHeader.voterSlotMagic := by
  rfl
end voter_slot_header

namespace voter_transport
theorem link_transportMagic : transportMagic.map UInt8.toBitVec = Logkeeper.VoterTransport.transportMagic := by
  rfl

theorem link_transportGroupMatches (group authorized installed : List UInt8) :
    transportGroupMatches group authorized installed ↔
      Logkeeper.VoterTransport.transportGroupMatches (group.map UInt8.toBitVec)
        (authorized.map UInt8.toBitVec) (installed.map UInt8.toBitVec) := by
  have eq (a b : List UInt8) : a.map UInt8.toBitVec = b.map UInt8.toBitVec ↔ a = b := by
    constructor
    · intro h
      have reversed := congrArg (List.map UInt8.ofBitVec) h
      simpa [List.map_map, Function.comp_def] using reversed
    · rintro rfl
      rfl
  simp only [transportGroupMatches, Logkeeper.VoterTransport.transportGroupMatches, eq]

theorem link_responseKind (kind expected : UInt8) :
    responseKind kind expected = Logkeeper.VoterTransport.responseKind kind.toBitVec expected.toBitVec := by
  simp [responseKind, Logkeeper.VoterTransport.responseKind, ← UInt8.toBitVec_inj]
end voter_transport


namespace rotation_slot_evidence
open Logkeeper.SelectionFence (SlotRead SlotDescriptor)
open Logkeeper.PrefixAgreement (ballotRank)

theorem link_distinct_voters (rows : List VoterSlots) :
    distinct_voters rows ↔ (rows.map VoterSlots.voter).Nodup := by
  unfold distinct_voters
  simp only [and_assoc, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact indexed_pairs rows (fun a b => a.voter ≠ b.voter)

-- This projects the coordinates attested by the authenticated vote. The
-- connection to the two visits and their descriptors is the media proof.
private def attestedRead (vote : Vote) (descriptor : SlotDescriptor Fingerprint) :
    SlotRead Fingerprint Fingerprint :=
  ⟨descriptor, ballotRank vote.ballot.round vote.ballot.nonce,
    ballotRank vote.ballot.round vote.ballot.nonce, vote.digest⟩

theorem link_at_fence (vote : Vote) (ballot : Ballot) (prefixDigest : Fingerprint)
    (descriptor : SlotDescriptor Fingerprint)
    (observedFits : vote.ballot.nonce < 2^128) (expectedFits : ballot.nonce < 2^128) :
    at_fence vote ballot prefixDigest ↔ vote.readBack = true ∧
      Logkeeper.SelectionFence.AtFence ⟨ballotRank ballot.round ballot.nonce, prefixDigest⟩
        (attestedRead vote descriptor) := by
  have ranks : ballotRank vote.ballot.round vote.ballot.nonce = ballotRank ballot.round ballot.nonce ↔
      vote.ballot = ballot := mirrored_voter_media.rank_eq _ _ observedFits expectedFits
  simp [at_fence, Logkeeper.SelectionFence.AtFence, attestedRead, ranks, and_assoc, and_left_comm, and_comm]

end rotation_slot_evidence

namespace object_name_codec
theorem link_zeroName : zeroName = Logkeeper.CompactImage.zeroName := by
  rfl
end object_name_codec


namespace ordered_lease_reducer

private theorem intervalSpan (interval : ReadInterval) :
    ((interval.through : Int) - (interval.floor : Int) ≤ (interval.retained : Int)) ↔
      interval.through - interval.floor ≤ interval.retained := by
  omega

theorem link_interval_available (interval : ReadInterval) :
    interval_available interval ↔ DisposalLease.interval_available interval.empty interval.floor
      interval.first interval.through interval.retained = true := by
  simp [interval_available, DisposalLease.interval_available, intervalSpan, and_assoc]

theorem link_read_lease_end {E H : Type} [Nonempty E] [Nonempty H] [DecidableEq E] [DecidableEq H]
    (enrolled principal : Option E) (owner : E) (stored : Option H) (requested : H)
    (interval : ReadInterval) (checkpoint : CheckpointAccess) (now duration : Nat) :
    read_lease_end enrolled principal owner stored requested interval checkpoint now duration =
      DisposalLease.read_lease_end enrolled principal owner stored requested
        (DisposalLease.interval_available interval.empty interval.floor interval.first interval.through interval.retained)
        (DisposalLease.checkpoint_open checkpoint.erasureFloor checkpoint.cut checkpoint.retained checkpoint.closed)
        now duration (2 ^ 64 - 1) := by
  have limit : ((now : Int) + (duration : Int) ≤ ((18446744073709551615 : Nat) : Int)) ↔
      now + duration ≤ (2 : Nat) ^ 64 - 1 := by omega
  unfold read_lease_end DisposalLease.read_lease_end DisposalLease.checkpoint_open
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, ← link_interval_available, interval_available,
    limit]
  have closed : ((!checkpoint.closed) = true) ↔ ¬ checkpoint.closed = true := by
    cases checkpoint.closed <;> decide
  simp only [closed]
  split
  · rename_i admitted
    rw [← Int.natCast_add, clipUnsigned_nat]
    have fits := admitted.2.2.2.2.2.2.2
    omega
  · rfl

end ordered_lease_reducer

namespace stream_keeper

open StreamJournal

theorem link_live {P : Type} (k : Keeper P) (created : k.created = true) :
    live k.deleted ↔ k.live := by
  simp [live, Keeper.live, created]

-- Model epoch zero is the initial sentinel. Real epochs, including wire epoch
-- zero, are shifted by one in the model.
theorem link_may_seal {P : Type} (k : Keeper P) (promise : Option Nat)
    (epoch holder : Nat) (projected : k.promised = (promise.map (· + 1)).getD 0) :
    may_seal promise.isSome (promise.getD 0) epoch (decide (k.identity = holder)) ↔
      SealAllowed k (epoch + 1) holder := by
  cases promise <;> simp [may_seal, SealAllowed, projected]

theorem link_preserves_head {P : Type} [DecidableEq P] (k : Keeper P) (next : History P) (start : Nat)
    (enough : k.head ≤ next.length) (unchanged : next.take (start - 1) = k.history.take (start - 1)) :
    preserves_head start k.head (decide
      (next.take k.head = k.history.take k.head)) ↔ SameCommitted k next := by
  simp only [preserves_head, decide_eq_true_eq, SameCommitted, enough, true_and]
  constructor
  · rintro (beyond | same)
    · have h : k.head ≤ start - 1 := by omega
      have cut := congrArg (List.take k.head) unchanged
      simpa [List.take_take, Nat.min_eq_left h] using cut
    · exact same
  · exact Or.inr

theorem link_may_append {P : Type} (k : Keeper P) (epoch : Nat) :
    may_append (decide (k.promised = epoch)) (decide (k.synced = epoch)) ↔ MayAppend k epoch := by
  simp [may_append, MayAppend, Synced]

theorem link_may_trim {P : Type} (k : Keeper P) (epoch through : Nat) (synced : Synced k epoch) :
    may_trim through k.head ↔ MayTrim k epoch through := by
  simp [may_trim, MayTrim, synced]

theorem link_checked_tail {P : Type} (k : Keeper P) (requested : Nat) :
    checked_tail k.tail requested = (check k).tail := rfl

theorem link_read_head {P : Type} (k : Keeper P) (start max : Nat) (page : Page P)
    (returned : readPage k start max = some page) :
    read_head k.head k.tail = page.head := by
  unfold readPage at returned
  split at returned
  · contradiction
  · cases returned
    rfl

theorem link_tombstone {P : Type} (k : Keeper P) (deleting : Bool) :
    tombstone k.deleted deleting ↔ (deleteKeeper k deleting).deleted = true := by
  cases deleting <;> simp [tombstone, deleteKeeper]

theorem link_append_retry {P : Type} [DecidableEq P] (history : History P)
    (floor holder epoch lsn : Nat) (payload : P) (retained : floor ≤ lsn) (old : lsn ≤ history.length) :
    append_retry true lsn history.length (decide (history[lsn - 1]? = some ⟨epoch, payload⟩)) ↔
      appendAt history floor holder epoch holder epoch lsn payload = .retry := by
  have notNext : lsn ≠ history.length + 1 := by omega
  simp [append_retry, appendAt, retained, Nat.not_lt_of_ge retained, old, notNext]

theorem link_may_read {P : Type} (k : Keeper P) (start max : Nat) :
    may_read k.floor start ↔ (readPage k start max).isSome = true := by
  simp only [may_read, readPage]
  split <;> simp_all <;> omega

end stream_keeper

namespace stream_writer

open StreamJournal PrefixAgreement JournalRefinement

theorem link_covers {P : Type} (vote : Option (PrefixAgreement.Vote (Record P))) (epoch : Nat) (history : History P)
    (issued : ∀ v ∈ vote, history <+: v.history ∨ v.history <+: history) :
    covers (vote.map (fun v => (v.ballot, v.history.length))) epoch history.length ↔
      ∃ v ∈ vote, Covers v epoch history := by
  cases vote with
  | none => simp [covers]
  | some v =>
    change (v.ballot = epoch ∧ history.length ≤ v.history.length) ↔
      ∃ other ∈ some v, (other.ballot = epoch ∧ history <+: other.history)
    simp only [Option.mem_def, Option.some.injEq]
    constructor
    · rintro ⟨sameEpoch, bound⟩
      refine ⟨v, rfl, sameEpoch, ?_⟩
      rcases issued v (by simp) with forward | reverse
      · exact forward
      · exact (reverse.eq_of_length_le bound) ▸ List.prefix_rfl
    · rintro ⟨other, rfl, sameEpoch, contained⟩
      exact ⟨sameEpoch, contained.length_le⟩

private def slotCovers (ack : Option (Nat × Nat)) (epoch atLsn : Nat) : Prop :=
  ∃ last, ack = some (epoch, last) ∧ atLsn ≤ last

theorem link_acknowledged {P : Type} (keepers : KeeperId → Keeper P)
    (acks : KeeperId → Option (Nat × Nat)) (epoch : Nat) (history : History P)
    (observed : ∀ k, slotCovers (acks k) epoch history.length ↔
      ∃ held, (keepers k).durable.votes ⟨epoch, held⟩ ∧ history <+: held) :
    acknowledged (acks 0) (acks 1) (acks 2) epoch history.length ↔
      QuorumAccepted keepers epoch history := by
  classical
  let votes : KeeperId → Bool := fun k => decide (slotCovers (acks k) epoch history.length)
  have eligible k : votes k = true ↔ slotCovers (acks k) epoch history.length := by simp [votes]
  have count : Majority ensemble votes ↔
      (votes 0 = true ∧ votes 1 = true) ∨ (votes 0 = true ∧ votes 2 = true) ∨
        (votes 1 = true ∧ votes 2 = true) := by
    unfold Majority ensemble
    cases h0 : votes 0 <;> cases h1 : votes 1 <;> cases h2 : votes 2 <;>
      simp [List.countP_cons, h0, h1, h2]
  have slots : acknowledged (acks 0) (acks 1) (acks 2) epoch history.length ↔ Majority ensemble votes := by
    simp only [count, eligible]
    rcases acks 0 with _ | ⟨_, _⟩ <;>
      rcases acks 1 with _ | ⟨_, _⟩ <;>
      rcases acks 2 with _ | ⟨_, _⟩ <;>
      simp [acknowledged, slotCovers, or_assoc, and_assoc]
  rw [slots]
  constructor
  · exact fun majority => ⟨votes, majority, fun k _ ack => (observed k).mp ((eligible k).mp ack)⟩
  · rintro ⟨other, majority, holds⟩
    have includes : ∀ k ∈ ensemble, other k = true → votes k = true :=
      fun k present yes => (eligible k).mpr ((observed k).mpr (holds k present yes))
    have bound : ensemble.countP other ≤ ensemble.countP votes := List.countP_mono_left includes
    unfold Majority at *
    omega

private def rankVote {P : Type} (synced : Option Nat) (history : History P) : PrefixAgreement.Vote (Record P) :=
  ⟨(synced.map (· + 1)).getD 0, history⟩

theorem link_outranks {P : Type} (left right : Option Nat) (old new : History P) :
    outranks left old.length right new.length ↔ ¬ RecoveryLE (rankVote right new) (rankVote left old) := by
  cases left <;> cases right <;> simp [outranks, RecoveryLE, recoveryEpoch, rankVote] <;> omega

theorem link_matches_epoch (checked : Option Nat) (expected : Nat) :
    matches_epoch checked expected ↔ StreamWriter.MatchesEpoch checked expected := by
  cases checked <;> simp [matches_epoch, StreamWriter.MatchesEpoch, optionSome]

theorem link_can_sync_from (floor head start : Nat) (matched : Bool) :
    can_sync_from floor head start matched ↔ StreamWriter.SyncStart floor head start matched := by
  simp [can_sync_from, StreamWriter.SyncStart, and_assoc]

theorem link_append_head (head last : Nat) :
    append_head head last = StreamWriter.AppendHead head last := by
  simp only [append_head, StreamWriter.AppendHead]
  split <;> omega

theorem link_accepted_tail (tail issued last : Nat) :
    accepted_tail tail issued last = StreamWriter.AcceptedTail tail issued last := by
  simp only [accepted_tail, StreamWriter.AcceptedTail]
  by_cases belowIssued : issued < last
  · rw [ite_eq_left belowIssued, Nat.max_eq_right (by omega)]
  · rw [ite_eq_right belowIssued]
    by_cases belowTail : tail < last
    · rw [ite_eq_left belowTail, Nat.max_eq_right (by omega)]
    · rw [ite_eq_right belowTail]
      split <;> omega

theorem link_fresh_sample (opened sent : Nat) :
    fresh_sample opened sent ↔ StreamHead.FreshSample opened sent := by
  simp [fresh_sample, StreamHead.FreshSample]

theorem link_sample_index (a b : Nat) :
    sample_index a b = StreamHead.SampleIndex a b := by
  simp only [sample_index, StreamHead.SampleIndex]
  split <;> omega

theorem link_eligible_sample (promised synced highest : Option Nat) (same : Bool) :
    eligible_sample promised synced highest same ↔
      StreamHead.EligibleSample promised synced highest same := by
  simp [eligible_sample, StreamHead.EligibleSample, and_assoc]

theorem link_head_quorum (count : Nat) :
    head_quorum count ↔ StreamHead.HeadQuorum count := by
  simp [head_quorum, StreamHead.HeadQuorum]

theorem head_quorum_is_majority (covered : KeeperId → Bool) :
    head_quorum (ensemble.countP covered) ↔ Majority ensemble covered := by
  rw [link_head_quorum]
  unfold StreamHead.HeadQuorum Majority
  have size : ensemble.length = 3 := rfl
  omega

/-- The generated recovery-start decision supplies the writer's agreement premise. -/
theorem recovery_start_agrees {P : Type} {s : StreamIO.State P}
    (reached : StreamIO.Reachable s) (keeper : KeeperId)
    {epoch floor start : Nat} {matched : Bool}
    (unstaged : (s.keeper keeper).staging = none)
    (allowed : can_sync_from floor (s.keeper keeper).head start matched)
    (observed : matched = true → ∃ a b : Record P, 1 < start ∧
      (s.keeper keeper).history[start - 2]? = some a ∧
      (s.writer.seed epoch)[start - 2]? = some b ∧ matches_epoch (some a.epoch) b.epoch) :
    StreamIO.Agrees (s.keeper keeper) epoch (s.writer.seed epoch) floor start := by
  apply StreamWriter.recovery_agrees reached keeper unstaged ((link_can_sync_from ..).mp allowed)
  intro compared
  obtain ⟨target, seed, positive, targetAt, seedAt, same⟩ := observed compared
  exact ⟨target, seed, positive, targetAt, seedAt, (link_matches_epoch ..).mp same⟩

theorem recovery_fallback_record {P : Type} {w : Writer P} {left right : History P}
    (leftOrigins : StreamWriter.Origins w left) (rightOrigins : StreamWriter.Origins w right)
    {i : Nat} {a b : Record P} (leftAt : left[i]? = some a)
    (rightAt : right[i]? = some b) (same : matches_epoch (some a.epoch) b.epoch) :
    a = b :=
  StreamWriter.recovery_record leftOrigins rightOrigins leftAt rightAt ((link_matches_epoch ..).mp same)

theorem append_head_sendable {P : Type} {w : Writer P} {keeper : Keeper P}
    {identity epoch start head : Nat} {payloads : List P}
    (elected : StreamIO.Elected w epoch identity)
    (within : start - 1 + payloads.length ≤ (w.issued epoch).length)
    (assigned : stamp epoch payloads = ((w.issued epoch).drop (start - 1)).take payloads.length)
    (certified : w.advertised ((w.issued epoch).take (append_head head (start - 1 + payloads.length)))) :
    StreamIO.Sendable w keeper identity (.append epoch start payloads (append_head head (start - 1 + payloads.length))) := by
  rw [link_append_head] at certified ⊢
  exact StreamWriter.sendable_append elected within assigned certified

theorem reused_sample_is_fresh (opened sent received : Nat) (eligible : fresh_sample opened sent)
    (inFlight : sent ≤ received) : opened ≤ received :=
  Nat.le_trans (Nat.le_of_lt ((link_fresh_sample ..).mp eligible)) inFlight

theorem sample_index_covers_both (a b : Nat) : a ≤ sample_index a b ∧ b ≤ sample_index a b := by
  rw [link_sample_index]
  exact StreamHead.sample_bounds a b

end stream_writer

end Logkeeper.Generated
