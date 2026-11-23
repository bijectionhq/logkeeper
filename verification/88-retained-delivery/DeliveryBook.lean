import OrderedReadReplay

set_option warningAsError true

namespace DeliveryBook

open RTDBFailover (Invocation Route Barrier)
open ChosenReplay (Lineage)
open RecoverableRead (Permit)
open SnapshotAdmission (Basis)
open EnvelopeCodec (Bytes Field word wordLimit readWord wordBytes)
open SourceOutcomes (Key)

variable {width limit capacity : Nat} {Signature : Type}

structure Entry (capacity : Nat) where
  serial : Nat
  orderedAt : Nat
  permit : Permit capacity
  root : Nat
  start : Nat
  borrow : PoolState.Identity
  reply : Barrier

def Entry.basis (row : Entry capacity) : Basis :=
  ⟨row.root, row.start, row.reply.cut⟩

def Entry.request (row : Entry capacity) : OrderedReadReplay.Delivery capacity :=
  ⟨row.reply.invocation, row.permit, row.basis⟩

structure Book (limit capacity : Nat) where
  issued : Nat
  rows : Fin limit → Option (Entry capacity)

def empty : Book limit capacity := ⟨0, fun _ => none⟩

def atKey (book : Book limit capacity) (key : Key limit) : Option (Entry capacity) :=
  (book.rows key.slot).filter (fun row => row.serial == key.serial)

def insert (book : Book limit capacity) (key : Key limit) (row : Entry capacity) : Book limit capacity :=
  ⟨key.serial, JointSource.setCell book.rows key.slot (some row)⟩

def clear (book : Book limit capacity) (key : Key limit) : Book limit capacity :=
  {book with rows := JointSource.setCell book.rows key.slot none}

def Entry.words (row : Entry capacity) : List Nat :=
  [row.serial, row.orderedAt, row.permit.slot.val, row.permit.serial,
   row.root, row.start, row.borrow.pool, row.borrow.serial]

def Entry.Fits (width : Nat) (row : Entry capacity) : Prop :=
  (∀ value ∈ row.words, value < wordLimit width) ∧ AppliedBarrierReceipt.Fits width row.reply

def Book.Valid (width : Nat) (book : Book limit capacity) : Prop :=
  book.issued < wordLimit width ∧ ∀ slot row, book.rows slot = some row →
    0 < row.serial ∧ row.serial ≤ book.issued ∧ row.Fits width

def MayInsert (width : Nat) (book : Book limit capacity) (key : Key limit) (row : Entry capacity) : Prop :=
  key.serial = book.issued + 1 ∧ row.serial = key.serial ∧ book.rows key.slot = none ∧ row.Fits width

theorem an_exact_insert_keeps_the_bounded_book_well_formed
    (book : Book limit capacity) (key : Key limit) (row : Entry capacity)
    (valid : book.Valid width) (allowed : MayInsert width book key row) :
    (insert book key row).Valid width ∧ atKey (insert book key row) key = some row := by
  obtain ⟨next, serial, _, fits⟩ := allowed
  have newFits := fits.1 row.serial (by simp [Entry.words])
  have counterFits : (insert book key row).issued < wordLimit width := by
    change key.serial < wordLimit width
    simpa [← serial] using newFits
  refine ⟨⟨counterFits, ?_⟩, ?_⟩
  · intro slot entry found
    by_cases same : slot = key.slot
    · subst slot
      have equal : row = entry := by simpa [insert, JointSource.setCell] using found
      subst entry
      exact ⟨by omega, Nat.le_of_eq serial, fits⟩
    · have earlier : book.rows slot = some entry := by simpa [insert, JointSource.setCell, same] using found
      obtain ⟨positive, below, bounded⟩ := valid.2 slot entry earlier
      exact ⟨positive, Nat.le_trans below (by change book.issued ≤ key.serial; omega), bounded⟩
  · simp [atKey, insert, JointSource.setCell, serial]

theorem exact_release_keeps_the_issuance_frontier_and_other_rows
    (book : Book limit capacity) (key : Key limit) (valid : book.Valid width) :
    (clear book key).Valid width ∧ (clear book key).issued = book.issued ∧
    atKey (clear book key) key = none ∧
    ∀ other : Key limit, other.slot ≠ key.slot → atKey (clear book key) other = atKey book other := by
  refine ⟨⟨valid.1, ?_⟩, rfl, by simp [atKey, clear, JointSource.setCell], ?_⟩
  · intro slot row found
    by_cases same : slot = key.slot
    · simp [clear, JointSource.setCell, same] at found
    · exact valid.2 slot row (by simpa [clear, JointSource.setCell, same] using found)
  · intro other different
    simp [atKey, clear, JointSource.setCell, different]

theorem an_old_obligation_cannot_use_a_recycled_slot
    (book : Book limit capacity) (old : Key limit) (entry : Entry capacity)
    (found : book.rows old.slot = some entry) (different : old.serial ≠ entry.serial) :
    atKey book old = none := by
  simp [atKey, found, different.symm]

def encodeRow (width : Nat) (row : Entry capacity) : Bytes :=
  EnvelopeCodec.flattenFields (row.words.map (word width)) ++ AppliedBarrierReceipt.encode width row.reply

def reconstruct (capacity : Nat) (words : List Nat) (reply : Barrier) : Option (Entry capacity) :=
  match words with
  | [serial, ordered, slot, permitSerial, root, start, pool, borrow] =>
      if fits : slot < capacity then some ⟨serial, ordered, ⟨⟨slot, fits⟩, permitSerial⟩, root, start, ⟨pool, borrow⟩, reply⟩
      else none
  | _ => none

def decodeRow (width capacity : Nat) (wire : Bytes) : Option (Entry capacity) := do
  let front ← EnvelopeCodec.readFields width 8 (wire.take (8 * width))
  let reply ← AppliedBarrierReceipt.decode width (wire.drop (8 * width))
  reconstruct capacity (front.map (fun field => readWord field.val)) reply

theorem each_representable_delivery_row_is_exactly_one_fixed_size_body
    (row : Entry capacity) (positive : 0 < width) (fits : row.Fits width) :
    decodeRow width capacity (encodeRow width row) = some row ∧ (encodeRow width row).length = 1 + 17 * width := by
  let front := EnvelopeCodec.flattenFields (row.words.map (word width))
  let body := AppliedBarrierReceipt.encode width row.reply
  have preSize : front.length = 8 * width := by
    simp [front, EnvelopeCodec.flattenFields_size, Entry.words]
  have readPrefix : EnvelopeCodec.readFields width 8 front = some (row.words.map (word width)) := by
    simpa [front, Entry.words] using EnvelopeCodec.readFields_after_flatten (row.words.map (word width))
  have readWords : (row.words.map (word width)).map (fun field => readWord field.val) = row.words := by
    rw [List.map_map]
    refine Eq.trans ?_ (List.map_id _)
    apply List.map_congr_left
    intro item present
    exact EnvelopeCodec.fixed_width_words_roundtrip (fits.1 item present)
  have parsed : AppliedBarrierReceipt.decode width body = some row.reply :=
    AppliedBarrierReceipt.a_representable_reply_round_trips row.reply positive fits.2
  constructor
  · have same : reconstruct capacity row.words row.reply = some row := by
      rcases row with ⟨serial, ordered, ⟨⟨slot, inRange⟩, permitSerial⟩, root, start, ⟨pool, borrow⟩, reply⟩
      simp [reconstruct, Entry.words, inRange]
    change decodeRow width capacity (front ++ body) = some row
    have takeFront : (front ++ body).take (8 * width) = front := by
      rw [← preSize]
      simp
    have dropFront : (front ++ body).drop (8 * width) = body := by
      rw [← preSize]
      simp
    simp only [decodeRow, takeFront, dropFront, readPrefix, parsed]
    change reconstruct capacity ((row.words.map (word width)).map (fun field => readWord field.val)) row.reply = some row
    rw [readWords]
    exact same
  · change (front ++ body).length = 1 + 17 * width
    rw [List.length_append, preSize, AppliedBarrierReceipt.an_encoded_reply_has_constant_length]
    omega

structure Section (limit : Nat) where
  issued : Field width
  rows : Fin limit → Option Bytes

def capture (width : Nat) (book : Book limit capacity) : Section (width := width) limit :=
  ⟨word width book.issued, fun slot => (book.rows slot).map (encodeRow width)⟩

def decodeBook (saved : Section (width := width) limit) : Book limit capacity :=
  ⟨readWord saved.issued.val, fun slot => (saved.rows slot).bind (decodeRow width capacity)⟩

noncomputable def openSection (saved : Section (width := width) limit) : Option (Book limit capacity) := by
  classical
  exact if (∀ slot bytes, saved.rows slot = some bytes → (decodeRow width capacity bytes).isSome = true) ∧
      (decodeBook saved : Book limit capacity).Valid width then some (decodeBook saved)
  else none

theorem the_bounded_delivery_book_reopens_from_its_exact_section
    (book : Book limit capacity) (positive : 0 < width) (valid : book.Valid width) :
    openSection (capture width book) = some book := by
  have exactSlot (slot : Fin limit) (entry : Entry capacity) (found : book.rows slot = some entry) :
      decodeRow width capacity (encodeRow width entry) = some entry :=
    (each_representable_delivery_row_is_exactly_one_fixed_size_body entry positive (valid.2 slot entry found).2.2).1
  have exactBook : decodeBook (capacity := capacity) (capture width book) = book := by
    rcases book with ⟨issued, rows⟩
    have counter : readWord (word width issued).val = issued := EnvelopeCodec.fixed_width_words_roundtrip valid.1
    have table : (fun slot => ((rows slot).map (encodeRow width)).bind (decodeRow width capacity)) = rows := by
      funext slot
      cases found : rows slot with
      | none => simp
      | some entry => simp [exactSlot slot entry found]
    change (⟨readWord (word width issued).val,
      fun slot => ((rows slot).map (encodeRow width)).bind (decodeRow width capacity)⟩ : Book limit capacity) =
      ⟨issued, rows⟩
    rw [counter, table]
  have complete : ∀ slot bytes, (capture width book).rows slot = some bytes → (decodeRow width capacity bytes).isSome = true := by
    intro slot bytes encoded
    cases found : book.rows slot with
    | none => simp [capture, found] at encoded
    | some entry =>
        have equal : encodeRow width entry = bytes := by simpa [capture, found] using encoded
        simp [← equal, exactSlot slot entry found]
  have sound : (decodeBook (capacity := capacity) (capture width book)).Valid width := exactBook.symm ▸ valid
  rw [openSection, ite_eq_left ⟨complete, sound⟩, exactBook]

def cellSize : Option Bytes → Nat
  | none => 1
  | some wire => 1 + wire.length

theorem every_encoded_slot_fits_one_tag_and_one_bounded_row
    (book : Book limit capacity) (positive : 0 < width) (valid : book.Valid width) (slot : Fin limit) :
    cellSize ((capture width book).rows slot) ≤ 2 + 17 * width := by
  cases found : book.rows slot with
  | none => simp [cellSize, capture, found]; omega
  | some row =>
      have count := (each_representable_delivery_row_is_exactly_one_fixed_size_body row positive (valid.2 slot row found).2.2).2
      simp [cellSize, capture, found, count]; omega

theorem a_framed_book_fits_one_counter_and_its_fixed_number_of_cells
    (book : Book limit capacity) (positive : 0 < width) (valid : book.Valid width) :
    (capture width book).issued.val.length +
      ((List.finRange limit).map (fun slot => cellSize ((capture width book).rows slot))).sum
      ≤ width + limit * (2 + 17 * width) := by
  have cap (slots : List (Fin limit)) :
      (slots.map (fun slot => cellSize ((capture width book).rows slot))).sum ≤ slots.length * (2 + 17 * width) := by
    induction slots with
    | nil => simp
    | cons slot rest smaller =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        have eachBound := every_encoded_slot_fits_one_tag_and_one_bounded_row book positive valid slot
        omega
  simpa only [(capture width book).issued.property, List.length_finRange] using Nat.add_le_add_left (cap (List.finRange limit)) width

end DeliveryBook
