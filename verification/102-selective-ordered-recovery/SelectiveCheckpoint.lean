import SelectiveOrderedRecovery
import DeliveryRecovery

set_option warningAsError true

namespace SelectiveCheckpoint

open EnvelopeCodec (Bytes Field wordBytes wordLimit readWord takeField)
open SelectiveReadWindow (Window)

variable {horizon : Nat}

def bitmapBytes (horizon : Nat) : Nat :=
  (horizon + 7) / 8

def bitmap (window : Window horizon) : BitVec horizon :=
  (BitVec.ofBoolListLE (List.ofFn window.bits)).cast List.length_ofFn

theorem the_packed_bitmap_keeps_each_exact_slot (window : Window horizon) (slot : Fin horizon) :
    (bitmap window).getLsbD slot.val = window.bits slot := by
  have within : slot.val < (List.ofFn window.bits).length := by simp
  rw [bitmap, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem within]
  simp

private theorem bitmap_fits_its_wire (window : Window horizon) :
    (bitmap window).toNat < wordLimit (bitmapBytes horizon) := by
  have enough : horizon ≤ 8 * bitmapBytes horizon := by unfold bitmapBytes; omega
  have bytePower : wordLimit (bitmapBytes horizon) = 2 ^ (8 * bitmapBytes horizon) := by
    unfold wordLimit
    rw [Nat.pow_mul]
  rw [bytePower]
  exact Nat.lt_of_lt_of_le (bitmap window).isLt (Nat.pow_le_pow_right (by decide) enough)

def encode (bytes : Nat) (window : Window horizon) : Bytes :=
  wordBytes bytes window.floor ++ wordBytes (bitmapBytes horizon) (bitmap window).toNat

def decode (bytes horizon : Nat) (wire : Bytes) : Option (Window horizon) := do
  let (floor, rest) ← takeField bytes wire
  let (bits, tail) ← takeField (bitmapBytes horizon) rest
  let packed := readWord bits.val
  if tail = [] ∧ packed < 2 ^ horizon then
    some ⟨readWord floor.val, fun slot => (BitVec.ofNat horizon packed).getLsbD slot.val⟩
  else none

theorem the_window_has_a_fixed_bit_packed_checkpoint_size (bytes : Nat) (window : Window horizon) :
    (encode bytes window).length = bytes + bitmapBytes horizon := by
  simp [encode, EnvelopeCodec.wordBytes_length]

theorem decode_the_exact_packed_window (bytes : Nat) (window : Window horizon) (fits : window.floor < wordLimit bytes) :
    decode bytes horizon (encode bytes window) = some window := by
  have fitsMask := bitmap_fits_its_wire window
  have mask := (bitmap window).isLt
  let floor := EnvelopeCodec.word bytes window.floor
  let flags := EnvelopeCodec.word (bitmapBytes horizon) (bitmap window).toNat
  have first := EnvelopeCodec.takeField_on_encoded_word floor flags.val
  have second : takeField (bitmapBytes horizon) flags.val = some (flags, []) := by
    simpa using EnvelopeCodec.takeField_on_encoded_word flags []
  change decode bytes horizon (floor.val ++ flags.val) = some window
  unfold decode
  rw [first]
  change (takeField (bitmapBytes horizon) flags.val).bind (fun (field, tail) =>
    if tail = [] ∧ readWord field.val < 2 ^ horizon then
      some ⟨readWord floor.val, fun slot => (BitVec.ofNat horizon (readWord field.val)).getLsbD slot.val⟩
    else none) = some window
  rw [second]
  change (if ([] : Bytes) = [] ∧ readWord flags.val < 2 ^ horizon then
    some ⟨readWord floor.val, fun slot => (BitVec.ofNat horizon (readWord flags.val)).getLsbD slot.val⟩
    else none) = some window
  have floorExact : readWord floor.val = window.floor := EnvelopeCodec.fixed_width_words_roundtrip fits
  have flagsExact : readWord flags.val = (bitmap window).toNat := EnvelopeCodec.fixed_width_words_roundtrip fitsMask
  rw [floorExact, flagsExact, ite_eq_left ⟨rfl, mask⟩]
  have bits : BitVec.ofNat horizon (bitmap window).toNat = bitmap window := by simp
  rw [bits]
  congr 1
  exact Window.mk.injEq _ _ _ _ |>.mpr ⟨rfl, funext (the_packed_bitmap_keeps_each_exact_slot window)⟩

theorem a_successful_decode_rejects_padding_and_has_no_other_wire (bytes : Nat) (wire : Bytes)
    (window : Window horizon) (accepted : decode bytes horizon wire = some window) :
    encode bytes window = wire := by
  cases first : takeField bytes wire with
  | none => simp [decode, first] at accepted
  | some found =>
    obtain ⟨floor, rest⟩ := found
    cases second : takeField (bitmapBytes horizon) rest with
    | none => simp [decode, first, second] at accepted
    | some found =>
      obtain ⟨bits, tail⟩ := found
      by_cases valid : tail = [] ∧ readWord bits.val < 2 ^ horizon
      · have image : (⟨readWord floor.val, fun slot =>
              (BitVec.ofNat horizon (readWord bits.val)).getLsbD slot.val⟩ : Window horizon) = window := by
          simpa [decode, first, second, valid] using accepted
        have packed : bitmap window = BitVec.ofNat horizon (readWord bits.val) := by
          apply BitVec.eq_of_getLsbD_eq
          intro index within
          rw [the_packed_bitmap_keeps_each_exact_slot window ⟨index, within⟩]
          exact congrFun (congrArg Window.bits image.symm) ⟨index, within⟩
        have value : (bitmap window).toNat = readWord bits.val := by
          rw [packed, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valid.2]
        obtain ⟨empty, _⟩ := valid
        have firstWord : wordBytes bytes window.floor = floor.val := by
          rw [← image]
          exact congrArg Subtype.val (EnvelopeCodec.readField_recovers_the_exact_word floor)
        have secondWord : wordBytes (bitmapBytes horizon) (bitmap window).toNat = bits.val := by
          rw [value]
          exact congrArg Subtype.val (EnvelopeCodec.readField_recovers_the_exact_word bits)
        rw [encode, firstWord, secondWord, ← EnvelopeCodec.takeField_consumes_the_exact_bytes first,
          ← EnvelopeCodec.takeField_consumes_the_exact_bytes second, empty, List.append_nil]
      · simp [decode, first, second, valid] at accepted

open RetainedDelivery (Rules)
open SelectiveOrderedRecovery (Image attach)

variable {bytes slots capacity limit : Nat} {Payload Ticket : Type}

structure Control (bytes slots capacity limit : Nat) (Payload : Type) where
  ordered : JointReadRecovery.Control capacity slots Payload
  delivery : DeliveryBook.Section (width := bytes) limit
  window : Bytes

abbrev Catalog (bytes slots capacity limit : Nat) (Payload : Type) :=
  EnvelopeRecovery.Catalog bytes (Control bytes slots capacity limit Payload) (FundedAppend.Source slots Payload)

def project (catalog : Catalog bytes slots capacity limit Payload) :
    DeliveryRecovery.Catalog bytes slots capacity limit Payload :=
  ⟨fun name => (catalog.control name).map (fun control =>
    ⟨⟨control.ordered, control.window.take bytes⟩, control.delivery⟩),
    catalog.data, catalog.manifests, catalog.retained⟩

def Ready (bytes : Nat) (window : Window horizon) : Prop :=
  (¬ SelectiveReadWindow.Spent window (window.floor + 1)) ∧
    ∀ nonce, SelectiveReadWindow.Spent window nonce → nonce < wordLimit bytes

noncomputable def openCheckpoint (rules : Rules bytes slots capacity limit Payload Ticket)
    (catalog : Catalog bytes slots capacity limit Payload) (authenticate : Bytes → Prop)
    (anchor : EnvelopeRecovery.Anchor bytes) (coreNeeds : Field bytes → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field bytes → Prop)
    (deliveryNeeds : DeliveryBook.Entry capacity → Field bytes → Prop) (wire : Bytes) :
    Option (Image horizon slots capacity limit Payload) := by
  classical
  exact do
    let (_, contents) ← EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire
    let window ← decode bytes horizon contents.control.window
    if Ready bytes window then
      let body ← DeliveryRecovery.openCheckpoint rules (project catalog) authenticate anchor coreNeeds readNeeds deliveryNeeds wire
      some (attach body window)
    else none

theorem a_named_open_uses_its_own_exact_ready_window
    (rules : Rules bytes slots capacity limit Payload Ticket)
    (catalog : Catalog bytes slots capacity limit Payload) (authenticate : Bytes → Prop)
    (anchor : EnvelopeRecovery.Anchor bytes) (coreNeeds : Field bytes → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field bytes → Prop)
    (deliveryNeeds : DeliveryBook.Entry capacity → Field bytes → Prop) (wire : Bytes)
    (image : Image horizon slots capacity limit Payload)
    (opened : openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire = some image) :
    ∃ header contents, EnvelopeRecovery.Opened catalog authenticate anchor coreNeeds wire header contents ∧
      contents.control.window = encode bytes image.window ∧ Ready bytes image.window ∧
      image.body.ordered.readThrough = image.window.floor := by
  cases named : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire with
  | none => simp [openCheckpoint, named] at opened
  | some result =>
    obtain ⟨header, contents⟩ := result
    cases decoded : decode bytes horizon contents.control.window with
    | none => simp [openCheckpoint, named, decoded] at opened
    | some window =>
      by_cases ready : Ready bytes window
      · cases exposed : DeliveryRecovery.openCheckpoint rules (project catalog) authenticate anchor coreNeeds
            readNeeds deliveryNeeds wire with
        | none => simp [openCheckpoint, named, exposed] at opened
        | some body =>
          have combined : attach body window = image := by
            simpa [openCheckpoint, named, decoded, ready, exposed] using opened
          subst image
          exact ⟨header, contents, EnvelopeRecovery.a_successful_open_has_all_authentication_and_custody_checks named,
            (a_successful_decode_rejects_padding_and_has_no_other_wire bytes _ window decoded).symm, ready, rfl⟩
      · simp [openCheckpoint, named, decoded, ready] at opened

#print axioms the_packed_bitmap_keeps_each_exact_slot
#print axioms the_window_has_a_fixed_bit_packed_checkpoint_size
#print axioms decode_the_exact_packed_window
#print axioms a_successful_decode_rejects_padding_and_has_no_other_wire
#print axioms a_named_open_uses_its_own_exact_ready_window

end SelectiveCheckpoint
