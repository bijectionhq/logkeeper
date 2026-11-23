import Std

set_option warningAsError true

namespace EnvelopeCodec

abbrev Bytes := List UInt8
abbrev Field (width : Nat) := {raw : Bytes // raw.length = width}

def wordLimit (width : Nat) : Nat := 256 ^ width

def wordBytes : Nat → Nat → Bytes
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: wordBytes width (value / 256)

def readWord : Bytes → Nat
  | [] => 0
  | byte :: tail => byte.toNat + 256 * readWord tail

theorem wordBytes_length (width value : Nat) : (wordBytes width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width prior => simp [wordBytes, prior]

def word (width value : Nat) : Field width := ⟨wordBytes width value, wordBytes_length width value⟩

theorem fixed_width_words_roundtrip {width value : Nat} (bounded : value < wordLimit width) :
    readWord (wordBytes width value) = value := by
  induction width generalizing value with
  | zero =>
      have zero : value = 0 := by simpa [wordLimit] using bounded
      simp [wordBytes, readWord, zero]
  | succ width prior =>
      have fit : value / 256 < wordLimit width := by
        apply Nat.div_lt_of_lt_mul
        simpa [wordLimit, Nat.pow_succ, Nat.mul_comm] using bounded
      simp only [wordBytes, readWord, UInt8.toNat_ofNat', prior fit]
      exact Nat.mod_add_div value 256

theorem wordBytes_after_readWord (raw : Bytes) :
    wordBytes raw.length (readWord raw) = raw := by
  induction raw with
  | nil => rfl
  | cons byte tail prior =>
      have small : byte.toNat < 256 := byte.toNat_lt
      have low : (byte.toNat + 256 * readWord tail) % 256 = byte.toNat := by omega
      have high : (byte.toNat + 256 * readWord tail) / 256 = readWord tail := by omega
      simp only [List.length_cons, wordBytes, readWord, high, prior]
      congr 1
      apply UInt8.toNat.inj
      rw [UInt8.toNat_ofNat', low]

theorem readField_recovers_the_exact_word {width : Nat} (field : Field width) :
    word width (readWord field.val) = field := by
  apply Subtype.ext
  have exactWord := wordBytes_after_readWord field.val
  rw [field.property] at exactWord
  exact exactWord

def takeField (width : Nat) (wire : Bytes) : Option (Field width × Bytes) :=
  if fits : width ≤ wire.length then
    some (⟨wire.take width, by simp [List.length_take, Nat.min_eq_left fits]⟩, wire.drop width)
  else none

theorem takeField_on_encoded_word {width : Nat} (word : Field width) (tail : Bytes) :
    takeField width (word.val ++ tail) = some (word, tail) := by
  obtain ⟨raw, size⟩ := word
  subst width
  simp [takeField]

theorem takeField_consumes_the_exact_bytes {width : Nat} {wire tail : Bytes} {word : Field width}
    (parsed : takeField width wire = some (word, tail)) : word.val ++ tail = wire := by
  unfold takeField at parsed
  split at parsed
  · cases parsed
    exact List.take_append_drop _ _
  · simp at parsed

def flattenFields {width : Nat} : List (Field width) → Bytes
  | [] => []
  | word :: remaining => word.val ++ flattenFields remaining

def atEnd (wire : Bytes) : Bool :=
  wire.isEmpty

theorem a_finished_record_has_no_leftover_bytes {wire : Bytes} (finished : atEnd wire = true) :
    wire = [] := by
  simpa [atEnd] using finished

def readFields (width : Nat) : Nat → Bytes → Option (List (Field width))
  | 0, wire => if atEnd wire then some [] else none
  | count + 1, wire => do
      let (word, tail) ← takeField width wire
      let rest ← readFields width count tail
      pure (word :: rest)

theorem readFields_after_flatten {width : Nat} (words : List (Field width)) :
    readFields width words.length (flattenFields words) = some words := by
  induction words with
  | nil => simp [readFields, atEnd, flattenFields]
  | cons word rest prior =>
      simp [readFields, flattenFields, takeField_on_encoded_word, prior]

theorem readFields_recovers_the_exact_wire {width count : Nat}
    {wire : Bytes} {words : List (Field width)} (parsed : readFields width count wire = some words) :
    flattenFields words = wire := by
  induction count generalizing wire words with
  | zero =>
      simp only [readFields] at parsed
      split at parsed
      next complete =>
        cases parsed
        exact (a_finished_record_has_no_leftover_bytes complete).symm
      next => simp at parsed
  | succ count prior =>
      cases took : takeField width wire with
      | none => simp [readFields, took] at parsed
      | some result =>
          obtain ⟨word, tail⟩ := result
          cases rest : readFields width count tail with
          | none => simp [readFields, took, rest] at parsed
          | some later =>
              simp [readFields, took, rest] at parsed
              subst words
              simp only [flattenFields, prior rest]
              exact takeField_consumes_the_exact_bytes took

theorem flattenFields_size {width : Nat} (words : List (Field width)) :
    (flattenFields words).length = words.length * width := by
  induction words with
  | nil => simp [flattenFields]
  | cons word rest prior =>
      simp only [flattenFields, List.length_append, word.property, prior, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

structure Envelope (width : Nat) where
  format : UInt8
  lineage : Field width
  position : Field width
  dataEnd : Field width
  prefixCommitment : Field width
  control : Field width
  data : Field width
  evidence : Field width

def fields (header : Envelope width) : List (Field width) :=
  [header.lineage, header.position, header.dataEnd, header.prefixCommitment, header.control, header.data, header.evidence]

def assemble (format : UInt8) : List (Field width) → Option (Envelope width)
  | [lineage, position, dataEnd, cut, control, data, evidence] =>
      some ⟨format, lineage, position, dataEnd, cut, control, data, evidence⟩
  | _ => none

theorem assemble_preserves_fields {format : UInt8} {words : List (Field width)} {header : Envelope width}
    (success : assemble format words = some header) : header.format = format ∧ fields header = words := by
  unfold assemble at success
  split at success
  · cases success
    exact ⟨rfl, rfl⟩
  · simp at success

def domainTag : UInt8 := 1

def encode (header : Envelope width) : Bytes :=
  domainTag :: header.format :: flattenFields (fields header)

def decode (width : Nat) : Bytes → Option (Envelope width)
  | tag :: format :: raw =>
      if tag = domainTag then (readFields width 7 raw).bind (assemble format) else none
  | _ => none

theorem decode_encode (header : Envelope width) : decode width (encode header) = some header := by
  have read := readFields_after_flatten (fields header)
  change readFields width 7 (flattenFields (fields header)) = some (fields header) at read
  simp only [encode, decode, read]
  cases header
  rfl

theorem accepted_envelope_has_one_canonical_encoding {wire : Bytes} {header : Envelope width}
    (accepted : decode width wire = some header) : encode header = wire := by
  cases wire with
  | nil => simp [decode] at accepted
  | cons tag remaining =>
      cases remaining with
      | nil => simp [decode] at accepted
      | cons format raw =>
          simp only [decode] at accepted
          split at accepted
          next correctTag =>
            cases parsed : readFields width 7 raw with
            | none => simp [parsed] at accepted
            | some words =>
                have built : assemble format words = some header := by simpa [parsed] using accepted
                obtain ⟨exactFormat, exactFields⟩ := assemble_preserves_fields built
                simp [encode, correctTag, exactFormat, exactFields, readFields_recovers_the_exact_wire parsed]
          next => simp at accepted

theorem encoded_envelope_size (header : Envelope width) : (encode header).length = 2 + 7 * width := by
  simp [encode, flattenFields_size, fields] <;> omega

theorem one_wire_image_identifies_one_envelope (first second : Envelope width)
    (same : encode first = encode second) : first = second := by
  have decoded := congrArg (decode width) same
  simpa only [decode_encode, Option.some.injEq] using decoded

#print axioms takeField_on_encoded_word
#print axioms takeField_consumes_the_exact_bytes
#print axioms a_finished_record_has_no_leftover_bytes
#print axioms readFields_after_flatten
#print axioms readFields_recovers_the_exact_wire
#print axioms flattenFields_size
#print axioms assemble_preserves_fields
#print axioms decode_encode
#print axioms accepted_envelope_has_one_canonical_encoding
#print axioms encoded_envelope_size
#print axioms one_wire_image_identifies_one_envelope

end EnvelopeCodec
