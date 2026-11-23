import EnvelopeRecovery
import RealizedSource

set_option warningAsError true

namespace SealBody

open EnvelopeCodec (Bytes Field flattenFields readFields)

variable {width slots : Nat}

structure Header (width : Nat) where
  stream : Field width
  incarnation : Field width
  slot : Field width
  serial : Field width
  sealPosition : Field width
  group : Field width
  generation : Field width

def Header.words (header : Header width) : List (Field width) :=
  [header.stream, header.incarnation, header.slot, header.serial, header.sealPosition, header.group, header.generation]

structure Extent (width : Nat) where
  pool : Field width
  serial : Field width
  key : Field width
  binding : Field width
  bytes : Field width

def Extent.words (extent : Extent width) : List (Field width) :=
  [extent.pool, extent.serial, extent.key, extent.binding, extent.bytes]

def readExtents : List (Field width) → Option (List (Extent width))
  | [] => some []
  | pool :: serial :: key :: binding :: bytes :: remaining =>
      (readExtents remaining).map (⟨pool, serial, key, binding, bytes⟩ :: ·)
  | _ => none

private theorem extents_round_trip (extents : List (Extent width)) :
    readExtents (extents.flatMap Extent.words) = some extents := by
  induction extents with
  | nil => rfl
  | cons extent rest prior =>
      simp [Extent.words, readExtents, prior]

private theorem exact_extent_words {words : List (Field width)} {extents : List (Extent width)}
    (decoded : readExtents words = some extents) : extents.flatMap Extent.words = words := by
  induction words using readExtents.induct generalizing extents with
  | case1 =>
      cases decoded
      rfl
  | case2 pool serial key binding bytes rest prior =>
      cases read : readExtents rest with
      | none => simp [readExtents, read] at decoded
      | some found =>
          simp [readExtents, read] at decoded
          subst extents
          simp [Extent.words, prior read]
  | case3 _ _ =>
      simp [readExtents] at decoded

structure Body (width : Nat) where
  header : Header width
  append : Extent width
  recovery : List (Extent width)

def Body.words (body : Body width) : List (Field width) :=
  body.header.words ++ (body.append :: body.recovery).flatMap Extent.words

def readBody : List (Field width) → Option (Body width)
  | stream :: incarnation :: slot :: serial :: position :: group :: generation :: remaining => do
      let append :: recovery ← readExtents remaining | none
      pure ⟨⟨stream, incarnation, slot, serial, position, group, generation⟩, append, recovery⟩
  | _ => none

private theorem body_round_trip (body : Body width) : readBody body.words = some body := by
  cases body with
  | mk header append recovery =>
      have parsed : readExtents (append.words ++ recovery.flatMap Extent.words) = some (append :: recovery) :=
        extents_round_trip (append :: recovery)
      rcases header with ⟨stream, incarnation, slot, serial, position, group, generation⟩
      simp [Body.words, Header.words, readBody, parsed]

private theorem exact_body_words {words : List (Field width)} {body : Body width}
    (decoded : readBody words = some body) : body.words = words := by
  fun_cases readBody words with
  | case1 stream incarnation slot serial position group generation remaining =>
      cases extents : readExtents remaining with
      | none => simp [readBody, extents] at decoded
      | some items =>
          cases items with
          | nil => simp [readBody, extents] at decoded
          | cons append recovery =>
              simp [readBody, extents] at decoded
              subst body
              simp [Body.words, Header.words, exact_extent_words extents]
  | case2 _ => simp_all [readBody]

private theorem body_word_count (body : Body width) : body.words.length = 7 + 5 * (body.recovery.length + 1) := by
  have items (extents : List (Extent width)) : (extents.flatMap Extent.words).length = 5 * extents.length := by
    induction extents with
    | nil => rfl
    | cons head tail prior =>
        simp only [List.flatMap_cons, List.length_append, prior, Extent.words, List.length_cons, List.length_nil]
        omega
  simp only [Body.words, List.length_append, items, Header.words, List.length_cons, List.length_nil]

def domain : UInt8 := 2

def encode (body : Body width) : Bytes := domain :: flattenFields body.words

def decode (width maxRecovery : Nat) (wire : Bytes) : Option (Body width) :=
  match wire with
  | tag :: raw => do
    if tag = domain ∧ 0 < width ∧ raw.length ≤ (7 + 5 * (maxRecovery + 1)) * width then
      let words ← readFields width (raw.length / width) raw
      readBody words
    else none
  | [] => none

theorem accepted_bytes_recover_the_exact_bounded_body
    {maxRecovery : Nat} {wire : Bytes} {body : Body width}
    (accepted : decode width maxRecovery wire = some body) :
    encode body = wire ∧ body.recovery.length ≤ maxRecovery := by
  cases wire with
  | nil => simp [decode] at accepted
  | cons tag raw =>
      simp only [decode] at accepted
      split at accepted
      next wellFormed =>
        cases parsed : readFields width (raw.length / width) raw with
        | none => simp [parsed] at accepted
        | some words =>
          have assembled : readBody words = some body := by simpa [parsed] using accepted
          have original : flattenFields body.words = raw :=
            (congrArg flattenFields (exact_body_words assembled)).trans
              (EnvelopeCodec.readFields_recovers_the_exact_wire parsed)
          have lengthExact := congrArg List.length original
          rw [EnvelopeCodec.flattenFields_size, body_word_count] at lengthExact
          have size : (7 + 5 * (body.recovery.length + 1)) * width ≤ (7 + 5 * (maxRecovery + 1)) * width :=
            lengthExact.symm ▸ wellFormed.2.2
          have amount := Nat.le_of_mul_le_mul_right size wellFormed.2.1
          refine ⟨?_, by omega⟩
          rw [encode, wellFormed.1, original]
      next => simp at accepted

theorem a_valid_body_round_trips (body : Body width) (maxRecovery : Nat)
    (widthPositive : 0 < width) (bounded : body.recovery.length ≤ maxRecovery) :
    decode width maxRecovery (encode body) = some body := by
  have count : (flattenFields body.words).length / width = body.words.length := by
    rw [EnvelopeCodec.flattenFields_size]
    exact Nat.mul_div_cancel _ widthPositive
  have limit : (flattenFields body.words).length ≤ (7 + 5 * (maxRecovery + 1)) * width := by
    rw [EnvelopeCodec.flattenFields_size, body_word_count]
    exact Nat.mul_le_mul_right width (by omega)
  simp [decode, encode, widthPositive, limit, count, EnvelopeCodec.readFields_after_flatten, body_round_trip]

theorem a_canonical_body_cannot_substitute_other_extents
    {first second : Body width} {maxRecovery : Nat} {wire : Bytes}
    (original : decode width maxRecovery wire = some first)
    (different : decode width maxRecovery wire = some second) :
    first.header = second.header ∧ first.append = second.append ∧ first.recovery = second.recovery := by
  have exact := Option.some.inj (original.symm.trans different)
  subst second
  exact ⟨rfl, rfl, rfl⟩

theorem bytes_cover_all_the_encoded_recovery_extents
    {maxRecovery : Nat} {wire : Bytes} {body : Body width}
    (accepted : decode width maxRecovery wire = some body) :
    wire.length ≤ 1 + (7 + 5 * (maxRecovery + 1)) * width := by
  obtain ⟨exact, cap⟩ := accepted_bytes_recover_the_exact_bounded_body accepted
  rw [← exact, encode, List.length_cons, EnvelopeCodec.flattenFields_size]
  rw [body_word_count]
  have bound := Nat.mul_le_mul_right width (show 7 + 5 * (body.recovery.length + 1) ≤
    7 + 5 * (maxRecovery + 1) by omega)
  simpa [Nat.add_comm] using Nat.add_le_add_right bound 1

structure Atoms (width : Nat) where
  number : Field width → Option Nat
  key : Field width → Option ChannelLifecycle.Key
  binding : Field width → Option RegistrationRecovery.Binding

def decodeExtent (atoms : Atoms width) (extent : Extent width) : Option AllocationVector.Receipt := do
  let pool ← atoms.number extent.pool
  let serial ← atoms.number extent.serial
  let key ← atoms.key extent.key
  let binding ← atoms.binding extent.binding
  let bytes ← atoms.number extent.bytes
  if pool = key.handle.custodian ∧ 0 < bytes then
    some ⟨⟨key, binding, bytes⟩, ⟨pool, serial⟩⟩
  else none

def decodeRecord (atoms : Atoms width) (slots : Nat) (body : Body width) : Option (RealizedSource.Record slots) := do
  let stream ← atoms.number body.header.stream
  let incarnation ← atoms.number body.header.incarnation
  let slot ← atoms.number body.header.slot
  let serial ← atoms.number body.header.serial
  let position ← atoms.number body.header.sealPosition
  let group ← atoms.number body.header.group
  let generation ← atoms.number body.header.generation
  let append ← decodeExtent atoms body.append
  let recovery ← body.recovery.mapM (decodeExtent atoms)
  if within : slot < slots then
    let plan : AllocationVector.Plan slots := ⟨⟨⟨slot, within⟩, serial⟩, ⟨group, generation⟩,
      append.demand, recovery.map AllocationVector.Receipt.demand⟩
    some ⟨⟨stream, incarnation⟩, ⟨⟨plan.move, plan.intent, .committed⟩, position⟩, ⟨append, recovery⟩⟩
  else none

theorem opening_the_same_authenticated_body_recovers_the_same_realized_record
    (atoms : Atoms width) (slots maxRecovery : Nat)
    {catalog : EnvelopeRecovery.Catalog width Bytes Data} {authenticated : Bytes → Prop}
    {expected : EnvelopeRecovery.Anchor width} {needed : Field width → Prop}
    {wire : Bytes} {first second : EnvelopeCodec.Envelope width}
    {left right : EnvelopeRecovery.Contents width Bytes Data}
    (old : EnvelopeRecovery.Opened catalog authenticated expected needed wire first left)
    (loaded : EnvelopeRecovery.Opened catalog authenticated expected needed wire second right)
    {original recovered : RealizedSource.Record slots}
    (committed : (decode width maxRecovery left.control).bind (decodeRecord atoms slots) = some original)
    (reopened : (decode width maxRecovery right.control).bind (decodeRecord atoms slots) = some recovered) :
    recovered = original := by
  have body := (EnvelopeRecovery.identical_certified_bytes_cannot_open_a_different_body old loaded).2
  rw [← body, committed] at reopened
  exact (Option.some.inj reopened).symm

theorem an_opened_realization_keeps_its_required_evidence
    {catalog : EnvelopeRecovery.Catalog width Bytes Data} {authenticated : Bytes → Prop}
    {expected : EnvelopeRecovery.Anchor width} {needed : Field width → Prop} {wire : Bytes}
    {header : EnvelopeCodec.Envelope width} {contents : EnvelopeRecovery.Contents width Bytes Data}
    (opened : EnvelopeRecovery.Opened catalog authenticated expected needed wire header contents) :
    ∀ object, needed object → catalog.retained object :=
  EnvelopeRecovery.opened_checkpoint_covers_every_required_object opened

#print axioms accepted_bytes_recover_the_exact_bounded_body
#print axioms a_valid_body_round_trips
#print axioms a_canonical_body_cannot_substitute_other_extents
#print axioms bytes_cover_all_the_encoded_recovery_extents
#print axioms opening_the_same_authenticated_body_recovers_the_same_realized_record
#print axioms an_opened_realization_keeps_its_required_evidence

end SealBody
