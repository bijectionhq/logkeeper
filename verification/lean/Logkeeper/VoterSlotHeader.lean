import Std.Tactic.BVDecide

namespace Logkeeper.VoterSlotHeader

abbrev Byte := BitVec 8
abbrev Word := BitVec 64
abbrev Bytes := List Byte

def voterSlotMagic : Bytes := [76, 75, 79, 82, 86, 48, 48, 53]

def encodeBE (value : Word) : Bytes :=
  [value.extractLsb' 56 8, value.extractLsb' 48 8, value.extractLsb' 40 8,
   value.extractLsb' 32 8, value.extractLsb' 24 8, value.extractLsb' 16 8,
   value.extractLsb' 8 8, value.extractLsb' 0 8]

def decodeBE (bytes : Bytes) : Word :=
  bytes[0]! ++ bytes[1]! ++ bytes[2]! ++ bytes[3]! ++
  bytes[4]! ++ bytes[5]! ++ bytes[6]! ++ bytes[7]!

theorem big_endian_round_trips (value : Word) : decodeBE (encodeBE value) = value := by
  simp [encodeBE, decodeBE]
  bv_decide

def slotDescriptor (group voter : Bytes) (generation length : Word) : Bytes :=
  voterSlotMagic ++ group ++ voter ++ encodeBE generation ++ encodeBE length

structure SlotHeader where
  magic : Bytes
  group : Bytes
  voter : Bytes
  generation : Word
  length : Word
  digest : Bytes
  deriving DecidableEq

def slotHeaderLengthValid (bytes : Bytes) (limit : Nat) : Prop :=
  bytes.length = 104 ∧
    2 ≤ (decodeBE ((bytes.drop 64).take 8)).toNat ∧
    (decodeBE ((bytes.drop 64).take 8)).toNat ≤ limit

def decodeHeader (bytes : Bytes) (limit : Nat) : Option SlotHeader :=
  if bytes.length = 104 then
    let length := decodeBE ((bytes.drop 64).take 8)
    if 2 ≤ length.toNat ∧ length.toNat ≤ limit then
      some ⟨bytes.take 8, (bytes.drop 8).take 32, (bytes.drop 40).take 16,
            decodeBE ((bytes.drop 56).take 8), length, bytes.drop 72⟩
    else none
  else none

def slotHeaderMatches (header : SlotHeader) (group voter : Bytes) : Prop :=
  header.magic = voterSlotMagic ∧ header.group = group ∧ header.voter = voter ∧
    header.generation ≠ 0

theorem voter_slot_header_rejects_inexact_extent (bytes : Bytes) (limit : Nat)
    (wrong : bytes.length ≠ 104) : decodeHeader bytes limit = none := by
  simp [decodeHeader, wrong]

theorem voter_slot_scope_is_exact (bytes group voter : Bytes) (limit : Nat) (header : SlotHeader)
    (decoded : decodeHeader bytes limit = some header) :
    slotHeaderMatches header group voter ↔
      bytes.take 8 = voterSlotMagic ∧ (bytes.drop 8).take 32 = group ∧
      (bytes.drop 40).take 16 = voter ∧ decodeBE ((bytes.drop 56).take 8) ≠ 0 := by
  unfold decodeHeader at decoded
  split at decoded <;> try contradiction
  dsimp only at decoded
  split at decoded <;> try contradiction
  cases decoded
  rfl

private theorem take_field (earlier field suffix : Bytes) (offset width : Nat)
    (before : earlier.length = offset) (inside : field.length = width) :
    ((earlier ++ field ++ suffix).drop offset).take width = field := by
  subst offset
  subst width
  rw [List.append_assoc, List.drop_left, List.take_left]

theorem voter_slot_header_round_trips (group voter digest : Bytes) (generation length : Word)
    (limit : Nat) (g : group.length = 32) (v : voter.length = 16) (d : digest.length = 32)
    (bounds : 2 ≤ length.toNat ∧ length.toNat ≤ limit) :
    decodeHeader (slotDescriptor group voter generation length ++ digest) limit =
      some ⟨voterSlotMagic, group, voter, generation, length, digest⟩ := by
  have magic : voterSlotMagic.length = 8 := rfl
  have enc (word : Word) : (encodeBE word).length = 8 := rfl
  have extent : (slotDescriptor group voter generation length ++ digest).length = 104 := by
    simp [slotDescriptor, g, v, d, magic, enc]
  have takeMagic :
      (slotDescriptor group voter generation length ++ digest).take 8 = voterSlotMagic := by
    simpa [slotDescriptor, List.append_assoc] using
      (take_field [] voterSlotMagic (group ++ voter ++ encodeBE generation ++ encodeBE length ++ digest)
        0 8 rfl magic)
  have takeGroup :
      ((slotDescriptor group voter generation length ++ digest).drop 8).take 32 = group := by
    simpa [slotDescriptor, List.append_assoc] using
      (take_field voterSlotMagic group (voter ++ encodeBE generation ++ encodeBE length ++ digest) 8 32 magic g)
  have takeVoter :
      ((slotDescriptor group voter generation length ++ digest).drop 40).take 16 = voter := by
    simpa [slotDescriptor, List.append_assoc] using
      (take_field (voterSlotMagic ++ group) voter (encodeBE generation ++ encodeBE length ++ digest)
        40 16 (by simp [magic, g]) v)
  have takeGeneration :
      ((slotDescriptor group voter generation length ++ digest).drop 56).take 8 = encodeBE generation := by
    simpa [slotDescriptor, List.append_assoc] using
      (take_field (voterSlotMagic ++ group ++ voter) (encodeBE generation) (encodeBE length ++ digest)
        56 8 (by simp [magic, g, v]) (enc generation))
  have takeLength :
      ((slotDescriptor group voter generation length ++ digest).drop 64).take 8 = encodeBE length := by
    simpa [slotDescriptor, List.append_assoc] using
      (take_field (voterSlotMagic ++ group ++ voter ++ encodeBE generation) (encodeBE length) digest
        64 8 (by simp [magic, g, v, enc]) (enc length))
  have takeDigest : (slotDescriptor group voter generation length ++ digest).drop 72 = digest := by
    have width : (slotDescriptor group voter generation length).length = 72 := by
      simp [slotDescriptor, magic, g, v, enc]
    rw [← width, List.drop_left]
  simp [decodeHeader, extent, takeMagic, takeGroup, takeVoter, takeGeneration, takeLength,
    takeDigest, big_endian_round_trips, bounds]

#print axioms big_endian_round_trips
#print axioms voter_slot_header_rejects_inexact_extent
#print axioms voter_slot_scope_is_exact
#print axioms voter_slot_header_round_trips

end Logkeeper.VoterSlotHeader
