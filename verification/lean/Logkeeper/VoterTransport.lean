import Logkeeper.VoterSlotHeader

namespace Logkeeper.VoterTransport

open Logkeeper.VoterSlotHeader (Byte Word Bytes decodeBE encodeBE big_endian_round_trips)

def transportMagic : Bytes := [76, 75, 79, 82, 80, 67, 48, 52]

def transportGroupMatches (group authorized installed : Bytes) : Prop :=
  group = authorized ∧ group = installed

inductive ResponseKind where
  | expected | deposed | rejected | invalid
  deriving DecidableEq

def responseKind (kind expected : Byte) : ResponseKind :=
  if kind = expected then .expected
  else if kind = 5 then .deposed
  else if kind = 6 then .rejected
  else .invalid

def ballotBytes (round : Word) (nonce : Bytes) : Bytes :=
  encodeBE round ++ nonce

def ballotValid (bytes : Bytes) : Prop :=
  bytes.length = 24 ∧ decodeBE (bytes.take 8) ≠ 0 ∧
    ∃ byte ∈ bytes.drop 8, byte ≠ 0

noncomputable def decodeBallot (bytes : Bytes) : Option (Word × Bytes) := by
  classical
  exact if ballotValid bytes then some (decodeBE (bytes.take 8), bytes.drop 8) else none

theorem transport_ballot_round_trips (round : Word) (nonce : Bytes)
    (nonceExtent : nonce.length = 16) (positive : round ≠ 0)
    (nonzero : ∃ byte ∈ nonce, byte ≠ 0) :
    decodeBallot (ballotBytes round nonce) = some (round, nonce) := by
  have width : (encodeBE round).length = 8 := rfl
  have takeRound : ((encodeBE round) ++ nonce).take 8 = encodeBE round := by
    rw [← width, List.take_left]
  have dropRound : ((encodeBE round) ++ nonce).drop 8 = nonce := by
    rw [← width, List.drop_left]
  simp [decodeBallot, ballotValid, ballotBytes, takeRound, dropRound, width, nonceExtent,
    big_endian_round_trips]
  exact ⟨positive, nonzero⟩

structure Image where
  generation : Word
  digest : Bytes
  deriving DecidableEq

structure VoteSlots where
  selected : Byte
  first : Image
  second : Image
  deriving DecidableEq

def voteSlotsMatch (bytes : Bytes) (slots : VoteSlots) : Prop :=
  bytes.length = 81 ∧ slots.selected = bytes[0]! ∧
  slots.first = ⟨decodeBE ((bytes.drop 1).take 8), (bytes.drop 9).take 32⟩ ∧
  slots.second = ⟨decodeBE ((bytes.drop 41).take 8), (bytes.drop 49).take 32⟩

def decodeVoteSlots (bytes : Bytes) : Option VoteSlots :=
  if bytes.length = 81 then
    some ⟨bytes[0]!,
          ⟨decodeBE ((bytes.drop 1).take 8), (bytes.drop 9).take 32⟩,
          ⟨decodeBE ((bytes.drop 41).take 8), (bytes.drop 49).take 32⟩⟩
  else none

theorem vote_reads_the_two_physical_slots_in_order (bytes : Bytes) (slots : VoteSlots)
    (decoded : decodeVoteSlots bytes = some slots) : voteSlotsMatch bytes slots := by
  unfold decodeVoteSlots at decoded
  split at decoded <;> try contradiction
  cases decoded
  simp [voteSlotsMatch, *]

theorem scope_requires_both_groups (group authorized installed : Bytes)
    (accepted : transportGroupMatches group authorized installed) :
    group = authorized ∧ group = installed := by
  exact accepted

def voteReadBackMatches (tag : Byte) (requested : Bool) : Prop :=
  tag = if requested then 1 else 0

theorem a_reply_cannot_change_witness_mode (tag : Byte) (requested : Bool)
    (accepted : voteReadBackMatches tag requested) :
    (requested = true ∧ tag = 1) ∨ (requested = false ∧ tag = 0) := by
  cases requested <;> simpa [voteReadBackMatches] using accepted

#print axioms transport_ballot_round_trips
#print axioms vote_reads_the_two_physical_slots_in_order
#print axioms scope_requires_both_groups
#print axioms a_reply_cannot_change_witness_mode

end Logkeeper.VoterTransport
