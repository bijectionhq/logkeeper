import Std

namespace Logkeeper.Codec

abbrev Bytes := List UInt8

def commandVersion : UInt8 := 8

def decisionHeader (time : Bytes) : Bytes := commandVersion :: time

def readDecisionTime (frame : Bytes) : Option Bytes :=
  match frame with
  | [] => none
  | version :: rest =>
      if version = commandVersion ∧ 8 ≤ rest.length then some (rest.take 8) else none

def decisionHeaderMatches (frame time : Bytes) : Prop :=
  time.length = 8 ∧ frame.take 9 = decisionHeader time

theorem decision_time_exact (frame time : Bytes) :
    readDecisionTime frame = some time ↔ decisionHeaderMatches frame time := by
  cases frame with
  | nil => simp [readDecisionTime, decisionHeaderMatches, decisionHeader]
  | cons version rest =>
    constructor
    · intro accepted
      have h : version = commandVersion ∧ 8 ≤ rest.length := by
        by_cases h : version = commandVersion ∧ 8 ≤ rest.length
        · exact h
        · simp [readDecisionTime, h] at accepted
      have ht : rest.take 8 = time := by simpa [readDecisionTime, h] using accepted
      refine ⟨?_, ?_⟩
      · rw [← ht, List.length_take, Nat.min_eq_left h.2]
      · simp [decisionHeader, h.1, ht]
    · rintro ⟨width, header⟩
      have h : version = commandVersion ∧ rest.take 8 = time := by
        simpa [decisionHeader] using header
      have bounds : 8 ≤ rest.length := by
        have length := congrArg List.length h.2
        rw [List.length_take, width] at length
        omega
      simp [readDecisionTime, h.1, h.2, bounds]

theorem decision_time_round_trips (time rest : Bytes) (width : time.length = 8) :
    readDecisionTime (decisionHeader time ++ rest) = some time := by
  apply (decision_time_exact _ _).2
  refine ⟨width, ?_⟩
  simp [decisionHeader, ← width]

theorem short_decision_header_is_rejected (frame : Bytes) (short : frame.length < 9) :
    readDecisionTime frame = none := by
  cases frame with
  | nil => rfl
  | cons version rest =>
    have h : ¬ 8 ≤ rest.length := by simp at short; omega
    simp [readDecisionTime, h]

def flagByte (value : Bool) : UInt8 := if value then 1 else 0

def readFlag (tag : UInt8) : Option Bool :=
  if tag = 0 then some false else if tag = 1 then some true else none

theorem flag_exact (tag : UInt8) (value : Bool) :
    readFlag tag = some value ↔ tag = flagByte value := by
  cases value <;> simp [readFlag, flagByte] <;> split <;> simp_all

theorem flag_round_trips (value : Bool) : readFlag (flagByte value) = some value :=
  (flag_exact _ _).2 rfl

abbrev bodyLengthBounded (declared minimum maximum : Nat) : Prop :=
  minimum ≤ declared ∧ declared ≤ maximum

def boundedBodyLength (declared minimum maximum : Nat) : Option Nat :=
  if bodyLengthBounded declared minimum maximum then some declared else none

theorem bounded_body_length_exact (declared minimum maximum decoded : Nat) :
    boundedBodyLength declared minimum maximum = some decoded ↔
      bodyLengthBounded declared minimum maximum ∧ decoded = declared := by
  by_cases h : bodyLengthBounded declared minimum maximum
  · simp [boundedBodyLength, eq_comm]
  · simp [boundedBodyLength, h]

theorem body_over_limit_is_rejected (declared minimum maximum : Nat) (tooBig : maximum < declared) :
    boundedBodyLength declared minimum maximum = none := by
  simp [boundedBodyLength, bodyLengthBounded, Nat.not_le_of_lt tooBig]

#print axioms decision_time_exact
#print axioms decision_time_round_trips
#print axioms short_decision_header_is_rejected
#print axioms flag_exact
#print axioms flag_round_trips
#print axioms bounded_body_length_exact
#print axioms body_over_limit_is_rejected

end Logkeeper.Codec
