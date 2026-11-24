import Logkeeper

namespace Logkeeper.Generated

abbrev PartialMap (K V : Type) := K → Option V
abbrev PredSet (T : Type) := T → Prop

def mapContains (m : PartialMap K V) (k : K) : Prop := m k ≠ none
def mapValues (m : PartialMap K V) (v : V) : Prop := ∃ k, m k = some v
def setContains (s : PredSet T) (x : T) : Prop := s x
def setUnion (a b : PredSet T) : PredSet T := fun x => a x ∨ b x
def setSubset (a b : PredSet T) : Prop := ∀ x, a x → b x
def seqSet (xs : List T) : PredSet T := fun x => x ∈ xs

def optionSome (value : Option T) : Prop := value ≠ none
def optionNone (value : Option T) : Prop := value = none

-- Values outside the index domain have no usable equations. The fallback is
-- keyed by the original operation's inputs.
noncomputable opaque unspecified {Input Output : Type} [Nonempty Output] (_ : Input) : Output :=
  Classical.choice inferInstance

noncomputable def optionValue [Nonempty T] (value : Option T) : T :=
  value.getD (unspecified value)

noncomputable def mapIndex [Nonempty V] (m : PartialMap K V) (k : K) : V :=
  (m k).getD (unspecified (m, k))

noncomputable def seqIndex [Nonempty T] (xs : List T) (i : Int) : T :=
  if 0 ≤ i then xs[i.toNat]?.getD (unspecified (xs, i)) else unspecified (xs, i)

noncomputable def seqSubrange (xs : List T) (start stop : Int) : List T :=
  if 0 ≤ start ∧ start ≤ stop ∧ stop ≤ (xs.length : Int) then
    (xs.drop start.toNat).take (stop - start).toNat
  else unspecified (xs, start, stop)

def seqNew (length : Nat) (f : Int → T) : List T :=
  List.ofFn (fun i : Fin length => f i.val)

noncomputable def seqDrop (xs : List T) (n : Int) : List T :=
  seqSubrange xs n xs.length

noncomputable def seqTake (xs : List T) (n : Int) : List T :=
  seqSubrange xs 0 n

noncomputable def asNatural (n : Int) : Nat :=
  if 0 ≤ n then n.toNat else unspecified n

theorem asNatural_of_nonneg (n : Int) (h : 0 ≤ n) : asNatural n = n.toNat := by
  exact ite_eq_left h

def clipUnsigned (bits : Nat) (n : Int) : Nat :=
  (n % ↑((2 : Nat) ^ bits)).toNat

theorem clipUnsigned_nat (bits n : Nat) (within : n < 2 ^ bits) :
    clipUnsigned bits (n : Int) = n := by
  have bounds : 0 ≤ (n : Int) ∧ (n : Int) < ↑((2 : Nat) ^ bits) := by omega
  rw [clipUnsigned, Int.emod_eq_of_lt bounds.1 bounds.2]
  rfl

def intKeys : List Nat → List Int := List.map Int.ofNat
def intReferences : List (List Nat) → List (List Int) := List.map intKeys

structure ReadInterval where
  empty : Bool
  floor : Nat
  first : Nat
  through : Nat
  retained : Nat

structure CheckpointAccess where
  cut : Nat
  erasureFloor : Nat
  retained : Bool
  closed : Bool

structure Cut where
  nextLsn : Nat
  history : List UInt8
  deriving DecidableEq, Nonempty

instance : Nonempty Logkeeper.Protocol.ChargeClass := ⟨.ordinary⟩

abbrev ReceiptRow (R : Type) := Logkeeper.Protocol.Ordered.RetainedReceipt (List UInt8) R

noncomputable instance [Nonempty R] : Nonempty (ReceiptRow R) :=
  ⟨⟨[], Classical.choice inferInstance⟩⟩

structure Ballot where
  round : Nat
  nonce : Nat
  deriving DecidableEq, Nonempty

structure VoterState where
  promised : Option Ballot
  accepted : Option (Ballot × Nat)
  deriving Nonempty

abbrev Fingerprint := List UInt8

structure SlotImage where
  generation : Nat
  digest : Fingerprint
  deriving Nonempty

structure SlotPair where
  selected : UInt8
  images : List SlotImage
  deriving Nonempty

structure VoterSlots where
  voter : Nat
  slots : SlotPair
  deriving Nonempty

structure Vote where
  voter : Nat
  ballot : Ballot
  digest : Fingerprint
  slots : SlotPair
  readBack : Bool

structure ReceiptKeys where
  active : PartialMap Nat Fingerprint
  predecessor : List Fingerprint
  retained : List Fingerprint

inductive AbstractAuthority (G : Type) where
  | active (grant : G)
  | vacant (previous : G)

end Logkeeper.Generated
