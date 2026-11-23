set_option warningAsError true

namespace Logkeeper.OrderedAdmission

def debit (used charge ceiling : Nat) : Option Nat :=
  if used + charge ≤ ceiling then some (used + charge) else none

/-- A nonempty live suffix intersects the prefix below the proposed floor. -/
def pinsSuffix (start stop floor : Nat) : Prop :=
  start < stop ∧ start < floor

def retainsReceipt (position expiresAt : Nat) (ownsLiveHold : Bool) : Prop :=
  position < expiresAt ∨ ownsLiveHold = true

def matchesFingerprint (stored presented : List UInt8) : Prop :=
  stored = presented

theorem maintenance_at_data_ceiling
    (dataCeiling userCharge used completionCharge reserve : Nat)
    (positive : 0 < userCharge) (funded : used + completionCharge ≤ reserve) :
    debit dataCeiling userCharge dataCeiling = none ∧
      debit used completionCharge reserve = some (used + completionCharge) := by
  constructor
  · unfold debit
    apply ite_eq_right
    omega
  · exact ite_eq_left funded

theorem pins_suffix_iff_intersects_prefix (start stop floor : Nat) :
    pinsSuffix start stop floor ↔ ∃ lsn, start ≤ lsn ∧ lsn < stop ∧ lsn < floor := by
  constructor
  · intro pins
    exact ⟨start, Nat.le_refl _, pins.1, pins.2⟩
  · rintro ⟨lsn, lower, within, removed⟩
    unfold pinsSuffix
    omega

theorem receipt_at_expiry_requires_hold (position : Nat) (ownsLiveHold : Bool) :
    retainsReceipt position position ownsLiveHold ↔ ownsLiveHold = true := by
  simp [retainsReceipt]

theorem different_fingerprints_are_refused (stored presented : List UInt8)
    (different : stored ≠ presented) : ¬ matchesFingerprint stored presented := by
  exact different

#print axioms maintenance_at_data_ceiling
#print axioms pins_suffix_iff_intersects_prefix
#print axioms receipt_at_expiry_requires_hold
#print axioms different_fingerprints_are_refused

end Logkeeper.OrderedAdmission
