set_option warningAsError true

namespace LeaseBounds

def MayServe (worker drift leaseEnd : Nat) : Prop :=
  worker + drift < leaseEnd

theorem admission_precedes_cutover
    (worker drift leaseEnd now : Nat)
    (bounded : now ≤ worker + drift)
    (admission : MayServe worker drift leaseEnd) :
    now < leaseEnd := by
  unfold MayServe at admission
  omega

def ReportedFloor (oldestActive applied : Nat) : Nat :=
  min oldestActive applied

theorem report_covers_existing_borrow
    (oldestActive applied cut : Nat) (registered : oldestActive ≤ cut) :
    ReportedFloor oldestActive applied ≤ cut := by
  exact Nat.le_trans (Nat.min_le_left oldestActive applied) registered

def InAdmissionRange (reported cut : Nat) : Prop :=
  reported ≤ cut

theorem report_covers_later_borrow
    (reported trimThrough cut : Nat)
    (authorizedTrim : trimThrough ≤ reported)
    (admitted : InAdmissionRange reported cut) :
    trimThrough ≤ cut := by
  unfold InAdmissionRange at admitted
  omega

#print axioms admission_precedes_cutover
#print axioms report_covers_existing_borrow
#print axioms report_covers_later_borrow

end LeaseBounds
