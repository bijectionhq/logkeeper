set_option warningAsError true

namespace DisposalLease

/-- The worker admits a read only while its own clock is before the lease end. -/
def Admits (leaseEnd workerClock : Nat) : Prop := workerClock < leaseEnd

/-- Disposal waits for the lease end plus the drift bound on the journal clock. -/
def MayDispose (leaseEnd drift now : Nat) : Prop := leaseEnd + drift ≤ now

theorem no_read_is_admitted_once_disposal_is_allowed
    (leaseEnd drift now workerClock : Nat)
    (bounded : now ≤ workerClock + drift) (dispose : MayDispose leaseEnd drift now) :
    ¬ Admits leaseEnd workerClock := by
  unfold Admits MayDispose at *
  omega

theorem without_the_drift_margin_a_lagging_worker_still_admits
    (leaseEnd drift : Nat) (granted : 0 < leaseEnd) (positive : 0 < drift) :
    ∃ now workerClock, now ≤ workerClock + drift ∧ leaseEnd ≤ now ∧ Admits leaseEnd workerClock :=
  ⟨leaseEnd, leaseEnd - 1, by omega, Nat.le_refl _, by unfold Admits; omega⟩

#print axioms no_read_is_admitted_once_disposal_is_allowed
#print axioms without_the_drift_margin_a_lagging_worker_still_admits

end DisposalLease
