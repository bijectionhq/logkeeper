import Logkeeper.Protocol

set_option warningAsError true

namespace Logkeeper.OrderedBudgets

open Logkeeper.Protocol (ChargeClass)

def referenceCharge : Option Nat → Nat
  | none => 0
  | some names => 4 + 32 * names

def recordCharge (payload : Nat) (references : Option Nat) : Nat :=
  payload + (217 + referenceCharge references)

structure Budget where
  spent : Nat
  ordinary : Nat
  maintenance : Nat
  deriving DecidableEq

def fundedBudget (budget : Budget) (window ordinaryCapacity reserve : Nat) : Prop :=
  budget.spent ≤ window ∧
    budget.ordinary + (window - budget.spent) ≤ ordinaryCapacity ∧
    budget.maintenance ≤ reserve

def appendBudget (budget : Budget) (lane : ChargeClass) (charge : Nat) : Budget :=
  match lane with
  | .ordinary => { budget with
      spent := budget.spent + charge
      ordinary := budget.ordinary + charge }
  | .maintenance => { budget with maintenance := budget.maintenance + charge }

def admitsDebit (used charge ceiling : Nat) : Prop :=
  used + charge ≤ ceiling

def admitsAppend (budget : Budget) (lane : ChargeClass) (charge : Nat)
    (window ordinaryCapacity reserve : Nat) : Prop :=
  match lane with
  | .ordinary => admitsDebit budget.spent charge window ∧
      admitsDebit budget.ordinary charge ordinaryCapacity
  | .maintenance => admitsDebit budget.maintenance charge reserve

theorem admitted_append_preserves_funding {budget : Budget} {window capacity reserve : Nat}
    (funded : fundedBudget budget window capacity reserve) {lane : ChargeClass}
    {payload : Nat} {references : Option Nat}
    (admitted : admitsAppend budget lane (recordCharge payload references) window capacity reserve) :
    fundedBudget (appendBudget budget lane (recordCharge payload references)) window capacity reserve := by
  cases lane <;> simp [fundedBudget, admitsAppend, admitsDebit, appendBudget] at *
  · omega
  · exact ⟨funded.1, funded.2.1, admitted⟩

theorem funding_new_window {budget : Budget} {capacity reserve oldWindow newWindow : Nat}
    (funded : fundedBudget budget oldWindow capacity reserve)
    (paid : admitsDebit budget.ordinary newWindow capacity) :
    fundedBudget { budget with spent := 0 } newWindow capacity reserve := by
  exact ⟨Nat.zero_le _, by simpa [admitsDebit] using paid, funded.2.2⟩

theorem independent_maintenance_at_full_window {budget : Budget} {window capacity reserve charge : Nat}
    (full : budget.spent = window) (positive : 0 < charge)
    (fits : admitsDebit budget.maintenance charge reserve) :
    ¬ admitsAppend budget .ordinary charge window capacity reserve ∧
      admitsAppend budget .maintenance charge window capacity reserve := by
  refine ⟨fun attempted => ?_, fits⟩
  have inside := attempted.1
  unfold admitsDebit at inside
  omega

theorem reachable_full_window :
    fundedBudget (appendBudget ⟨0, 0, 0⟩ .ordinary (recordCharge 5 (some 1))) 258 258 257 := by
  simp [fundedBudget, appendBudget, recordCharge, referenceCharge]

theorem omitted_references_admit_an_unfunded_append :
    admitsAppend ⟨0, 0, 0⟩ .ordinary (recordCharge 5 none) 222 222 257 ∧
    ¬ admitsAppend ⟨0, 0, 0⟩ .ordinary (recordCharge 5 (some 1)) 222 222 257 := by
  simp [recordCharge, referenceCharge, admitsAppend, admitsDebit]

theorem ordinary_limit_cannot_fund_maintenance :
    admitsDebit 0 (recordCharge 5 (some 1)) 258 ∧
    ¬ admitsAppend ⟨0, 0, 0⟩ .maintenance (recordCharge 5 (some 1)) 258 258 257 := by
  simp [recordCharge, referenceCharge, admitsAppend, admitsDebit]

#print axioms admitted_append_preserves_funding
#print axioms funding_new_window
#print axioms independent_maintenance_at_full_window
#print axioms reachable_full_window
#print axioms omitted_references_admit_an_unfunded_append
#print axioms ordinary_limit_cannot_fund_maintenance

end Logkeeper.OrderedBudgets
