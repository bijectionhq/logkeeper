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

def trimBudget (budget : Budget) (credit : Logkeeper.Protocol.Credit) : Budget :=
  { budget with
    ordinary := budget.ordinary - credit.ordinary
    maintenance := budget.maintenance - credit.maintenance }

theorem trim_preserves_funding {budget : Budget} {window capacity reserve : Nat}
    (funded : fundedBudget budget window capacity reserve) (credit : Logkeeper.Protocol.Credit) :
    fundedBudget (trimBudget budget credit) window capacity reserve := by
  simp only [fundedBudget, trimBudget] at *
  omega

structure State where
  budget : Budget
  window : Nat

inductive Step (capacity reserve : Nat) : State → State → Prop where
  | append (state : State) (lane : ChargeClass) (payload : Nat) (references : Option Nat)
      (admitted : admitsAppend state.budget lane (recordCharge payload references)
        state.window capacity reserve) :
      Step capacity reserve state
        { state with budget := appendBudget state.budget lane (recordCharge payload references) }
  | fund (state : State) (window : Nat) (paid : admitsDebit state.budget.ordinary window capacity) :
      Step capacity reserve state ⟨{ state.budget with spent := 0 }, window⟩
  | trim (state : State) (credit : Logkeeper.Protocol.Credit)
      (ordinary : credit.ordinary ≤ state.budget.ordinary)
      (maintenance : credit.maintenance ≤ state.budget.maintenance) :
      Step capacity reserve state { state with budget := trimBudget state.budget credit }

inductive Trace (capacity reserve : Nat) : State → State → Prop where
  | empty (state : State) : Trace capacity reserve state state
  | next {start here finish : State} (earlier : Trace capacity reserve start here)
      (step : Step capacity reserve here finish) : Trace capacity reserve start finish

theorem trace_preserves_funding {start finish : State} {capacity reserve : Nat}
    (funded : fundedBudget start.budget start.window capacity reserve)
    (trace : Trace capacity reserve start finish) :
    fundedBudget finish.budget finish.window capacity reserve := by
  induction trace with
  | empty => exact funded
  | next _ step prior =>
    cases step with
    | append _ _ _ admitted => exact admitted_append_preserves_funding prior admitted
    | fund _ paid => exact funding_new_window prior paid
    | trim credit _ _ => exact trim_preserves_funding prior credit

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
#print axioms trim_preserves_funding
#print axioms trace_preserves_funding
#print axioms independent_maintenance_at_full_window
#print axioms reachable_full_window
#print axioms omitted_references_admit_an_unfunded_append
#print axioms ordinary_limit_cannot_fund_maintenance

end Logkeeper.OrderedBudgets
