import Logkeeper.OrderedWriter

set_option warningAsError true

/- The timing predicates originate in Study 113 (113-worker-disposal/DisposalLease.lean). -/
namespace DisposalLease

open Logkeeper.Kernel.Ordered (authorize_writer)

def Admits (leaseEnd workerClock : Nat) : Prop := workerClock < leaseEnd

def MayDispose (leaseEnd drift now : Nat) : Prop := leaseEnd + drift ≤ now

def decision_time (previous incoming : Nat) : Option Nat :=
  if previous ≤ incoming then some incoming else none

def lease_end {Owner : Type} [DecidableEq Owner] (principal : Option Owner)
    (current : Option (Owner × Nat × Nat)) (grant : Owner × Nat × Nat)
    (enrolled : Option Owner) (now duration maxTime : Nat) : Option Nat :=
  if authorize_writer principal current grant && decide (enrolled = some grant.1) &&
      decide (now + duration ≤ maxTime) then some (now + duration) else none

def disposal_time (endTime : Option Nat) (drift maxTime : Nat) : Option Nat :=
  match endTime with
  | none => some 0
  | some time => if time + drift ≤ maxTime then some (time + drift) else none

/-- The exact enrollment is compared against the worker's current roster slot. -/
def withdrawn (serial lastSerial : Nat) (enrolled : Bool) : Bool :=
  decide (0 < serial ∧ serial ≤ lastSerial) && !enrolled

def may_dispose (authorized : Bool) (serial lastSerial : Nat) (enrolled : Bool)
    (now : Nat) (endTime : Option Nat) (drift maxTime : Nat) : Bool :=
  authorized && withdrawn serial lastSerial enrolled &&
    (disposal_time endTime drift maxTime).any (fun due => due ≤ now)

def eligible_owner {Worker Owner : Type} [LT Owner] (roster : Worker → Option Owner)
    (owner : Owner) (worker : Worker) (after : Option Owner) : Prop :=
  (match after with | some cursor => cursor < owner | none => True) ∧ roster worker ≠ some owner

def qualifying_owners {Worker Owner : Type} [LT Owner] (holds : List (Owner × Worker))
    (roster : Worker → Option Owner) (after : Option Owner) (owner : Owner) : Prop :=
  ∃ worker, (owner, worker) ∈ holds ∧ eligible_owner roster owner worker after

/-- The exact first page is sorted and contains all eligible owners unless it is full.
Any omitted eligible owner sorts strictly after every returned owner. -/
def owner_page {Owner : Type} [LT Owner] (eligible : Owner → Prop)
    (limit : Nat) (page : List Owner) : Prop :=
  page.Pairwise (· < ·) ∧ page.length ≤ limit ∧
    (∀ owner ∈ page, eligible owner) ∧
    (∀ owner, eligible owner → owner ∉ page →
      page.length = limit ∧ ∀ listed ∈ page, listed < owner)

/-- Association-list image of the hold map. A grant can add a fresh recovery hold. -/
def grant_holds {Key Hold : Type} (holds : List (Key × Hold)) (newHold : Option (Key × Hold)) :
    List (Key × Hold) :=
  match newHold with
  | none => holds
  | some entry => entry :: holds

theorem decision_time_is_monotone {old incoming applied : Nat}
    (appliedDecision : decision_time old incoming = some applied) :
    old ≤ applied ∧ applied = incoming := by
  unfold decision_time at appliedDecision
  split at appliedDecision <;> simp_all

theorem lease_requires_current_enrolled_grant {Owner : Type} [DecidableEq Owner]
    {principal enrolled : Option Owner} {current : Option (Owner × Nat × Nat)}
    {grant : Owner × Nat × Nat} {now duration maxTime time : Nat}
    (issued : lease_end principal current grant enrolled now duration maxTime = some time) :
    authorize_writer principal current grant = true ∧ enrolled = some grant.1 ∧
      time = now + duration := by
  unfold lease_end at issued
  split at issued <;> simp_all

theorem no_read_is_admitted_once_disposal_is_allowed
    (leaseEnd drift now workerClock : Nat)
    (bounded : now ≤ workerClock + drift) (dispose : MayDispose leaseEnd drift now) :
    ¬ Admits leaseEnd workerClock := by
  unfold Admits MayDispose at *
  omega

theorem disposal_requires_withdrawal_and_drift {authorized enrolled : Bool}
    {serial lastSerial now drift maxTime : Nat} {endTime : Option Nat}
    (accepted : may_dispose authorized serial lastSerial enrolled now endTime drift maxTime = true) :
    withdrawn serial lastSerial enrolled = true ∧
      ∀ time, endTime = some time → MayDispose time drift now := by
  simp only [may_dispose, Bool.and_eq_true] at accepted
  refine ⟨accepted.1.2, ?_⟩
  intro time present
  rw [present] at accepted
  by_cases bounded : time + drift ≤ maxTime
  · simpa [MayDispose, disposal_time, bounded] using accepted.2
  · simp [disposal_time, bounded] at accepted

theorem full_page_has_only_later_omissions {Owner : Type} [LT Owner]
    {eligible : Owner → Prop} {limit : Nat} {page : List Owner}
    (exactPage : owner_page eligible limit page) {owner : Owner}
    (qualifies : eligible owner) (omitted : owner ∉ page) :
    page.length = limit ∧ ∀ listed ∈ page, listed < owner :=
  exactPage.2.2.2 owner qualifies omitted

theorem grant_change_preserves_holds {Key Hold : Type} (holds : List (Key × Hold))
    (newHold : Option (Key × Hold)) (entry : Key × Hold) (held : entry ∈ holds) :
    entry ∈ grant_holds holds newHold := by
  cases newHold <;> simp_all [grant_holds]

-- Concrete reachable timing witness: issue at 10, withdraw, then reach the disposal time.
example :
    lease_end (some 2) (some (2, 3, 1)) (2, 3, 1) (some 2) 10 8 100 = some 18 ∧
    decision_time 10 19 = some 19 ∧
    may_dispose true 2 2 false 19 (some 18) 1 100 = true := by decide

example : owner_page (fun owner : Nat => owner ∈ [2, 4, 7]) 2 [2, 4] := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro owner member
    simp at member ⊢
    omega
  · intro owner eligible omitted
    simp at eligible omitted
    have : owner = 7 := by omega
    subst owner
    simp

#print axioms decision_time_is_monotone
#print axioms lease_requires_current_enrolled_grant
#print axioms no_read_is_admitted_once_disposal_is_allowed
#print axioms disposal_requires_withdrawal_and_drift
#print axioms full_page_has_only_later_omissions
#print axioms grant_change_preserves_holds

end DisposalLease
