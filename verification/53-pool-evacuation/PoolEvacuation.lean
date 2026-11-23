import SharedExtentAccounting

set_option warningAsError true

namespace PoolEvacuation

open SharedExtentAccounting (Layout)

variable {Pool Zone Image Ticket : Type}

structure State (Pool Ticket : Type) where
  accounting : SharedExtentAccounting.State Pool Ticket
  placed : Nat → Prop
  reachable : Pool → Prop

def Eligible (layout : Layout Pool) (state : State Pool Ticket) (version : Nat) : Prop :=
  state.placed version ∧ state.reachable (layout.pool version)

def Protected (layout : Layout Pool) (zone : Pool → Zone) (state : State Pool Ticket) : Prop :=
  ∀ failed, ∃ version, Eligible layout state version ∧ zone (layout.pool version) ≠ failed

def loseZone (zone : Pool → Zone) (state : State Pool Ticket) (failed : Zone) : State Pool Ticket :=
  {state with reachable := fun pool => state.reachable pool ∧ zone pool ≠ failed}

def dropPlacement (state : State Pool Ticket) (version : Nat) : State Pool Ticket :=
  {state with placed := fun other => state.placed other ∧ other ≠ version}

structure Sound [DecidableEq Pool] (layout : Layout Pool) (needs : SharedCustody.Dependencies)
    (image : Nat → Image) (required : Image) (state : State Pool Ticket) : Prop where
  ledger : SharedExtentAccounting.Sound layout needs state.accounting
  placement : ∀ version, state.placed version →
    image version = required ∧ state.accounting.catalog.physical version = true

inductive Step [DecidableEq Pool] [DecidableEq Ticket]
    (layout : Layout Pool) (needs : SharedCustody.Dependencies)
    (closeAllowed : Nat → Prop) (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (zone : Pool → Zone) (image : Nat → Image) (required : Image) :
    State Pool Ticket → State Pool Ticket → Prop
  | account {state next}
      (update : SharedExtentAccounting.Step layout needs closeAllowed reserve state.accounting next)
      (reachableForNew : ∀ version ∈ next.debits, version ∉ state.accounting.debits →
        state.reachable (layout.pool version))
      (ordinaryAdmission : ∀ pool, state.accounting.ordinary pool < next.ordinary pool →
        state.reachable pool)
      (retains : ∀ version, state.placed version → next.catalog.physical version = true) :
      Step layout needs closeAllowed reserve zone image required state {state with accounting := next}
  | join {state} (version : Nat) (reachable : state.reachable (layout.pool version))
      (exact : image version = required)
      (registered : state.accounting.catalog.physical version = true) :
      Step layout needs closeAllowed reserve zone image required state
        {state with placed := fun other => state.placed other ∨ other = version}
  | fault {state} (failed : Zone) :
      Step layout needs closeAllowed reserve zone image required state (loseZone zone state failed)
  | withdraw {state} (version : Nat) (inPlacement : state.placed version)
      (coverage : Protected layout zone (dropPlacement state version)) :
      Step layout needs closeAllowed reserve zone image required state (dropPlacement state version)

variable [DecidableEq Pool] [DecidableEq Ticket]
variable {layout : Layout Pool} {needs : SharedCustody.Dependencies}
variable {closeAllowed : Nat → Prop} {reserve : ProviderIOClosure.Custody Ticket → Prop}
variable {zone : Pool → Zone} {image : Nat → Image} {required : Image}

theorem every_step_preserves_valid_placement_and_numeric_custody {state next : State Pool Ticket}
    (safe : Sound layout needs image required state)
    (step : Step layout needs closeAllowed reserve zone image required state next) :
    Sound layout needs image required next := by
  cases step with
  | account update _ _ retains =>
      refine ⟨SharedExtentAccounting.numeric_and_custody_invariants_hold_after_each_step safe.ledger update, ?_⟩
      exact fun version held => ⟨(safe.placement version held).1, retains version held⟩
  | join version _ exact registered =>
      refine ⟨safe.ledger, ?_⟩
      intro query held
      rcases held with original | rfl
      · exact safe.placement query original
      · exact ⟨exact, registered⟩
  | fault => exact ⟨safe.ledger, safe.placement⟩
  | withdraw => exact ⟨safe.ledger, fun version held => safe.placement version held.1⟩

inductive Trace (layout : Layout Pool) (needs : SharedCustody.Dependencies)
    (closeAllowed : Nat → Prop) (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (zone : Pool → Zone) (image : Nat → Image) (required : Image) :
    State Pool Ticket → State Pool Ticket → Prop
  | same (state : State Pool Ticket) : Trace layout needs closeAllowed reserve zone image required state state
  | next {first state next} : Trace layout needs closeAllowed reserve zone image required first state →
      Step layout needs closeAllowed reserve zone image required state next →
      Trace layout needs closeAllowed reserve zone image required first next

theorem trace_preserves_valid_placement_and_numeric_custody {first next : State Pool Ticket}
    (safe : Sound layout needs image required first)
    (trace : Trace layout needs closeAllowed reserve zone image required first next) :
    Sound layout needs image required next := by
  induction trace with
  | same => exact safe
  | next _ step prior => exact every_step_preserves_valid_placement_and_numeric_custody prior step

theorem new_debit_requires_eligible_local_capacity {state next : State Pool Ticket}
    (safe : Sound layout needs image required state)
    (step : Step layout needs closeAllowed reserve zone image required state next)
    {version : Nat} (newDebit : version ∈ next.accounting.debits)
    (unfunded : version ∉ state.accounting.debits) :
    state.reachable (layout.pool version) ∧
      SharedExtentAccounting.Used layout next.accounting (layout.pool version) ≤
        layout.limit (layout.pool version) := by
  have within := (every_step_preserves_valid_placement_and_numeric_custody safe step).ledger.fit
  refine ⟨?_, within _⟩
  cases step with
  | account _ openPool _ _ => exact openPool version newDebit unfunded
  | join => exact False.elim (unfunded newDebit)
  | fault => exact False.elim (unfunded newDebit)
  | withdraw => exact False.elim (unfunded newDebit)

omit [DecidableEq Ticket] in
theorem protection_covers_any_single_zone_failure {state : State Pool Ticket}
    (safe : Sound layout needs image required state)
    (coverage : Protected layout zone state) (failed : Zone) :
    ∃ version, Eligible layout (loseZone zone state failed) version ∧ image version = required ∧
      (state.accounting.provider version).present = true ∧ version ∈ state.accounting.debits := by
  obtain ⟨version, ⟨placed, online⟩, different⟩ := coverage failed
  obtain ⟨exact, registered⟩ := safe.placement version placed
  have present := safe.ledger.available version registered
  exact ⟨version, ⟨placed, online, different⟩, exact, present, safe.ledger.paid version (.inl present)⟩

omit [DecidableEq Pool] [DecidableEq Ticket] in
theorem copies_in_one_zone_do_not_restore_protection {state : State Pool Ticket} (single : Zone)
    (coLocated : ∀ version, Eligible layout state version → zone (layout.pool version) = single) :
    ¬ Protected layout zone state := by
  intro coverage
  obtain ⟨version, eligible, outside⟩ := coverage single
  exact outside (coLocated version eligible)

theorem withdrawal_preserves_protection {state next : State Pool Ticket}
    (step : Step layout needs closeAllowed reserve zone image required state next)
    {version : Nat} (original : state.placed version) (removed : ¬next.placed version) :
    Protected layout zone next := by
  cases step with
  | account => exact False.elim (removed original)
  | join => exact False.elim (removed (.inl original))
  | fault => exact False.elim (removed original)
  | withdraw _ _ coverage => exact coverage

theorem funded_offline_withdrawal_preserves_original_borrow_and_debit {state : State Pool Ticket}
    (safe : Sound layout needs image required state) {original : Nat}
    (inPlacement : state.placed original) (unreachable : ¬state.reachable (layout.pool original))
    (borrowed : 0 < state.accounting.catalog.borrows original)
    (built : Protected layout zone (dropPlacement state original)) :
    ∃ next, Step layout needs closeAllowed reserve zone image required state next ∧
      Protected layout zone next ∧ ¬next.placed original ∧
      ¬next.reachable (layout.pool original) ∧ next.accounting = state.accounting ∧
      0 < next.accounting.catalog.borrows original ∧ original ∈ next.accounting.debits :=
  ⟨dropPlacement state original, .withdraw original inPlacement built, built,
    fun present => present.2 rfl, unreachable, rfl, borrowed,
    (SharedExtentAccounting.a_read_borrow_preserves_its_debit_without_a_live_root safe.ledger borrowed).2⟩

omit [DecidableEq Ticket] in
theorem physical_failure_does_not_refund_any_debit_or_settle_a_live_borrow {state : State Pool Ticket}
    (safe : Sound layout needs image required state) (failed : Zone)
    {version evidence : Nat} (charged : version ∈ state.accounting.debits)
    (borrowed : 0 < state.accounting.catalog.borrows version) :
    version ∈ (loseZone zone state failed).accounting.debits ∧
      ¬ SharedExtentAccounting.CanRefund (loseZone zone state failed).accounting version evidence :=
  ⟨charged, SharedExtentAccounting.an_old_borrow_blocks_return_of_its_physical_debit safe.ledger borrowed⟩

#print axioms every_step_preserves_valid_placement_and_numeric_custody
#print axioms trace_preserves_valid_placement_and_numeric_custody
#print axioms new_debit_requires_eligible_local_capacity
#print axioms protection_covers_any_single_zone_failure
#print axioms copies_in_one_zone_do_not_restore_protection
#print axioms withdrawal_preserves_protection
#print axioms funded_offline_withdrawal_preserves_original_borrow_and_debit
#print axioms physical_failure_does_not_refund_any_debit_or_settle_a_live_borrow

end PoolEvacuation
