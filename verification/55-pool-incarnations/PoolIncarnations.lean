import SharedExtentAccounting

set_option warningAsError true

namespace PoolIncarnations

open SharedExtentAccounting (Layout)
open SnapshotAdmission (setSlot)

variable {Ticket Book : Type}

inductive Phase where
  | offline
  | quarantine
  | eligible
  deriving DecidableEq

structure Access where
  phase : Phase
  epoch : Nat

structure Validation (Book : Type) where
  scope : Nat
  epoch : Nat
  book : Book

structure State (Ticket : Type) where
  ledger : SharedExtentAccounting.State Nat Ticket
  registry : List Nat
  issued : Nat
  access : Nat → Access

def Eligible (state : State Ticket) (scope : Nat) : Prop :=
  scope ∈ state.registry ∧ (state.access scope).phase = .eligible

def Uses (layout : Layout Nat) (ledger : SharedExtentAccounting.State Nat Ticket) (scope : Nat) : Prop :=
  (∃ version ∈ ledger.debits, layout.pool version = scope) ∨ 0 < ledger.ordinary scope

def Uncharged (layout : Layout Nat) (state : State Ticket) (scope : Nat) : Prop :=
  ¬ Uses layout state.ledger scope

structure Sound (limit : Nat) (layout : Layout Nat) (needs : SharedCustody.Dependencies)
    (state : State Ticket) : Prop where
  funded : SharedExtentAccounting.Sound layout needs state.ledger
  fit : state.registry.length ≤ limit
  unique : state.registry.Nodup
  issued : ∀ scope ∈ state.registry, scope ≤ state.issued
  covered : ∀ scope, Uses layout state.ledger scope → scope ∈ state.registry

def register (state : State Ticket) : State Ticket :=
  let scope := state.issued + 1
  {state with registry := scope :: state.registry, issued := scope,
              access := setSlot state.access scope ⟨.quarantine, 0⟩}

def setAccess (state : State Ticket) (scope : Nat) (access : Access) : State Ticket :=
  {state with access := setSlot state.access scope access}

def fault (state : State Ticket) (scope : Nat) : State Ticket :=
  setAccess state scope ⟨.offline, (state.access scope).epoch + 1⟩

def changePhase (state : State Ticket) (scope : Nat) (phase : Phase) : State Ticket :=
  setAccess state scope {state.access scope with phase}

def forget (state : State Ticket) (scope : Nat) : State Ticket :=
  {state with registry := state.registry.filter (· != scope)}

def CanOpen (expected : SharedExtentAccounting.State Nat Ticket → Nat → Book)
    (authenticated : Validation Book → Prop) (state : State Ticket) (scope : Nat)
    (proof : Validation Book) : Prop :=
  scope ∈ state.registry ∧ (state.access scope).phase = .quarantine ∧
    proof.scope = scope ∧ proof.epoch = (state.access scope).epoch ∧
    proof.book = expected state.ledger scope ∧ authenticated proof

inductive Event where
  | register
  | fault
  | reconnect
  | validate
  | settle
  | account

inductive Step [DecidableEq Ticket] (limit : Nat) (layout : Layout Nat)
    (needs : SharedCustody.Dependencies) (closeAllowed : Nat → Prop)
    (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (expected : SharedExtentAccounting.State Nat Ticket → Nat → Book)
    (authenticated : Validation Book → Prop) (namespaceClosed : Nat → Prop) :
    State Ticket → Event → State Ticket → Prop
  | register {state} (room : state.registry.length < limit) :
      Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        state .register (PoolIncarnations.register state)
  | fault {state} (scope : Nat) (enrolled : scope ∈ state.registry) :
      Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed state .fault
        (PoolIncarnations.fault state scope)
  | reconnect {state} (scope : Nat) (enrolled : scope ∈ state.registry)
      (offline : (state.access scope).phase = .offline) :
      Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        state .reconnect (changePhase state scope .quarantine)
  | validate {state} (scope : Nat) (proof : Validation Book)
      (verified : CanOpen expected authenticated state scope proof) :
      Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        state .validate (changePhase state scope .eligible)
  | settle {state} (scope : Nat) (enrolled : scope ∈ state.registry)
      (offline : (state.access scope).phase = .offline)
      (terminal : namespaceClosed scope) (clear : Uncharged layout state scope) :
      Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        state .settle (forget state scope)
  | account {state next}
      (update : SharedExtentAccounting.Step layout needs closeAllowed reserve state.ledger next)
      (newAllocation : ∀ version ∈ next.debits, version ∉ state.ledger.debits →
        Eligible state (layout.pool version))
      (newOrdinary : ∀ scope, state.ledger.ordinary scope < next.ordinary scope → Eligible state scope) :
      Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        state .account {state with ledger := next}

variable [DecidableEq Ticket] {limit : Nat} {layout : Layout Nat} {needs : SharedCustody.Dependencies}
variable {closeAllowed namespaceClosed : Nat → Prop} {reserve : ProviderIOClosure.Custody Ticket → Prop}
variable {expected : SharedExtentAccounting.State Nat Ticket → Nat → Book}
variable {authenticated : Validation Book → Prop}

theorem every_step_preserves_bounded_scoped_custody {state next : State Ticket} {event : Event}
    (safe : Sound limit layout needs state)
    (step : Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed state event next) :
    Sound limit layout needs next := by
  cases step with
  | register room =>
      refine ⟨safe.funded, ?_, ?_, ?_, fun scope used => List.mem_cons_of_mem _ (safe.covered scope used)⟩
      · simpa [register] using Nat.succ_le_of_lt room
      · apply List.nodup_cons.mpr
        exact ⟨fun old => Nat.not_succ_le_self _ (safe.issued _ old), safe.unique⟩
      · intro scope enrolled
        rcases List.mem_cons.mp enrolled with rfl | old
        · exact Nat.le_refl _
        · exact Nat.le_succ_of_le (safe.issued _ old)
  | fault | reconnect | validate =>
      exact ⟨safe.funded, safe.fit, safe.unique, safe.issued, safe.covered⟩
  | settle scope _ _ _ clear =>
      refine ⟨safe.funded, Nat.le_trans (List.length_filter_le _ _) safe.fit,
        safe.unique.filter _, ?_, ?_⟩
      · intro id member
        exact safe.issued id (List.mem_filter.mp member).1
      · intro id used
        have different : id ≠ scope := by
          intro same
          subst id
          exact clear used
        exact List.mem_filter.mpr ⟨safe.covered id used, by simp [different]⟩
  | @account next update newAllocation newOrdinary =>
      refine ⟨SharedExtentAccounting.numeric_and_custody_invariants_hold_after_each_step safe.funded update,
        safe.fit, safe.unique, safe.issued, ?_⟩
      intro scope used
      rcases used with ⟨version, booked, rfl⟩ | ordinary
      · by_cases old : version ∈ state.ledger.debits
        · exact safe.covered _ (.inl ⟨version, old, rfl⟩)
        · exact (newAllocation version booked old).1
      · by_cases old : 0 < state.ledger.ordinary scope
        · exact safe.covered _ (.inr old)
        · change 0 < next.ordinary scope at ordinary
          exact (newOrdinary scope (by omega)).1

inductive Trace (limit : Nat) (layout : Layout Nat) (needs : SharedCustody.Dependencies)
    (closeAllowed : Nat → Prop) (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (expected : SharedExtentAccounting.State Nat Ticket → Nat → Book)
    (authenticated : Validation Book → Prop) (namespaceClosed : Nat → Prop) :
    State Ticket → State Ticket → Prop
  | same (state) : Trace limit layout needs closeAllowed reserve expected authenticated namespaceClosed state state
  | next {first before after event}
      (prefixTrace : Trace limit layout needs closeAllowed reserve expected authenticated namespaceClosed first before)
      (step : Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed before event after) :
      Trace limit layout needs closeAllowed reserve expected authenticated namespaceClosed first after

theorem bounded_custody_survives_arbitrary_admitted_traces {first next : State Ticket}
    (safe : Sound limit layout needs first)
    (trace : Trace limit layout needs closeAllowed reserve expected authenticated namespaceClosed first next) :
    Sound limit layout needs next := by
  induction trace with
  | same => exact safe
  | next _ step earlier => exact every_step_preserves_bounded_scoped_custody earlier step

def registrations : Event → Nat
  | .register => 1
  | _ => 0

inductive WithoutSettlement (limit : Nat) (layout : Layout Nat) (needs : SharedCustody.Dependencies)
    (closeAllowed : Nat → Prop) (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (expected : SharedExtentAccounting.State Nat Ticket → Nat → Book)
    (authenticated : Validation Book → Prop) (namespaceClosed : Nat → Prop) :
    State Ticket → Nat → State Ticket → Prop
  | same (state) :
      WithoutSettlement limit layout needs closeAllowed reserve expected authenticated namespaceClosed state 0 state
  | next {first before after count event}
      (prior : WithoutSettlement limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        first count before)
      (unsettled : event ≠ .settle)
      (step : Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed before event after) :
      WithoutSettlement limit layout needs closeAllowed reserve expected authenticated namespaceClosed
        first (count + registrations event) after

theorem without_settlement_each_registration_consumes_another_slot {first next : State Ticket}
    (safe : Sound limit layout needs first) {count : Nat}
    (trace : WithoutSettlement limit layout needs closeAllowed reserve expected authenticated
      namespaceClosed first count next) :
    next.registry.length = first.registry.length + count ∧ first.registry.length + count ≤ limit := by
  induction trace with
  | same => simpa using safe.fit
  | next _ unsettled step earlier =>
      cases step with
      | register room =>
          constructor
          · simp [register, registrations, earlier.1, Nat.add_assoc]
          · rw [← Nat.add_assoc, ← earlier.1]
            exact Nat.succ_le_of_lt room
      | settle => exact False.elim (unsettled rfl)
      | fault | reconnect | validate | account =>
          simpa [registrations, fault, changePhase, setAccess] using earlier

omit [DecidableEq Ticket] in
theorem a_previous_probe_cannot_authorize_after_another_failure {state : State Ticket} {scope : Nat}
    {proof : Validation Book} (beforeFault : proof.epoch = (state.access scope).epoch) :
    ¬ CanOpen expected authenticated (changePhase (fault state scope) scope .quarantine) scope proof := by
  intro accepted
  have newEpoch : proof.epoch = ((changePhase (fault state scope) scope .quarantine).access scope).epoch :=
    accepted.2.2.2.1
  simp [fault, changePhase, setAccess, setSlot] at newEpoch
  omega

theorem fault_at_capacity_keeps_the_original_registry_and_ledger {state : State Ticket} {scope : Nat}
    (enrolled : scope ∈ state.registry) :
    Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
      state .fault (fault state scope) ∧
    (fault state scope).registry = state.registry ∧ (fault state scope).ledger = state.ledger :=
  ⟨.fault scope enrolled, rfl, rfl⟩

theorem exact_validation_can_reopen_without_another_slot {state : State Ticket} {scope : Nat}
    {proof : Validation Book} (verified : CanOpen expected authenticated state scope proof) :
    ∃ next, Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed state .validate next ∧
      Eligible next scope ∧ next.registry = state.registry ∧ next.ledger = state.ledger := by
  refine ⟨changePhase state scope .eligible, .validate scope proof verified, ⟨verified.1, ?_⟩, rfl, rfl⟩
  simp [changePhase, setAccess, setSlot]

theorem a_forgotten_issued_namespace_cannot_rejoin {first next : State Ticket}
    (trace : Trace limit layout needs closeAllowed reserve expected authenticated namespaceClosed first next)
    {scope : Nat} (issued : scope ≤ first.issued) (absent : scope ∉ first.registry) :
    scope ≤ next.issued ∧ scope ∉ next.registry := by
  induction trace with
  | same => exact ⟨issued, absent⟩
  | next _ step prior =>
      cases step with
      | register =>
          refine ⟨Nat.le_succ_of_le prior.1, ?_⟩
          simp only [register, List.mem_cons, not_or]
          exact ⟨by omega, prior.2⟩
      | settle =>
          exact ⟨prior.1, fun enrolled => prior.2 (List.mem_filter.mp enrolled).1⟩
      | fault | validate | reconnect | account => exact prior

theorem exact_settlement_at_capacity_allows_a_fresh_registration {state : State Ticket} {scope : Nat}
    (full : state.registry.length = limit) (enrolled : scope ∈ state.registry)
    (offline : (state.access scope).phase = .offline)
    (terminal : namespaceClosed scope) (clear : Uncharged layout state scope) :
    Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed state .settle (forget state scope) ∧
    Step limit layout needs closeAllowed reserve expected authenticated namespaceClosed
      (forget state scope) .register (register (forget state scope)) := by
  refine ⟨.settle scope enrolled offline terminal clear, .register ?_⟩
  have notEqual : (state.registry.filter (· != scope)).length ≠ state.registry.length := by
    intro equal
    have excluded := List.length_filter_eq_length_iff.mp equal scope enrolled
    simp at excluded
  have bound := List.length_filter_le (· != scope) state.registry
  change (state.registry.filter (· != scope)).length < limit
  omega

omit [DecidableEq Ticket] in
theorem a_live_physical_borrow_blocks_namespace_forgetting {state : State Ticket} {version : Nat}
    (safe : Sound limit layout needs state) (borrowed : 0 < state.ledger.catalog.borrows version) :
    ¬ Uncharged layout state (layout.pool version) := by
  intro clear
  have paid := (SharedExtentAccounting.a_read_borrow_preserves_its_debit_without_a_live_root safe.funded borrowed).2
  exact clear (.inl ⟨version, paid, rfl⟩)

omit [DecidableEq Ticket] in
theorem unregistered_namespaces_have_no_live_physical_work {state : State Ticket} {version : Nat}
    (safe : Sound limit layout needs state) (unregistered : layout.pool version ∉ state.registry) :
    ¬ SharedExtentAccounting.PhysicalWork (state.ledger.provider version) := by
  intro work
  have paid := safe.funded.paid version work
  exact unregistered (safe.covered _ (.inl ⟨version, paid, rfl⟩))

#print axioms every_step_preserves_bounded_scoped_custody
#print axioms bounded_custody_survives_arbitrary_admitted_traces
#print axioms without_settlement_each_registration_consumes_another_slot
#print axioms a_previous_probe_cannot_authorize_after_another_failure
#print axioms fault_at_capacity_keeps_the_original_registry_and_ledger
#print axioms exact_validation_can_reopen_without_another_slot
#print axioms a_forgotten_issued_namespace_cannot_rejoin
#print axioms exact_settlement_at_capacity_allows_a_fresh_registration
#print axioms a_live_physical_borrow_blocks_namespace_forgetting
#print axioms unregistered_namespaces_have_no_live_physical_work

end PoolIncarnations
