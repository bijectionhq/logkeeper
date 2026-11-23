import CopyFence
import SharedExtentAccounting
import UnifiedSource

set_option warningAsError true

namespace LatePrepare

open ChannelLifecycle (Key Authority Store)
open RegistrationRecovery (Binding)
open SnapshotAdmission (setSlot)
open SharedExtentAccounting (Layout)

variable {Ticket : Type}

structure Rules (Ticket : Type) where
  authority : Authority
  extent : Key → Nat
  singleOwner : ∀ first second, extent first = extent second → first = second
  chosenAbort : Key → Binding → Prop
  layout : Layout Nat
  needs : SharedCustody.Dependencies
  closeAllowed : Nat → Prop
  reserve : ProviderIOClosure.Custody Ticket → Prop

def gateRules (rules : Rules Ticket) : Authority :=
  {rules.authority with mayRelease := rules.chosenAbort}

structure World (Ticket : Type) where
  gate : Store
  ledger : SharedExtentAccounting.State Nat Ticket

def Sound (rules : Rules Ticket) (world : World Ticket) : Prop :=
  SharedExtentAccounting.Sound rules.layout rules.needs world.ledger ∧
    ∀ key binding, world.gate.grants key = some binding → rules.extent key ∈ world.ledger.debits

def prepare (world : World Ticket) (key : Key) (binding : Binding) (version : Nat) : World Ticket :=
  ⟨ChannelLifecycle.setGrant world.gate key (some binding),
    {world.ledger with
      debits := version :: world.ledger.debits
      issued := version
      provider := setSlot world.ledger.provider version ProviderIOClosure.initial
      opening := setSlot world.ledger.opening version true}⟩

structure Adm (rules : Rules Ticket) (world : World Ticket) (key : Key) (binding : Binding) : Prop where
  planned : rules.authority.planned key binding
  gateRoom : rules.authority.mayPin world.gate
  openScope : ChannelLifecycle.decideAcquire world.gate key binding = .admit
  correctPool : rules.layout.pool (rules.extent key) = key.handle.custodian
  fresh : rules.extent key = world.ledger.issued + 1
  empty : world.ledger.catalog.physical (rules.extent key) = false
  room : ∀ pool, SharedExtentAccounting.Used rules.layout world.ledger pool +
    SharedExtentAccounting.allocationBytes rules.layout pool (rules.extent key) ≤ rules.layout.limit pool

variable [DecidableEq Ticket]

abbrev Physical (rules : Rules Ticket) :=
  SharedExtentAccounting.Step rules.layout rules.needs rules.closeAllowed rules.reserve

inductive Step (rules : Rules Ticket) : World Ticket → World Ticket → Prop
  | prepare {world} (key : Key) (binding : Binding) (admit : Adm rules world key binding) :
      Step rules world (LatePrepare.prepare world key binding (rules.extent key))
  | gate {world next} (change : ChannelLifecycle.Step (gateRules rules) world.gate next)
      (preservesGrants : next.grants = world.gate.grants) :
      Step rules world {world with gate := next}
  | physical {world next} (change : Physical rules world.ledger next)
      (samePreparedDebits : ∀ key, rules.extent key ∈ next.debits ↔ rules.extent key ∈ world.ledger.debits)
      (startsFromGrant : ∀ key ticket,
        (world.ledger.provider (rules.extent key)).status ticket = .unused →
        (next.provider (rules.extent key)).status ticket = .pending →
        ∃ binding, world.gate.grants key = some binding) :
      Step rules world {world with ledger := next}
  | fence {world} (key : Key) (binding : Binding) (chosen : rules.chosenAbort key binding)
      (issued : key.handle.nonce ≤ world.gate.issued)
      (compatible : world.gate.grants key = none ∨ world.gate.grants key = some binding) :
      Step rules world {world with gate := ChannelLifecycle.releaseGrant world.gate key}
  | refund {world} (key : Key) (closed : CopyFence.Closed world.gate key)
      (erased : (world.ledger.provider (rules.extent key)).erased = true) :
      Step rules world {world with ledger := {world.ledger with
        debits := world.ledger.debits.filter (· != rules.extent key)}}

inductive Trace (rules : Rules Ticket) : World Ticket → World Ticket → Prop
  | same (world : World Ticket) : Trace rules world world
  | next {first before after} : Trace rules first before → Step rules before after → Trace rules first after

theorem every_step_projects_to_exact_gate_and_physical_decisions
    {rules : Rules Ticket} {before after : World Ticket} (event : Step rules before after) :
    (before.gate = after.gate ∨ ChannelLifecycle.Step (gateRules rules) before.gate after.gate) ∧
    (before.ledger = after.ledger ∨ Physical rules before.ledger after.ledger) := by
  cases event with
  | prepare key binding admit =>
      exact ⟨.inr (.acquire key binding admit.planned admit.gateRoom admit.openScope),
        .inr (.allocate (rules.extent key) admit.fresh admit.empty admit.room)⟩
  | gate change _ => exact ⟨.inr change, .inl rfl⟩
  | physical change _ _ => exact ⟨.inl rfl, .inr change⟩
  | fence key binding chosen _ compatible => exact ⟨.inr (.release key binding compatible chosen), .inl rfl⟩
  | refund key _ erased => exact ⟨.inl rfl, .inr (.refund (rules.extent key) (rules.extent key) ⟨rfl, erased⟩)⟩

theorem a_late_preparation_has_the_same_exact_backing_and_retry_result
    (rules : Rules Ticket) (world : World Ticket) (key : Key) (binding : Binding)
    (admit : Adm rules world key binding) :
    let after := prepare world key binding (rules.extent key)
    Step rules world after ∧ after.gate.grants key = some binding ∧
      rules.extent key ∈ after.ledger.debits ∧
      ChannelLifecycle.decideAcquire after.gate key binding = .replay := by
  have held : (prepare world key binding (rules.extent key)).gate.grants key = some binding := by
    simp [prepare, ChannelLifecycle.setGrant]
  exact ⟨.prepare key binding admit, held, List.mem_cons_self,
    (ChannelLifecycle.existing_grant_retries_without_channel_metadata held (other := binding)).1⟩

theorem every_step_preserves_capacity_and_pays_for_every_grant
    {rules : Rules Ticket} {before after : World Ticket}
    (safe : Sound rules before) (event : Step rules before after) : Sound rules after := by
  have physical : SharedExtentAccounting.Sound rules.layout rules.needs after.ledger := by
    rcases (every_step_projects_to_exact_gate_and_physical_decisions event).2 with same | step
    · exact same ▸ safe.1
    · exact SharedExtentAccounting.numeric_and_custody_invariants_hold_after_each_step safe.1 step
  refine ⟨physical, ?_⟩
  intro query value held
  cases event with
  | prepare key binding _ =>
      by_cases same : query = key
      · subst query
        exact List.mem_cons_self
      · have prior : before.gate.grants query = some value := by
          simpa [prepare, ChannelLifecycle.setGrant, same] using held
        exact List.mem_cons_of_mem _ (safe.2 query value prior)
  | gate _ grants =>
      exact safe.2 query value (by simpa only [grants] using held)
  | physical _ sameDebits _ =>
      exact (sameDebits query).2 (safe.2 query value held)
  | fence key _ _ _ _ =>
      have effects := ChannelLifecycle.release_clears_only_the_exact_key before.gate key
      by_cases same : query = key
      · subst query
        rw [effects.1] at held
        cases held
      · exact safe.2 query value ((effects.2 query same).symm.trans held)
  | refund key closed _ =>
      have distinct : rules.extent query ≠ rules.extent key := by
        intro same
        have equal := rules.singleOwner query key same
        subst query
        rw [closed.empty] at held
        cases held
      exact List.mem_filter.mpr ⟨safe.2 query value held, by simpa using distinct⟩

theorem arbitrary_interleavings_keep_exact_grants_and_physical_work_paid
    {rules : Rules Ticket} {first last : World Ticket}
    (safe : Sound rules first) (trace : Trace rules first last) : Sound rules last := by
  induction trace with
  | same => exact safe
  | next _ step prior => exact every_step_preserves_capacity_and_pays_for_every_grant prior step

theorem a_chosen_exact_abort_fences_even_an_empty_scope
    (rules : Rules Ticket) (world : World Ticket) (key : Key) (binding : Binding)
    (chosen : rules.chosenAbort key binding) (issued : key.handle.nonce ≤ world.gate.issued)
    (compatible : world.gate.grants key = none ∨ world.gate.grants key = some binding) :
    let after := {world with gate := ChannelLifecycle.releaseGrant world.gate key}
    Step rules world after ∧ CopyFence.Closed after.gate key ∧ after.ledger = world.ledger := by
  exact ⟨.fence key binding chosen issued compatible, CopyFence.releasing_an_issued_key_establishes_a_fence issued, rfl⟩

theorem a_fenced_scope_stays_closed_through_all_interleavings
    {rules : Rules Ticket} {first last : World Ticket} {key : Key}
    (closed : CopyFence.Closed first.gate key) (trace : Trace rules first last) : CopyFence.Closed last.gate key := by
  induction trace with
  | same => exact closed
  | next _ step prior =>
      rcases (every_step_projects_to_exact_gate_and_physical_decisions step).1 with same | localStep
      · exact same ▸ prior
      · exact CopyFence.a_copy_fence_survives_every_custodian_step prior localStep

theorem a_fenced_refunded_scope_cannot_reacquire_its_debit
    {rules : Rules Ticket} {first last : World Ticket} {key : Key}
    (closed : CopyFence.Closed first.gate key) (refunded : rules.extent key ∉ first.ledger.debits)
    (trace : Trace rules first last) : rules.extent key ∉ last.ledger.debits := by
  induction trace with
  | same => exact refunded
  | next earlier event previous =>
      have refusal := a_fenced_scope_stays_closed_through_all_interleavings closed earlier
      cases event with
      | prepare other binding admit =>
          have distinct : rules.extent key ≠ rules.extent other := by
            intro same
            have exactKey := rules.singleOwner key other same
            subst other
            have denied := admit.openScope
            rw [CopyFence.closed_copy_refuses_every_binding refusal binding] at denied
            cases denied
          intro member
          exact (List.mem_cons.mp member).elim distinct previous
      | gate _ _ => exact previous
      | physical _ sameDebits _ => exact fun held => previous ((sameDebits key).1 held)
      | fence _ _ _ _ _ => exact previous
      | refund _ _ _ => exact fun held => previous (List.mem_filter.mp held).1

theorem a_closed_preparation_issues_no_new_provider_ticket
    {rules : Rules Ticket} {before after : World Ticket} {key : Key} {ticket : Ticket}
    (closed : CopyFence.Closed before.gate key)
    (event : Step rules before after)
    (unused : (before.ledger.provider (rules.extent key)).status ticket = .unused) :
    (after.ledger.provider (rules.extent key)).status ticket ≠ .pending := by
  intro pending
  cases event with
  | prepare other binding _ =>
      by_cases same : rules.extent key = rules.extent other
      · simp [prepare, setSlot, same, ProviderIOClosure.initial] at pending
      · simp [prepare, setSlot, same, unused] at pending
  | physical _ _ starts =>
      obtain ⟨value, held⟩ := starts key ticket unused pending
      rw [closed.empty] at held
      cases held
  | gate _ _ | fence _ _ _ _ _ | refund _ _ _ =>
      rw [unused] at pending
      cases pending

omit [DecidableEq Ticket] in
theorem a_fenced_scope_can_settle_only_against_absence_or_paid_custody
    {rules : Rules Ticket} {world : World Ticket} {key : Key}
    (safe : Sound rules world) (closed : CopyFence.Closed world.gate key)
    (disposition : rules.extent key ∉ world.ledger.debits ∨
      rules.extent key ∈ world.ledger.debits ∧
        ∃ record, (world.ledger.provider (rules.extent key)).custodian = some record) :
    (∀ binding, ChannelLifecycle.decideAcquire world.gate key binding = .refuse) ∧
    (¬ SharedExtentAccounting.PhysicalWork (world.ledger.provider (rules.extent key)) ∨
      rules.extent key ∈ world.ledger.debits ∧
        ∃ record, (world.ledger.provider (rules.extent key)).custodian = some record ∧
          ProviderIOClosure.Covers (world.ledger.provider (rules.extent key)) record) := by
  refine ⟨CopyFence.closed_copy_refuses_every_binding closed, ?_⟩
  rcases disposition with absent | ⟨charged, record, owns⟩
  · exact .inl (fun work => absent (safe.1.paid (rules.extent key) work))
  · exact .inr ⟨charged, record, owns, (safe.1.providerSound (rules.extent key)).custody record owns⟩

omit [DecidableEq Ticket] in
theorem a_physical_refund_requires_stable_absence_of_the_exact_extent
    {rules : Rules Ticket} {world : World Ticket} {key : Key}
    (safe : Sound rules world)
    (evidence : SharedExtentAccounting.CanRefund world.ledger (rules.extent key) (rules.extent key)) :
    ProviderIOClosure.StableAbsence (world.ledger.provider (rules.extent key)) :=
  (safe.1.providerSound (rules.extent key)).erasure evidence.2

#print axioms every_step_projects_to_exact_gate_and_physical_decisions
#print axioms a_late_preparation_has_the_same_exact_backing_and_retry_result
#print axioms every_step_preserves_capacity_and_pays_for_every_grant
#print axioms arbitrary_interleavings_keep_exact_grants_and_physical_work_paid
#print axioms a_chosen_exact_abort_fences_even_an_empty_scope
#print axioms a_fenced_scope_stays_closed_through_all_interleavings
#print axioms a_fenced_refunded_scope_cannot_reacquire_its_debit
#print axioms a_closed_preparation_issues_no_new_provider_ticket
#print axioms a_fenced_scope_can_settle_only_against_absence_or_paid_custody
#print axioms a_physical_refund_requires_stable_absence_of_the_exact_extent

end LatePrepare
