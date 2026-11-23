import StandingReadRecovery

set_option warningAsError true

namespace StandingProviderSettlement

open StandingReadCredit (Window Fence)
open DeliveryBook (Entry)

variable {capacity limit : Nat} {Ticket : Type}

inductive Status where
  | unseen
  | using
  | terminal
  deriving DecidableEq

structure Operation (capacity limit : Nat) where
  slot : Fin limit
  entry : Entry capacity

structure Local (capacity limit : Nat) (Ticket : Type) where
  window : Window
  frozen : Option (Fence capacity limit Ticket)
  status : Nat → Status

structure Rules (capacity limit : Nat) (Ticket : Type) where
  chosen : Window → Operation capacity limit → Prop
  authenticatedFence : Fence capacity limit Ticket → Prop
  terminal : Window → Operation capacity limit → Prop

def update (status : Nat → Status) (serial : Nat) (value : Status) : Nat → Status :=
  fun query => if query = serial then value else status query

def SelectedBy (_fence : Fence capacity limit Ticket)
    (_operation : Operation capacity limit) : Prop :=
  _fence.book.rows _operation.slot = some _operation.entry

theorem a_selected_operation_names_the_exact_row
    (fence : Fence capacity limit Ticket) (operation : Operation capacity limit)
    (selected : SelectedBy fence operation) :
    fence.book.rows operation.slot = some operation.entry := by
  exact selected

def Member (pool : PoolState.Image Ticket) (allocation : PoolState.Identity) : Prop :=
  ∃ row ∈ pool.rows, row.identity = allocation

structure Eligible (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (operation : Operation capacity limit) : Prop where
  charged : Member pool provider.window.allocation
  scope : provider.window.serials.Contains operation.entry.borrow
  chosen : rules.chosen provider.window operation
  frozen : ∀ fence, provider.frozen = some fence → SelectedBy fence operation
  unseen : provider.status operation.entry.borrow.serial = .unseen

theorem positive_admission_requires_a_live_exact_allocation
    (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (operation : Operation capacity limit)
    (eligible : Eligible rules pool provider operation) : Member pool provider.window.allocation := by
  exact eligible.charged

theorem frozen_admission_requires_the_exact_selected_row
    (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (operation : Operation capacity limit)
    (fence : Fence capacity limit Ticket) (atSeal : provider.frozen = some fence)
    (eligible : Eligible rules pool provider operation) : fence.book.rows operation.slot = some operation.entry := by
  exact a_selected_operation_names_the_exact_row fence operation (eligible.frozen fence atSeal)

def MayEffect (pool : PoolState.Image Ticket) (provider : Local capacity limit Ticket)
    (rules : Rules capacity limit Ticket) (operation : Operation capacity limit) : Prop :=
  Member pool provider.window.allocation ∧ provider.window.serials.Contains operation.entry.borrow ∧
    rules.chosen provider.window operation ∧
    (∀ fence, provider.frozen = some fence → SelectedBy fence operation) ∧
    provider.status operation.entry.borrow.serial = .using

inductive Step (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket) :
    Local capacity limit Ticket → Local capacity limit Ticket → Prop where
  | installFence {before : Local capacity limit Ticket} (fence : Fence capacity limit Ticket)
      (known : rules.authenticatedFence fence) (same : fence.grant.window = before.window)
      (firstOrRetry : before.frozen = none ∨ before.frozen = some fence) :
      Step rules pool before {before with frozen := some fence}
  | start {before : Local capacity limit Ticket} (operation : Operation capacity limit)
      (ready : Eligible rules pool before operation) :
      Step rules pool before {before with status := update before.status operation.entry.borrow.serial .using}
  | finish {before : Local capacity limit Ticket} (operation : Operation capacity limit)
      (member : Member pool before.window.allocation)
      (scope : before.window.serials.Contains operation.entry.borrow)
      (chosen : rules.chosen before.window operation)
      (authentic : rules.terminal before.window operation) :
      Step rules pool before {before with status := update before.status operation.entry.borrow.serial .terminal}

inductive Trace (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket) :
    Local capacity limit Ticket → Local capacity limit Ticket → Prop where
  | same (state : Local capacity limit Ticket) : Trace rules pool state state
  | next {first before after : Local capacity limit Ticket} :
      Trace rules pool first before → Step rules pool before after → Trace rules pool first after

theorem exact_fence_admits_an_unobserved_choice_with_its_original_charge
    (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (operation : Operation capacity limit)
    (fence : Fence capacity limit Ticket) (known : rules.authenticatedFence fence)
    (same : fence.grant.window = provider.window) (opened : provider.frozen = none)
    (charged : Member pool provider.window.allocation) (scope : provider.window.serials.Contains operation.entry.borrow)
    (chosen : rules.chosen provider.window operation) (recorded : SelectedBy fence operation)
    (unseen : provider.status operation.entry.borrow.serial = .unseen) :
    ∃ gated started, Step rules pool provider gated ∧ Step rules pool gated started ∧
      MayEffect pool started rules operation := by
  let gated := {provider with frozen := some fence}
  let started := {gated with status := update provider.status operation.entry.borrow.serial .using}
  refine ⟨gated, started, .installFence fence known same (.inl opened), .start operation ?_,
    charged, scope, chosen, ?_, by simp [started, update]⟩
  · exact ⟨charged, scope, chosen, fun _ same => Option.some.inj same ▸ recorded, unseen⟩
  · exact fun _ same => Option.some.inj same ▸ recorded

theorem a_terminal_borrow_never_starts_or_takes_effect_again
    (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider after : Local capacity limit Ticket) (operation : Operation capacity limit)
    (stopped : provider.status operation.entry.borrow.serial = .terminal)
    (history : Trace rules pool provider after) :
    after.status operation.entry.borrow.serial = .terminal ∧
      ¬ Eligible rules pool after operation ∧ ¬ MayEffect pool after rules operation := by
  have persistent : after.status operation.entry.borrow.serial = .terminal := by
    induction history with
    | same => exact stopped
    | next _ event prior =>
        cases event with
        | installFence _ _ _ _ => exact prior
        | start other ready =>
            by_cases same : operation.entry.borrow.serial = other.entry.borrow.serial
            · have impossible := same.symm ▸ prior
              rw [ready.unseen] at impossible
              cases impossible
            · simp [update, same, prior]
        | finish other _ _ _ _ =>
            by_cases same : operation.entry.borrow.serial = other.entry.borrow.serial
            · simp [update, same]
            · simp [update, same, prior]
  refine ⟨persistent, ?_, ?_⟩
  · intro again
    have contradiction := persistent.symm.trans again.unseen
    cases contradiction
  · intro again
    have contradiction := persistent.symm.trans again.2.2.2.2
    cases contradiction

theorem an_installed_frozen_book_cannot_be_replaced_by_a_rival
    (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider after : Local capacity limit Ticket) (fence : Fence capacity limit Ticket)
    (bound : provider.frozen = some fence) (history : Trace rules pool provider after) :
    after.frozen = some fence := by
  induction history with
  | same => exact bound
  | next _ event prior =>
      cases event with
      | start _ _ | finish _ _ _ _ _ => exact prior
      | installFence _ _ _ candidate =>
          rcases candidate with empty | same
          · rw [prior] at empty
            cases empty
          · exact same.symm.trans prior

structure Drained (rules : Rules capacity limit Ticket) (provider : Local capacity limit Ticket)
    (fence : Fence capacity limit Ticket) : Prop where
  installed : provider.frozen = some fence
  authentic : rules.authenticatedFence fence
  original : fence.grant.window = provider.window
  done : ∀ slot entry, fence.book.rows slot = some entry →
    provider.window.serials.Contains entry.borrow → provider.status entry.borrow.serial = .terminal

theorem a_recovered_hidden_assignment_still_blocks_disposition
    (rules : Rules capacity limit Ticket) (provider : Local capacity limit Ticket)
    (fence : Fence capacity limit Ticket)
    (operation : Operation capacity limit) (recorded : fence.book.rows operation.slot = some operation.entry)
    (scope : provider.window.serials.Contains operation.entry.borrow)
    (outstanding : provider.status operation.entry.borrow.serial ≠ .terminal) :
    ¬ Drained rules provider fence := by
  intro drained
  exact outstanding (drained.done operation.slot operation.entry recorded scope)

theorem a_drained_original_window_permits_no_delayed_effect
    (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (fence : Fence capacity limit Ticket)
    (operation : Operation capacity limit) (drained : Drained rules provider fence) :
    ¬ MayEffect pool provider rules operation := by
  rintro ⟨_, scope, _, frozen, running⟩
  have selected := a_selected_operation_names_the_exact_row fence operation (frozen fence drained.installed)
  have terminal := drained.done operation.slot operation.entry selected scope
  rw [terminal] at running
  cases running

variable [DecidableEq Ticket]

omit [DecidableEq Ticket] in
private theorem row_keeps_provider_identity (row : PoolState.Row Ticket)
    (next : ProviderIOClosure.State Ticket) : ({row with provider := next} : PoolState.Row Ticket).identity = row.identity :=
  rfl

theorem an_issued_absent_allocation_cannot_reappear_in_one_pool_step
    (rules : PoolState.Rules Ticket) (before after : PoolState.Image Ticket)
    (allocation : PoolState.Identity)
    (issued : allocation.serial ≤ before.issued) (absent : ¬ Member before allocation)
    (step : PoolState.Step rules before after) :
    allocation.serial ≤ after.issued ∧ ¬ Member after allocation := by
  cases step with
  | prepare key binding _ =>
      refine ⟨Nat.le_trans issued (Nat.le_succ _), ?_⟩
      rintro ⟨row, found, exact⟩
      rcases List.mem_cons.mp found with rfl | retained
      · have equal := congrArg PoolState.Identity.serial exact
        change before.issued + 1 = allocation.serial at equal
        omega
      · exact absent ⟨row, retained, exact⟩
  | ordinary _ _ | gate _ _ | fence _ _ _ _ _ => exact ⟨issued, absent⟩
  | @provider row next earlier later exactRows _ _ =>
      refine ⟨issued, ?_⟩
      rintro ⟨other, found, exact⟩
      rcases List.mem_append.mp found with older | newly
      · exact absent ⟨other, by rw [exactRows]; exact List.mem_append_left _ older, exact⟩
      · rcases List.mem_cons.mp newly with rfl | younger
        · exact absent ⟨row, by rw [exactRows]; exact List.mem_append_right _ List.mem_cons_self,
            (row_keeps_provider_identity row next).symm.trans exact⟩
        · exact absent ⟨other, by rw [exactRows]; exact List.mem_append_right _ (List.mem_cons_of_mem _ younger), exact⟩
  | @refund row earlier later exactRows _ _ =>
      refine ⟨issued, ?_⟩
      rintro ⟨other, found, exact⟩
      rcases List.mem_append.mp found with older | younger
      · exact absent ⟨other, by rw [exactRows]; exact List.mem_append_left _ older, exact⟩
      · exact absent ⟨other, by rw [exactRows]; exact List.mem_append_right _ (List.mem_cons_of_mem _ younger), exact⟩

theorem a_refunded_old_allocation_stays_refused_through_arbitrary_pool_turnover
    (rules : Rules capacity limit Ticket) (poolRules : PoolState.Rules Ticket)
    (before after : PoolState.Image Ticket) (provider : Local capacity limit Ticket)
    (issued : provider.window.allocation.serial ≤ before.issued)
    (absent : ¬ Member before provider.window.allocation)
    (history : PoolState.Trace poolRules before after) :
    ∀ operation, ¬ Eligible rules after provider operation ∧ ¬ MayEffect after provider rules operation := by
  have never : provider.window.allocation.serial ≤ after.issued ∧ ¬ Member after provider.window.allocation := by
    induction history with
    | same => exact ⟨issued, absent⟩
    | next _ step prior =>
        exact an_issued_absent_allocation_cannot_reappear_in_one_pool_step poolRules _ _
          provider.window.allocation prior.1 prior.2 step
  intro operation
  exact ⟨fun eligible => never.2 (positive_admission_requires_a_live_exact_allocation rules after provider operation eligible),
    fun effect => never.2 effect.1⟩

structure Returnable (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (row : PoolState.Row Ticket)
    (earlier later : List (PoolState.Row Ticket)) : Prop where
  record : pool.rows = earlier ++ row :: later
  allocation : row.identity = provider.window.allocation
  drained : ∃ fence, Drained rules provider fence
  closed : CopyFence.Closed pool.gate row.key
  absent : row.provider.erased = true

omit [DecidableEq Ticket] in
noncomputable def refundWindow (rules : Rules capacity limit Ticket) (pool : PoolState.Image Ticket)
    (provider : Local capacity limit Ticket) (row : PoolState.Row Ticket)
    (earlier later : List (PoolState.Row Ticket)) : Option (PoolState.Image Ticket) := by
  classical
  exact if Returnable rules pool provider row earlier later then
    some {pool with rows := earlier ++ later}
  else none

theorem a_refund_decision_requires_the_frozen_drain_and_original_physical_absence
    (rules : Rules capacity limit Ticket) (poolRules : PoolState.Rules Ticket)
    (pool after : PoolState.Image Ticket) (provider : Local capacity limit Ticket)
    (row : PoolState.Row Ticket) (earlier later : List (PoolState.Row Ticket))
    (refunded : refundWindow rules pool provider row earlier later = some after) :
    Returnable rules pool provider row earlier later ∧ PoolState.Step poolRules pool after := by
  unfold refundWindow at refunded
  split at refunded
  · next valid =>
      cases refunded
      exact ⟨valid, .refund earlier later valid.record valid.closed valid.absent⟩
  · contradiction

theorem an_exact_refund_at_capacity_returns_the_old_row_without_requiring_new_space
    (rules : Rules capacity limit Ticket) (poolRules : PoolState.Rules Ticket)
    (pool : PoolState.Image Ticket) (provider : Local capacity limit Ticket)
    (row : PoolState.Row Ticket) (earlier later : List (PoolState.Row Ticket))
    (safe : PoolState.Sound poolRules pool) (fullyCharged : PoolState.used poolRules pool = poolRules.limit)
    (record : pool.rows = earlier ++ row :: later) (same : row.identity = provider.window.allocation)
    (unique : ∀ other ∈ pool.rows, other.identity = provider.window.allocation → other = row)
    (disjoint : row ∉ earlier ++ later)
    (fence : Fence capacity limit Ticket) (settled : Drained rules provider fence) (closed : CopyFence.Closed pool.gate row.key)
    (erased : row.provider.erased = true) :
    ∃ after, refundWindow rules pool provider row earlier later = some after ∧
      PoolState.Step poolRules pool after ∧ PoolState.Sound poolRules after ∧
      PoolState.used poolRules after < poolRules.limit ∧ ¬ Member after provider.window.allocation ∧
      provider.window.allocation.serial ≤ after.issued ∧
      ProviderIOClosure.StableAbsence row.provider ∧ Drained rules provider fence := by
  let after := {pool with rows := earlier ++ later}
  have admitted : refundWindow rules pool provider row earlier later = some after :=
    ite_eq_left ⟨record, same, ⟨fence, settled⟩, closed, erased⟩
  have refund := (a_refund_decision_requires_the_frozen_drain_and_original_physical_absence rules poolRules
    pool after provider row earlier later admitted).2
  have member : row ∈ pool.rows := by simp [record]
  have known := PoolState.a_physical_refund_requires_its_own_provider_absence safe member erased
  have uncharged : ¬ Member after provider.window.allocation := by
    rintro ⟨other, found, exact⟩
    have formerly : other ∈ pool.rows := by
      rw [record]
      exact (List.mem_append.mp found).elim
        (List.mem_append_left _) (fun found => List.mem_append_right _ (List.mem_cons_of_mem _ found))
    have exactRow := unique other formerly exact
    exact disjoint (exactRow ▸ found)
  have original := fullyCharged
  have positive := poolRules.positive row.binding
  simp [PoolState.used, PoolState.charges, record] at original
  have smaller : PoolState.used poolRules after < poolRules.limit := by
    simp [after, PoolState.used, PoolState.charges]
    omega
  exact ⟨after, admitted, refund, PoolState.every_local_decision_preserves_capacity_and_exact_paid_grants safe refund,
    smaller, uncharged, by simpa [after, ← same, PoolState.Row.identity] using safe.known row member, known, settled⟩

omit [DecidableEq Ticket] in
theorem a_chosen_seal_installs_the_exact_original_fence_without_resetting_provider_status
    {width slots : Nat} {Payload : Type}
    (rules : Rules capacity limit Ticket) (ordered : StandingReadCredit.Rules width slots capacity limit Payload Ticket)
    (lineage : ChosenReplay.Lineage)
    (source sealed : StandingReadCredit.State slots capacity limit Payload Ticket)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key slots) (vector : RealizedSource.Vector)
    (evidence : JointSource.SealEvidence) (ticket : Ticket)
    (store : StandingReadRecovery.SealStore width capacity limit)
    (archive : EnvelopeCodec.Field width → Option Ticket) (anchor : EnvelopeRecovery.Anchor width)
    (original : StandingReadCredit.StandingGrant Ticket) (current : source.current = some original)
    (fence : Fence capacity limit Ticket)
    (chosen : StandingReadRecovery.chooseSeal ordered lineage source writer key vector evidence ticket store archive anchor =
      some (sealed, some fence))
    (certified : rules.authenticatedFence fence)
    (pool : PoolState.Image Ticket) (provider : Local capacity limit Ticket)
    (sameProvider : provider.window = original.window) (unfenced : provider.frozen = none) :
    fence.book = sealed.retained.deliveries ∧
      Step rules pool provider {provider with frozen := some fence} := by
  obtain ⟨_, _, exactFence, _, _, _, _⟩ :=
    StandingReadRecovery.a_chosen_seal_preserves_the_watermark_and_fences_the_original_window
      ordered lineage source sealed writer key vector evidence ticket store archive anchor (some fence) chosen
  have exact : fence = ⟨original, RetainedDelivery.position sealed.retained, sealed.retained.deliveries⟩ := by
    simpa [current] using exactFence
  refine ⟨congrArg Fence.book exact, .installFence fence certified ?_ (.inl unfenced)⟩
  rw [exact, sameProvider]

theorem refund_allows_permanent_retirement_without_retaining_a_tombstone
    (rules : Rules capacity limit Ticket) (poolRules : PoolState.Rules Ticket)
    (pool : PoolState.Image Ticket) (provider : Local capacity limit Ticket)
    (row : PoolState.Row Ticket) (earlier later : List (PoolState.Row Ticket))
    (safe : PoolState.Sound poolRules pool) (fullyCharged : PoolState.used poolRules pool = poolRules.limit)
    (record : pool.rows = earlier ++ row :: later) (same : row.identity = provider.window.allocation)
    (unique : ∀ other ∈ pool.rows, other.identity = provider.window.allocation → other = row)
    (disjoint : row ∉ earlier ++ later)
    (fence : Fence capacity limit Ticket) (settled : Drained rules provider fence)
    (closed : CopyFence.Closed pool.gate row.key) (erased : row.provider.erased = true) :
    ∃ after, PoolState.Step poolRules pool after ∧ PoolState.used poolRules after < poolRules.limit ∧
      ∀ future, PoolState.Trace poolRules after future →
        ∀ operation, ¬ Eligible rules future provider operation ∧ ¬ MayEffect future provider rules operation := by
  obtain ⟨after, _, refund, _, room, absent, issued, _, _⟩ :=
    an_exact_refund_at_capacity_returns_the_old_row_without_requiring_new_space rules poolRules
      pool provider row earlier later safe fullyCharged record same unique disjoint fence settled closed erased
  exact ⟨after, refund, room, fun future history =>
    a_refunded_old_allocation_stays_refused_through_arbitrary_pool_turnover
      rules poolRules after future provider issued absent history⟩

#print axioms a_selected_operation_names_the_exact_row
#print axioms positive_admission_requires_a_live_exact_allocation
#print axioms frozen_admission_requires_the_exact_selected_row
#print axioms exact_fence_admits_an_unobserved_choice_with_its_original_charge
#print axioms a_terminal_borrow_never_starts_or_takes_effect_again
#print axioms an_installed_frozen_book_cannot_be_replaced_by_a_rival
#print axioms a_recovered_hidden_assignment_still_blocks_disposition
#print axioms a_drained_original_window_permits_no_delayed_effect
#print axioms an_issued_absent_allocation_cannot_reappear_in_one_pool_step
#print axioms a_refunded_old_allocation_stays_refused_through_arbitrary_pool_turnover
#print axioms a_refund_decision_requires_the_frozen_drain_and_original_physical_absence
#print axioms an_exact_refund_at_capacity_returns_the_old_row_without_requiring_new_space

#print axioms a_chosen_seal_installs_the_exact_original_fence_without_resetting_provider_status
#print axioms refund_allows_permanent_retirement_without_retaining_a_tombstone

end StandingProviderSettlement
