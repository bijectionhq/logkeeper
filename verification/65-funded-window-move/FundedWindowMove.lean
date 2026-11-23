import ChosenReplay

set_option warningAsError true

namespace FundedWindowMove

open SnapshotAdmission (setSlot)

variable {slots : Nat} {Payload Ticket : Type}

structure Key (slots : Nat) where
  stream : Nat
  move : SourceOutcomes.Key slots
  deriving DecidableEq

structure Plan where
  target : Kernel.Placement
  window : Nat
  recovery : List Nat

def Plan.extents (plan : Plan) : List Nat :=
  plan.window :: plan.recovery

structure Rules (slots : Nat) (Payload Ticket : Type) where
  append : FundedAppend.Rules slots Payload Ticket
  plan : Key slots → Plan
  owner : Nat → Option (Key slots)

structure State (slots : Nat) (Payload Ticket : Type) where
  appends : FundedAppend.State slots Payload Ticket
  held : Nat → Option (Key slots)
  installed : Key slots → Bool

def source (state : State slots Payload Ticket) (key : Key slots) :
    FundedAppend.Source slots Payload :=
  state.appends.regional.streams key.stream

def layout (rules : Rules slots Payload Ticket) : SharedExtentAccounting.Layout Nat :=
  rules.append.regional.layout

def intent (rules : Rules slots Payload Ticket) (key : Key slots) : FundedSeal.Intent Nat :=
  let plan := rules.plan key
  ⟨key.move.serial, plan.target, fun pool => SharedExtentAccounting.charges (layout rules) pool plan.extents⟩

def Holds (state : State slots Payload Ticket) (version : Nat) : Prop :=
  version ∈ state.appends.regional.pools.ledger.debits

structure Complete (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (key : Key slots) : Prop where
  unique : (rules.plan key).extents.Nodup
  owners : ∀ version ∈ (rules.plan key).extents, rules.owner version = some key
  held : ∀ version ∈ (rules.plan key).extents, state.held version = some key
  paid : ∀ version ∈ (rules.plan key).extents, Holds state version

def PreparedReceipt (rules : Rules slots Payload Ticket) (key : Key slots) (pool : Nat) :
    FundedSeal.Receipt Nat :=
  ⟨intent rules key, pool, (intent rules key).needs pool⟩

def ExactReceipts (rules : Rules slots Payload Ticket) (key : Key slots)
    (received : List (FundedSeal.Receipt Nat)) : Prop :=
  ∀ pool, 0 < (intent rules key).needs pool →
    PreparedReceipt rules key pool ∈ received ∧
      (rules.append.regional.source key.stream).preparedReceipt (PreparedReceipt rules key pool)

theorem the_existing_seal_uses_the_exact_pointwise_receipts
    {rules : Rules slots Payload Ticket} {key : Key slots} {received : List (FundedSeal.Receipt Nat)}
    (valid : ExactReceipts rules key received) :
    UnifiedSource.full (rules.append.regional.source key.stream) received (intent rules key) := by
  intro pool required
  exact ⟨PreparedReceipt rules key pool, valid pool required, rfl, rfl, rfl⟩

def BindsPlan (rules : Rules slots Payload Ticket) (key : Key slots)
    (anchor : UnifiedSource.Anchor slots Nat) : Prop :=
  anchor.decision.key = key.move ∧ anchor.decision.binding = intent rules key ∧
  anchor.decision.result = .committed

def CanSettle (state : State slots Payload Ticket) (key : Key slots) : Prop :=
  state.installed key = true ∨
    ∃ result, SourceOutcomes.lookup (source state key).core.book key.move = some result ∧
      result.result = some .canceled

noncomputable def applySource (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (key : Key slots) (command : UnifiedSource.Command slots Nat Payload Ticket) :
    FundedAppend.State slots Payload Ticket × List (UnifiedSource.Reply Payload) :=
  let result := UnifiedSource.replay (rules.append.regional.limits key.stream)
    (rules.append.regional.source key.stream) (source state key) [command]
  ({state.appends with regional := {state.appends.regional with
    streams := setSlot state.appends.regional.streams key.stream result.1}}, result.2)

def destinationWriter (rules : Rules slots Payload Ticket) (key : Key slots)
    (proof : UnifiedSource.Installation slots Nat Payload Ticket) : Kernel.Writer :=
  {proof.writer with placement := (rules.plan key).target}

structure WindowReady (rules : Rules slots Payload Ticket) (state : FundedAppend.State slots Payload Ticket)
    (key : Key slots) (writer : Kernel.Writer) : Prop where
  owned : rules.append.owner (rules.plan key).window = key.stream
  newer : state.book.latest key.stream < (rules.plan key).window
  unused : state.book.windows (rules.plan key).window = none
  writer : (state.regional.streams key.stream).core.stream.authority = .active writer
  eligible : PoolIncarnations.Eligible state.regional.pools ((layout rules).pool (rules.plan key).window)
  physical : (state.regional.pools.ledger.provider (rules.plan key).window).present = true

theorem a_prepared_charge_supplies_the_window_grant
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    {proof : UnifiedSource.Installation slots Nat Payload Ticket} (complete : Complete rules state key)
    (ready : WindowReady rules (applySource rules state key (.activate proof)).1
      key (destinationWriter rules key proof)) :
    FundedAppend.PublishWindow rules.append (applySource rules state key (.activate proof)).1
      key.stream (rules.plan key).window (destinationWriter rules key proof) := by
  exact ⟨ready.owned, ready.newer, ready.unused, ready.writer, ready.eligible,
    complete.paid _ List.mem_cons_self, ready.physical⟩

abbrev MoveRow :=
  SourceOutcomes.Row (FundedSeal.Intent Nat) (SettlementComposition.Participant Nat)

structure SealReady (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (key : Key slots) (writer : Kernel.Writer) (row : MoveRow) : Prop where
  ready : UnifiedSource.Ready (source state key).core key.move row
  matchesPlan : row.binding = intent rules key
  authorized : (source state key).core.stream.authority = .active writer
  advances : writer.placement.generation < row.binding.target.generation
  relocates : writer.placement.group ≠ row.binding.target.group

theorem a_complete_vector_binds_the_original_ordered_seal
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    {writer : Kernel.Writer} {row : MoveRow} {received : List (FundedSeal.Receipt Nat)}
    (ready : SealReady rules state key writer row) (checked : ExactReceipts rules key received) :
    let after := {state with appends := (applySource rules state key (.fundedSeal writer key.move received)).1}
    let anchor : UnifiedSource.Anchor slots Nat :=
      ⟨⟨key.move, row.binding, .committed⟩, (source state key).position + 1⟩
    (source after key).core.handoff = some anchor ∧ BindsPlan rules key anchor := by
  have receipts : UnifiedSource.full (rules.append.regional.source key.stream) received row.binding :=
    ready.matchesPlan.symm ▸ the_existing_seal_uses_the_exact_pointwise_receipts checked
  have binding := UnifiedSource.a_successful_funded_seal_records_both_effects_at_one_position
    (rules.append.regional.limits key.stream) (rules.append.regional.source key.stream)
    (source state key).core ((source state key).position + 1) writer key.move row received
    ready.ready ready.authorized ready.advances ready.relocates receipts
  exact ⟨by simpa [source, applySource, setSlot, UnifiedSource.replay] using binding.2.2,
    rfl, ready.matchesPlan, rfl⟩

noncomputable def publish (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (key : Key slots) (proof : UnifiedSource.Installation slots Nat Payload Ticket) :
    State slots Payload Ticket :=
  let activated := (applySource rules state key (.activate proof)).1
  {state with
    appends := FundedAppend.openWindow activated key.stream (rules.plan key).window (destinationWriter rules key proof)
    installed := fun query => if query = key then true else state.installed query}

def ClaimsPaid (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) : Prop :=
  ∀ version key, state.held version = some key → rules.owner version = some key ∧ Holds state version

structure Sound (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) : Prop where
  regional : RegionalRetirement.Sound rules.append.regional state.appends.regional
  windows : FundedAppend.Funded rules.append state.appends
  claims : ClaimsPaid rules state

variable [DecidableEq Ticket]

inductive Step (rules : Rules slots Payload Ticket) :
    State slots Payload Ticket → State slots Payload Ticket → Prop
  | ordinary {state next} (change : FundedAppend.Step rules.append state.appends next)
      (protects : ∀ version key, state.held version = some key → version ∈ next.regional.pools.ledger.debits)
      (noHandoff : ∀ stream, (next.regional.streams stream).core.handoff =
        (state.appends.regional.streams stream).core.handoff)
      (noNewOwnedWindow : ∀ version key, rules.owner version = some key →
        next.book.windows version ≠ none → state.appends.book.windows version ≠ none) :
      Step rules state {state with appends := next}
  | claim {state} (key : Key slots) (version : Nat)
      (member : version ∈ (rules.plan key).extents) (owned : rules.owner version = some key)
      (paid : Holds state version) (vacant : state.held version = none)
      (notPublished : state.appends.book.windows version = none)
      (pending : (source state key).core.pending = some key.move) :
      Step rules state {state with held := setSlot state.held version (some key)}
  | chooseSeal {state} (key : Key slots) (writer : Kernel.Writer)
      (received : List (FundedSeal.Receipt Nat)) (row : MoveRow)
      (fullyOwned : Complete rules state key)
      (checked : ExactReceipts rules key received)
      (ready : SealReady rules state key writer row) :
      Step rules state {state with appends := (applySource rules state key (.fundedSeal writer key.move received)).1}
  | install {state} (key : Key slots) (proof : UnifiedSource.Installation slots Nat Payload Ticket)
      (fullyOwned : Complete rules state key) (bound : BindsPlan rules key proof.anchor)
      (accepted : (applySource rules state key (.activate proof)).2 = [.accepted])
      (ready : WindowReady rules (applySource rules state key (.activate proof)).1
        key (destinationWriter rules key proof)) :
      Step rules state (publish rules state key proof)
  | settle {state} (key : Key slots) (version : Nat) (held : state.held version = some key)
      (terminal : CanSettle state key)
      (absent : (state.appends.regional.pools.ledger.provider version).erased = true) :
      Step rules state {state with held := setSlot state.held version none}

inductive Trace (rules : Rules slots Payload Ticket) :
    State slots Payload Ticket → State slots Payload Ticket → Prop
  | same (state : State slots Payload Ticket) : Trace rules state state
  | next {first before after} : Trace rules first before → Step rules before after → Trace rules first after

private theorem source_command_projects
    (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) (key : Key slots)
    (command : UnifiedSource.Command slots Nat Payload Ticket) :
    RegionalRetirement.Step rules.append.regional state.appends.regional
      (applySource rules state key command).1.regional :=
  .ordered key.stream command

theorem the_shared_move_machine_preserves_stream_pool_and_window_bounds
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket}
    (safe : Sound rules state) (event : Step rules state next) : Sound rules next := by
  cases event with
  | ordinary change protects _ _ =>
      rcases FundedAppend.every_funded_step_refines_the_regional_authority change with same | regional
      · exact ⟨same ▸ safe.regional, FundedAppend.regional_steps_preserve_every_window_charge safe.windows change,
          fun version key held => ⟨(safe.claims version key held).1, protects version key held⟩⟩
      · exact ⟨RegionalRetirement.the_regional_machine_preserves_stream_and_pool_bounds safe.regional regional,
          FundedAppend.regional_steps_preserve_every_window_charge safe.windows change,
          fun version key held => ⟨(safe.claims version key held).1, protects version key held⟩⟩
  | claim key version _ owner paid _ _ _ =>
      refine ⟨safe.regional, safe.windows, ?_⟩
      intro query claimant held
      by_cases same : query = version
      · subst query
        simp [setSlot] at held
        subst claimant
        exact ⟨owner, paid⟩
      · exact safe.claims query claimant (by simpa [setSlot, same] using held)
  | chooseSeal key writer received _ _ _ _ =>
      exact ⟨RegionalRetirement.the_regional_machine_preserves_stream_and_pool_bounds safe.regional
        (source_command_projects rules _ key (.fundedSeal writer key.move received)), safe.windows, safe.claims⟩
  | install key proof complete _ _ ready =>
      have activatedWindows : FundedAppend.Funded rules.append (applySource rules state key (.activate proof)).1 :=
        safe.windows
      have funded := a_prepared_charge_supplies_the_window_grant complete ready
      exact ⟨RegionalRetirement.the_regional_machine_preserves_stream_and_pool_bounds safe.regional
          (source_command_projects rules _ key (.activate proof)),
        FundedAppend.regional_steps_preserve_every_window_charge activatedWindows (.publish _ _ _ funded),
        safe.claims⟩
  | settle key version =>
      refine ⟨safe.regional, safe.windows, ?_⟩
      intro query claimant held
      by_cases same : query = version
      · simp [setSlot, same] at held
      · exact safe.claims query claimant (by simpa [setSlot, same] using held)

theorem arbitrary_competing_moves_and_appends_preserve_the_regional_bounds
    {rules : Rules slots Payload Ticket} {first last : State slots Payload Ticket}
    (safe : Sound rules first) (trace : Trace rules first last) : Sound rules last := by
  induction trace with
  | same => exact safe
  | next _ event previous => exact the_shared_move_machine_preserves_stream_pool_and_window_bounds previous event

omit [DecidableEq Ticket] in
theorem the_complete_held_vector_fits_alongside_existing_ordinary_load
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (safe : Sound rules state) (complete : Complete rules state key) (pool : Nat) :
    state.appends.regional.pools.ledger.ordinary pool + (intent rules key).needs pool ≤
      (layout rules).limit pool := by
  have selectedCharges := StagedVotes.sum_of_required_charges_le_total
    (SharedExtentAccounting.allocationBytes (layout rules) pool) complete.unique (fun {version} member =>
      complete.paid version member)
  have fit := safe.regional.pools.funded.fit pool
  unfold SharedExtentAccounting.Used SharedExtentAccounting.charges at fit
  change state.appends.regional.pools.ledger.ordinary pool +
      ((rules.plan key).extents.map (SharedExtentAccounting.allocationBytes (layout rules) pool)).sum ≤ _
  unfold layout at selectedCharges ⊢
  omega

omit [DecidableEq Ticket] in
private theorem originalOwner
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (reserved : Complete rules state key) {version : Nat} (member : version ∈ (rules.plan key).extents) :
    rules.owner version = some key := by
  exact reserved.owners version member

omit [DecidableEq Ticket] in
theorem a_complete_vector_cannot_pay_for_a_different_moves_window
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {left right : Key slots}
    (fullyOwned : Complete rules state left) (different : left ≠ right) :
    rules.owner (rules.plan left).window ≠ some right := by
  have scope : rules.owner (rules.plan left).window = some left :=
    originalOwner fullyOwned List.mem_cons_self
  intro alias
  exact different (Option.some.inj (scope.symm.trans alias))

omit [DecidableEq Ticket] in
theorem installation_reuses_the_same_paid_window_and_preserves_all_original_debits
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (proof : UnifiedSource.Installation slots Nat Payload Ticket) (fullyOwned : Complete rules state key) :
    let next := publish rules state key proof
    next.appends.regional.pools.ledger.debits = state.appends.regional.pools.ledger.debits ∧
      (rules.plan key).window ∈ next.appends.regional.pools.ledger.debits ∧
      next.appends.book.latest key.stream = (rules.plan key).window ∧
      ∀ pool, SharedExtentAccounting.Used (layout rules) next.appends.regional.pools.ledger pool =
        SharedExtentAccounting.Used (layout rules) state.appends.regional.pools.ledger pool := by
  refine ⟨rfl, fullyOwned.paid _ List.mem_cons_self, ?_, fun _ => rfl⟩
  simp [publish, FundedAppend.openWindow, setSlot]

omit [DecidableEq Ticket] in
theorem the_predecessor_borrow_is_still_protected_at_promotion
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (proof : UnifiedSource.Installation slots Nat Payload Ticket) (safe : Sound rules state)
    {loan : RegionalRetirement.Borrow} (outstanding : loan ∈ state.appends.regional.borrows) :
    let next := publish rules state key proof
    loan ∈ next.appends.regional.borrows ∧ loan.version ∈ next.appends.regional.pools.ledger.debits := by
  exact ⟨outstanding, (RegionalRetirement.an_outstanding_exact_read_keeps_shared_provider_bytes
    safe.regional outstanding).2⟩

omit [DecidableEq Ticket] in
theorem the_fresh_window_cannot_alias_the_recovered_image
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (reserved : Complete rules state key) : (rules.plan key).window ∉ (rules.plan key).recovery := by
  exact (List.nodup_cons.mp reserved.unique).1

omit [DecidableEq Ticket] in
theorem a_distinct_old_loan_and_the_full_replacement_fit_together
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (safe : Sound rules state) (reserved : Complete rules state key) {loan : RegionalRetirement.Borrow}
    (live : loan ∈ state.appends.regional.borrows)
    (independent : rules.owner loan.version ≠ some key) (pool : Nat) :
    state.appends.regional.pools.ledger.ordinary pool +
      SharedExtentAccounting.charges (layout rules) pool (loan.version :: (rules.plan key).extents) ≤
      (layout rules).limit pool := by
  have outside : loan.version ∉ (rules.plan key).extents :=
    fun taken => independent (originalOwner reserved taken)
  have distinct := List.nodup_cons.mpr ⟨outside, reserved.unique⟩
  have included : loan.version :: (rules.plan key).extents ⊆ state.appends.regional.pools.ledger.debits := by
    intro version member
    rcases List.mem_cons.mp member with rfl | held
    · exact (RegionalRetirement.an_outstanding_exact_read_keeps_shared_provider_bytes safe.regional live).2
    · exact reserved.paid version held
  have bounded := StagedVotes.sum_of_required_charges_le_total
    (SharedExtentAccounting.allocationBytes (layout rules) pool) distinct included
  have numeric := safe.regional.pools.funded.fit pool
  unfold SharedExtentAccounting.Used SharedExtentAccounting.charges at numeric
  unfold layout at bounded
  unfold SharedExtentAccounting.charges layout
  omega

theorem an_exact_funded_install_is_available_at_full_capacity
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (proof : UnifiedSource.Installation slots Nat Payload Ticket)
    (complete : Complete rules state key) (bound : BindsPlan rules key proof.anchor)
    (accepted : (applySource rules state key (.activate proof)).2 = [.accepted])
    (ready : WindowReady rules (applySource rules state key (.activate proof)).1
      key (destinationWriter rules key proof)) (pool : Nat)
    (full : SharedExtentAccounting.Used (layout rules) state.appends.regional.pools.ledger pool =
      (layout rules).limit pool) :
    ∃ next, Step rules state next ∧
      next.appends.book.latest key.stream = (rules.plan key).window ∧
      SharedExtentAccounting.Used (layout rules) next.appends.regional.pools.ledger pool =
        (layout rules).limit pool := by
  have conserved := installation_reuses_the_same_paid_window_and_preserves_all_original_debits proof complete
  exact ⟨publish rules state key proof, .install key proof complete bound accepted ready,
    conserved.2.2.1, (conserved.2.2.2 pool).trans full⟩

theorem a_prepared_claim_stays_owned_until_its_exact_terminal_decision
    {rules : Rules slots Payload Ticket} {before after : State slots Payload Ticket}
    {key : Key slots} {version : Nat} (pending : ¬ CanSettle before key)
    (held : before.held version = some key) (step : Step rules before after) :
    after.held version = some key := by
  cases step with
  | claim other added _ _ _ empty _ _ =>
      by_cases same : version = added
      · subst added
        rw [empty] at held
        cases held
      · simpa [setSlot, same] using held
  | settle other removed claimed terminal _ =>
      by_cases same : version = removed
      · subst removed
        have sameKey := Option.some.inj (held.symm.trans claimed)
        exact False.elim (pending (sameKey ▸ terminal))
      · simpa [setSlot, same] using held
  | _ => exact held

#print axioms the_existing_seal_uses_the_exact_pointwise_receipts
#print axioms a_prepared_charge_supplies_the_window_grant
#print axioms a_complete_vector_binds_the_original_ordered_seal
#print axioms the_shared_move_machine_preserves_stream_pool_and_window_bounds
#print axioms arbitrary_competing_moves_and_appends_preserve_the_regional_bounds
#print axioms the_complete_held_vector_fits_alongside_existing_ordinary_load
#print axioms a_complete_vector_cannot_pay_for_a_different_moves_window
#print axioms installation_reuses_the_same_paid_window_and_preserves_all_original_debits
#print axioms the_predecessor_borrow_is_still_protected_at_promotion
#print axioms the_fresh_window_cannot_alias_the_recovered_image
#print axioms a_distinct_old_loan_and_the_full_replacement_fit_together
#print axioms an_exact_funded_install_is_available_at_full_capacity
#print axioms a_prepared_claim_stays_owned_until_its_exact_terminal_decision

end FundedWindowMove
