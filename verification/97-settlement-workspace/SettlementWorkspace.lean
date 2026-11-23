import PoolState

set_option warningAsError true

namespace SettlementWorkspace

open PoolState (Image Row Rules)

variable {Ticket : Type}

structure Ready (pool : Image Ticket) (row : Row Ticket) : Prop where
  present : row ∈ pool.rows
  fenced : CopyFence.Closed pool.gate row.key
  erased : row.provider.erased = true

noncomputable def checkEvidence (pool : Image Ticket) (row : Row Ticket) : Bool := by
  classical
  exact if Ready pool row then true else false

def CanStage (_hasLocalEvidence : Bool) : Prop :=
  _hasLocalEvidence = true

theorem a_stage_requires_local_evidence (evidence : Bool) (ready : CanStage evidence) :
    evidence = true := by
  exact ready

private theorem ready_can_stage {pool : Image Ticket} {row : Row Ticket} (ready : Ready pool row) :
    CanStage (checkEvidence pool row) := by
  classical
  have checked : checkEvidence pool row = true := by
    simp [checkEvidence, ready]
  rw [checked] <;> rfl

private theorem staged_evidence_is_ready {pool : Image Ticket} {row : Row Ticket}
    (allowed : CanStage (checkEvidence pool row)) : Ready pool row := by
  classical
  have evidence := a_stage_requires_local_evidence _ allowed
  by_cases ready : Ready pool row
  · exact ready
  · simp [checkEvidence, ready] at evidence

structure State (Ticket : Type) where
  durable : Image Ticket
  staged : Option (Row Ticket)

inductive Step : State Ticket → State Ticket → Prop
  | stage {before} (row : Row Ticket) (free : before.staged = none)
      (eligible : CanStage (checkEvidence before.durable row)) :
      Step before {before with staged := some row}
  | restart {before} : Step before {before with staged := none}
  | publish {before row} (earlier later : List (Row Ticket))
      (same : before.staged = some row) (exactRows : before.durable.rows = earlier ++ row :: later)
      (ready : Ready before.durable row) :
      Step before ⟨{before.durable with rows := earlier ++ later}, none⟩

inductive Trace : State Ticket → State Ticket → Prop
  | same (state : State Ticket) : Trace state state
  | next {first before after : State Ticket} : Trace first before → Step before after → Trace first after

def OnlyReady (state : State Ticket) : Prop :=
  ∀ row, state.staged = some row → Ready state.durable row

theorem a_workspace_holder_is_already_ready
    {before after : State Ticket} (step : Step before after) : OnlyReady after := by
  intro row staged
  cases step with
  | stage _ _ ready =>
      have same := Option.some.inj staged
      exact same ▸ staged_evidence_is_ready ready
  | restart => cases staged
  | publish _ _ _ _ _ => cases staged

theorem a_waiting_row_cannot_take_the_shared_workspace
    (state : State Ticket) (row : Row Ticket) (waiting : ¬ Ready state.durable row) :
    ¬ CanStage (checkEvidence state.durable row) :=
  fun staged => waiting (staged_evidence_is_ready staged)

variable [DecidableEq Ticket]

theorem every_workspace_step_is_a_stutter_or_exact_pool_refund
    (rules : Rules Ticket) {before after : State Ticket} (step : Step before after) :
    before.durable = after.durable ∨ PoolState.Step rules before.durable after.durable := by
  cases step with
  | stage _ _ _ | restart => exact .inl rfl
  | publish earlier later _ exactRows ready =>
      exact .inr (.refund earlier later exactRows ready.fenced ready.erased)

theorem a_workspace_trace_refines_the_original_physical_pool
    (rules : Rules Ticket) {first after : State Ticket} (history : Trace first after) :
    PoolState.Trace rules first.durable after.durable := by
  induction history with
  | same => exact .same _
  | next _ step prior =>
      rcases every_workspace_step_is_a_stutter_or_exact_pool_refund rules step with same | refund
      · exact same ▸ prior
      · exact .next prior refund

def chargedUse (rules : Rules Ticket) (publicationBytes : Nat) (state : State Ticket) : Nat :=
  PoolState.used rules state.durable + if state.staged.isSome then publicationBytes else 0

theorem local_publication_fits_its_own_reserved_peak
    (rules : Rules Ticket) {first after : State Ticket} (publicationBytes reservedBytes : Nat)
    (fitsReserve : publicationBytes ≤ reservedBytes) (safe : PoolState.Sound rules first.durable)
    (history : Trace first after) : chargedUse rules publicationBytes after ≤ rules.limit + reservedBytes := by
  have sound := PoolState.all_local_histories_keep_the_exact_allocator_and_capacity safe
    (a_workspace_trace_refines_the_original_physical_pool rules history)
  unfold chargedUse
  split
  · exact Nat.add_le_add sound.1.fits fitsReserve
  · exact Nat.add_le_add sound.1.fits (Nat.zero_le _)

omit [DecidableEq Ticket] in
theorem restart_returns_the_workspace_and_keeps_all_original_charges
    (before : State Ticket) :
    ∃ after, Step before after ∧ after.staged = none ∧ after.durable = before.durable :=
  ⟨{before with staged := none}, .restart, rfl, rfl⟩

omit [DecidableEq Ticket] in
theorem ready_refund_progresses_at_capacity_while_its_peer_waits
    (rules : Rules Ticket) (pool : Image Ticket) (waiting ready : Row Ticket) (others : List (Row Ticket))
    (rows : pool.rows = waiting :: ready :: others)
    (pending : ¬ Ready pool waiting) (eligible : Ready pool ready)
    (used : PoolState.used rules pool = rules.limit) :
    ∃ after, Trace (⟨pool, none⟩ : State Ticket) after ∧ after.staged = none ∧
      waiting ∈ after.durable.rows ∧ PoolState.used rules after.durable < rules.limit ∧
      ¬ CanStage (checkEvidence pool waiting) := by
  let initial : State Ticket := ⟨pool, none⟩
  let running : State Ticket := ⟨pool, some ready⟩
  let after : State Ticket := ⟨{pool with rows := waiting :: others}, none⟩
  have start : Step initial running := .stage ready rfl (ready_can_stage eligible)
  have finish : Step running after := .publish [waiting] others rfl rows eligible
  have drops : PoolState.used rules after.durable + rules.cost ready.binding = PoolState.used rules pool := by
    simp [after, PoolState.used, PoolState.charges, rows]
    omega
  have positive := rules.positive ready.binding
  exact ⟨after, .next (.next (.same _) start) finish, rfl, List.mem_cons_self,
    by omega, a_waiting_row_cannot_take_the_shared_workspace initial waiting pending⟩

theorem reserving_a_positive_workspace_per_obligation_cannot_fit_one_workspace
    (jobs workspace : Nat) (multiple : 1 < jobs) (positive : 0 < workspace) :
    ¬ jobs * workspace ≤ workspace := by
  have atLeastTwo := Nat.mul_le_mul_right workspace (show 2 ≤ jobs by omega)
  omega

#print axioms a_stage_requires_local_evidence
#print axioms a_workspace_holder_is_already_ready
#print axioms a_waiting_row_cannot_take_the_shared_workspace
#print axioms every_workspace_step_is_a_stutter_or_exact_pool_refund
#print axioms a_workspace_trace_refines_the_original_physical_pool
#print axioms local_publication_fits_its_own_reserved_peak
#print axioms restart_returns_the_workspace_and_keeps_all_original_charges
#print axioms ready_refund_progresses_at_capacity_while_its_peer_waits
#print axioms reserving_a_positive_workspace_per_obligation_cannot_fit_one_workspace

end SettlementWorkspace
