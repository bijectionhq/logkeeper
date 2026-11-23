import UnifiedSource
import PoolIncarnations

set_option warningAsError true

namespace RegionalRetirement

open SnapshotAdmission (setSlot)

variable {Payload Ticket : Type} {slots : Nat}

structure Borrow where
  serial : Nat
  root : Nat
  version : Nat
  deriving DecidableEq

structure State (slots : Nat) (Payload Ticket : Type) where
  streams : Nat → UnifiedSource.State slots Nat Payload
  pools : PoolIncarnations.State Ticket
  borrows : List Borrow
  issuedBorrow : Nat

structure Rules (slots : Nat) (Payload Ticket : Type) where
  limits : Nat → Kernel.Limits
  source : Nat → UnifiedSource.Rules slots Nat Payload Ticket
  owner : Nat → Nat
  erasureScope : Nat → Nat → Prop
  poolLimit : Nat
  borrowLimit : Nat
  layout : SharedExtentAccounting.Layout Nat
  needs : SharedCustody.Dependencies
  closeAllowed : Nat → Prop
  reserve : ProviderIOClosure.Custody Ticket → Prop
  expected : SharedExtentAccounting.State Nat Ticket → Nat → Nat
  authenticated : PoolIncarnations.Validation Nat → Prop
  namespaceClosed : Nat → Prop
  stopped : Borrow → Prop

def count (borrows : List Borrow) (version : Nat) : Nat :=
  borrows.countP (fun loan => loan.version == version)

def Retired (state : State slots Payload Ticket) (stream : Nat) : Prop :=
  (state.streams stream).core.stream.authority = .retired

def CanBorrow (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (root version : Nat) : Prop :=
  ¬ Retired state (rules.owner root) ∧ state.pools.ledger.catalog.roots root = .live ∧
    state.pools.ledger.catalog.refs root version = .held

def ReadCustodySettled (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (stream : Nat) : Prop :=
  (∀ root version, rules.owner root = stream → state.pools.ledger.catalog.refs root version ≠ .held) ∧
  (∀ loan ∈ state.borrows, rules.owner loan.root ≠ stream)

def ErasureReady (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (stream : Nat) : Prop :=
  Retired state stream ∧ ReadCustodySettled rules state stream ∧
  ∀ version, rules.erasureScope stream version →
    version ≤ state.pools.ledger.issued ∧ (state.pools.ledger.provider version).erased = true

private noncomputable def streamAfter (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (stream : Nat) (command : UnifiedSource.Command slots Nat Payload Ticket) :
    UnifiedSource.State slots Nat Payload :=
  ((UnifiedSource.replay (rules.limits stream) (rules.source stream) (state.streams stream) [command]).1)

def withCount (poolState : PoolIncarnations.State Ticket) (version next : Nat) :
    PoolIncarnations.State Ticket :=
  {poolState with ledger := {poolState.ledger with catalog := {
    poolState.ledger.catalog with borrows := setSlot poolState.ledger.catalog.borrows version next}}}

variable [DecidableEq Ticket]

abbrev PoolStep (rules : Rules slots Payload Ticket) :=
  PoolIncarnations.Step rules.poolLimit rules.layout rules.needs rules.closeAllowed rules.reserve
    rules.expected rules.authenticated rules.namespaceClosed

inductive Step (rules : Rules slots Payload Ticket) :
    State slots Payload Ticket → State slots Payload Ticket → Prop
  | ordered {state} (stream : Nat) (command : UnifiedSource.Command slots Nat Payload Ticket) :
      Step rules state {state with streams := setSlot state.streams stream (streamAfter rules state stream command)}
  | pool {state next} (event : PoolIncarnations.Event) (effect : PoolStep rules state.pools event next)
      (exactCounts : next.ledger.catalog.borrows = state.pools.ledger.catalog.borrows)
      (closedReferences : ∀ root version, Retired state (rules.owner root) →
        next.ledger.catalog.refs root version = .held →
        state.pools.ledger.catalog.refs root version = .held) :
      Step rules state {state with pools := next}
  | borrow {state} (root version : Nat) (allowed : CanBorrow rules state root version)
      (room : state.borrows.length < rules.borrowLimit) :
      Step rules state {state with
        pools := withCount state.pools version (state.pools.ledger.catalog.borrows version + 1)
        borrows := ⟨state.issuedBorrow + 1, root, version⟩ :: state.borrows
        issuedBorrow := state.issuedBorrow + 1}
  | finish {state} (loan : Borrow) (earlier later : List Borrow)
      (exact : state.borrows = earlier ++ loan :: later)
      (authenticated : rules.stopped loan)
      (outstanding : 0 < state.pools.ledger.catalog.borrows loan.version) :
      Step rules state {state with
        pools := withCount state.pools loan.version (state.pools.ledger.catalog.borrows loan.version - 1)
        borrows := earlier ++ later}

structure Sound (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) : Prop where
  streams : ∀ stream, Kernel.Valid (rules.limits stream) (state.streams stream).core.stream
  pools : PoolIncarnations.Sound rules.poolLimit rules.layout rules.needs state.pools
  counts : ∀ version, state.pools.ledger.catalog.borrows version = count state.borrows version
  unique : (state.borrows.map Borrow.serial).Nodup
  issued : ∀ loan ∈ state.borrows, loan.serial ≤ state.issuedBorrow
  bounded : state.borrows.length ≤ rules.borrowLimit

inductive Trace (rules : Rules slots Payload Ticket) :
    State slots Payload Ticket → State slots Payload Ticket → Prop
  | same (state) : Trace rules state state
  | next {first before after} : Trace rules first before → Step rules before after → Trace rules first after

theorem every_regional_step_projects_to_the_existing_reducers
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket} (step : Step rules state next) :
    (∀ stream, Kernel.Trace (rules.limits stream) (state.streams stream).core.stream (next.streams stream).core.stream) ∧
    (next.pools = state.pools ∨ ∃ event, PoolStep rules state.pools event next.pools) := by
  cases step with
  | ordered stream command =>
      refine ⟨?_, .inl rfl⟩
      intro query
      by_cases same : query = stream
      · subst query
        simpa [setSlot, streamAfter] using UnifiedSource.a_joint_history_projects_to_the_stream_trace
          (rules.limits stream) (rules.source stream) (state.streams stream) [command]
      · simpa [setSlot, same] using Kernel.Trace.same (limits := rules.limits query) ((state.streams query).core.stream)
  | pool event effect _ _ =>
      exact ⟨fun stream => .same ((state.streams stream).core.stream), .inr ⟨event, effect⟩⟩
  | borrow root version allowed _ =>
      refine ⟨fun stream => .same ((state.streams stream).core.stream), .inr ⟨.account, ?_⟩⟩
      refine .account (.references (.borrow root version allowed.2.1 allowed.2.2)) ?_ ?_
      · intro other member absent
        exact False.elim (absent member)
      · intro pool grows
        exact False.elim (Nat.lt_irrefl (state.pools.ledger.ordinary pool) grows)
  | finish loan _ _ _ _ outstanding =>
      refine ⟨fun stream => .same ((state.streams stream).core.stream), .inr ⟨.account, ?_⟩⟩
      refine .account (.references (.finish loan.version outstanding)) ?_ ?_
      · intro other member absent
        exact False.elim (absent member)
      · intro pool grows
        exact False.elim (Nat.lt_irrefl (state.pools.ledger.ordinary pool) grows)

theorem the_regional_machine_preserves_stream_and_pool_bounds
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket}
    (safe : Sound rules state) (step : Step rules state next) : Sound rules next := by
  have ⟨eachStream, physical⟩ := every_regional_step_projects_to_the_existing_reducers step
  have streamValid := fun stream => Kernel.every_trace_preserves_bounds (safe.streams stream) (eachStream stream)
  have poolValid : PoolIncarnations.Sound rules.poolLimit rules.layout rules.needs next.pools := by
    rcases physical with same | ⟨_, effect⟩
    · rw [same]
      exact safe.pools
    · exact PoolIncarnations.every_step_preserves_bounded_scoped_custody safe.pools effect
  refine ⟨streamValid, poolValid, ?_, ?_, ?_, ?_⟩
  all_goals cases step
  case ordered => exact safe.counts
  case pool _ _ same _ => exact fun version => congrFun same version |>.trans (safe.counts version)
  case borrow root version _ _ =>
    intro query
    by_cases same : query = version
    · subst query
      simp [withCount, setSlot, count, safe.counts]
    · have diff : version ≠ query := Ne.symm same
      simp [withCount, setSlot, count, same, diff, safe.counts]
  case finish loan earlier later exactBook _ _ =>
    intro query
    by_cases same : query = loan.version
    · subst query
      simp [withCount, setSlot, count, safe.counts, exactBook, List.countP_append]
    · have diff : loan.version ≠ query := Ne.symm same
      simp [withCount, setSlot, count, same, diff, safe.counts, exactBook, List.countP_append]
  case ordered => exact safe.unique
  case pool => exact safe.unique
  case borrow =>
    apply List.nodup_cons.mpr
    refine ⟨?_, safe.unique⟩
    intro found
    obtain ⟨loan, member, equal⟩ := List.mem_map.mp found
    have issued := safe.issued loan member
    change loan.serial = state.issuedBorrow + 1 at equal
    omega
  case finish loan earlier later exactBook _ _ =>
    have unique := safe.unique
    rw [exactBook] at unique
    have retained : List.Sublist (earlier ++ later) (earlier ++ loan :: later) :=
      (List.Sublist.cons loan (List.Sublist.refl later)).append_left earlier
    exact (retained.map Borrow.serial).nodup unique
  case ordered => exact safe.issued
  case pool => exact safe.issued
  case borrow =>
    intro loan found
    rcases List.mem_cons.mp found with rfl | earlier
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (safe.issued loan earlier)
  case finish loan earlier later exactBook _ _ =>
    intro other found
    apply safe.issued
    rw [exactBook]
    rcases List.mem_append.mp found with before | after
    · exact List.mem_append_left _ before
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
  case ordered => exact safe.bounded
  case pool => exact safe.bounded
  case borrow _ _ _ room => exact Nat.succ_le_of_lt room
  case finish loan earlier later exactBook _ _ =>
    have bound := safe.bounded
    simp [exactBook] at bound
    simp
    omega

theorem every_regional_trace_preserves_both_logical_and_physical_bounds
    {rules : Rules slots Payload Ticket} {first last : State slots Payload Ticket}
    (safe : Sound rules first) (trace : Trace rules first last) :
    Sound rules last := by
  induction trace with
  | same => exact safe
  | next _ step previous => exact the_regional_machine_preserves_stream_and_pool_bounds previous step

omit [DecidableEq Ticket] in
theorem an_outstanding_exact_read_keeps_shared_provider_bytes
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} (safe : Sound rules state)
    {loan : Borrow} (outstanding : loan ∈ state.borrows) :
    (state.pools.ledger.provider loan.version).present = true ∧ loan.version ∈ state.pools.ledger.debits := by
  have positive : 0 < count state.borrows loan.version := by
    have existsMatching : ∃ item ∈ state.borrows, (item.version == loan.version) = true :=
      ⟨loan, outstanding, by simp⟩
    exact List.countP_pos_iff.mpr existsMatching
  apply SharedExtentAccounting.a_read_borrow_preserves_its_debit_without_a_live_root safe.pools.funded
  rw [safe.counts]
  exact positive

omit [DecidableEq Ticket] in
theorem a_retired_stream_cannot_begin_a_new_borrow
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket}
    {root version : Nat} (retired : Retired state (rules.owner root)) :
    ¬ CanBorrow rules state root version := by
  intro allowed
  exact allowed.1 retired

theorem settled_read_custody_stays_settled_for_a_retired_stream
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket} {stream : Nat}
    (step : Step rules state next) (retired : Retired state stream)
    (settled : ReadCustodySettled rules state stream) :
    Retired next stream ∧ ReadCustodySettled rules next stream := by
  have trace := (every_regional_step_projects_to_the_existing_reducers step).1 stream
  refine ⟨Kernel.retired_absorbs_trace retired trace, ?_⟩
  cases step with
  | ordered => exact settled
  | pool _ _ _ closedReferences =>
      exact ⟨fun root version owner held =>
        settled.1 root version owner (closedReferences root version (owner.symm ▸ retired) held), settled.2⟩
  | borrow root version allowed _ =>
      refine ⟨settled.1, ?_⟩
      intro loan member
      rcases List.mem_cons.mp member with rfl | earlier
      · intro sameOwner
        exact (a_retired_stream_cannot_begin_a_new_borrow (version := version) (sameOwner.symm ▸ retired)) allowed
      · exact settled.2 loan earlier
  | finish loan earlier later exactBook _ _ =>
      refine ⟨settled.1, ?_⟩
      intro other member
      apply settled.2 other
      rw [exactBook]
      exact ((List.Sublist.cons loan (List.Sublist.refl later)).append_left earlier).subset member

theorem a_survivor_can_borrow_at_full_physical_capacity_while_erasure_is_ready
    (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) (stream root version : Nat)
    (ready : ErasureReady rules state stream) (allowed : CanBorrow rules state root version)
    (room : state.borrows.length < rules.borrowLimit) :
    ∃ next, Step rules state next ∧ ErasureReady rules next stream ∧
      (∀ pool, SharedExtentAccounting.Used rules.layout next.pools.ledger pool =
        SharedExtentAccounting.Used rules.layout state.pools.ledger pool) ∧
      ⟨state.issuedBorrow + 1, root, version⟩ ∈ next.borrows := by
  have step := Step.borrow root version allowed room
  have preserved := settled_read_custody_stays_settled_for_a_retired_stream step ready.1 ready.2.1
  exact ⟨_, step, ⟨preserved.1, preserved.2, ready.2.2⟩, fun _ => rfl, List.mem_cons_self⟩

omit [DecidableEq Ticket] in
theorem an_erasure_receipt_requires_disposition_of_an_original_extent
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {stream version : Nat}
    (ready : ErasureReady rules state stream) (original : rules.erasureScope stream version) :
    (state.pools.ledger.provider version).erased = true := by
  exact (ready.2.2 version original).2

theorem a_scoped_finish_preserves_every_other_read_identity
    (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) (loan : Borrow)
    (earlier later : List Borrow) (exactBook : state.borrows = earlier ++ loan :: later)
    (authorized : rules.stopped loan) (positive : 0 < state.pools.ledger.catalog.borrows loan.version)
    {other : Borrow} (outstanding : other ∈ state.borrows) (different : other ≠ loan) :
    ∃ next, Step rules state next ∧ other ∈ next.borrows := by
  refine ⟨_, .finish loan earlier later exactBook authorized positive, ?_⟩
  rw [exactBook] at outstanding
  rcases List.mem_append.mp outstanding with before | after
  · exact List.mem_append_left _ before
  · rcases List.mem_cons.mp after with rfl | later
    · exact False.elim (different rfl)
    · exact List.mem_append_right _ later

private theorem an_absent_issued_borrow_serial_stays_absent
    {rules : Rules slots Payload Ticket} {before after : State slots Payload Ticket}
    (step : Step rules before after) (serial : Nat) (issued : serial ≤ before.issuedBorrow)
    (absent : serial ∉ before.borrows.map Borrow.serial) :
    serial ≤ after.issuedBorrow ∧ serial ∉ after.borrows.map Borrow.serial := by
  cases step with
  | ordered | pool => exact ⟨issued, absent⟩
  | borrow =>
      refine ⟨Nat.le_succ_of_le issued, ?_⟩
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun same => by change serial = before.issuedBorrow + 1 at same; omega, absent⟩
  | finish loan earlier later exactBook _ _ =>
      refine ⟨issued, ?_⟩
      intro found
      apply absent
      rw [exactBook]
      exact ((List.Sublist.cons loan (List.Sublist.refl later)).append_left earlier).map Borrow.serial |>.subset found

theorem a_completed_borrow_serial_cannot_be_reused_after_any_trace
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket}
    (safe : Sound rules state) (loan : Borrow) (earlier later : List Borrow)
    (exactBook : state.borrows = earlier ++ loan :: later)
    (authorized : rules.stopped loan) (positive : 0 < state.pools.ledger.catalog.borrows loan.version) :
    ∃ next, Step rules state next ∧
      ∀ last, Trace rules next last → loan.serial ∉ last.borrows.map Borrow.serial := by
  refine ⟨_, .finish loan earlier later exactBook authorized positive, ?_⟩
  intro last trace
  have registered : loan ∈ state.borrows := by
    rw [exactBook]
    exact List.mem_append_right _ List.mem_cons_self
  have issued := safe.issued loan registered
  have unique := safe.unique
  rw [exactBook, List.map_append, List.map_cons] at unique
  have absent : loan.serial ∉ (earlier ++ later).map Borrow.serial := by
    rw [List.map_append, List.mem_append]
    intro found
    rcases found with before | after
    · exact (List.nodup_append.mp unique).2.2 loan.serial before loan.serial List.mem_cons_self rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1 after
  have permanent :
      loan.serial ≤ last.issuedBorrow ∧ loan.serial ∉ last.borrows.map Borrow.serial := by
    induction trace with
    | same => exact ⟨issued, absent⟩
    | next _ step prior => exact an_absent_issued_borrow_serial_stays_absent step _ prior.1 prior.2
  exact permanent.2

theorem an_ordered_retirement_preserves_the_surviving_stream_and_its_borrow
    (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (closing survivor : Nat) (different : survivor ≠ closing) (writer : Kernel.Writer)
    (active : (state.streams closing).core.stream.authority = .active writer)
    (noPending : (state.streams closing).core.pending = none)
    (safe : Sound rules state) {loan : Borrow} (outstanding : loan ∈ state.borrows) :
    ∃ next, Step rules state next ∧ Retired next closing ∧ next.streams survivor = state.streams survivor ∧
      loan ∈ next.borrows ∧ loan.version ∈ next.pools.ledger.debits := by
  let command : UnifiedSource.Command slots Nat Payload Ticket := .retire writer
  let next := {state with streams := setSlot state.streams closing (streamAfter rules state closing command)}
  refine ⟨next, .ordered closing command, ?_, ?_, outstanding, ?_⟩
  · simp [Retired, next, setSlot, streamAfter, UnifiedSource.replay, command, UnifiedSource.decide, active, noPending]
  · simp [next, setSlot, different]
  · exact (an_outstanding_exact_read_keeps_shared_provider_bytes safe outstanding).2

#print axioms every_regional_step_projects_to_the_existing_reducers
#print axioms the_regional_machine_preserves_stream_and_pool_bounds
#print axioms every_regional_trace_preserves_both_logical_and_physical_bounds
#print axioms an_outstanding_exact_read_keeps_shared_provider_bytes
#print axioms a_retired_stream_cannot_begin_a_new_borrow
#print axioms settled_read_custody_stays_settled_for_a_retired_stream
#print axioms a_survivor_can_borrow_at_full_physical_capacity_while_erasure_is_ready
#print axioms an_erasure_receipt_requires_disposition_of_an_original_extent
#print axioms a_scoped_finish_preserves_every_other_read_identity
#print axioms a_completed_borrow_serial_cannot_be_reused_after_any_trace
#print axioms an_ordered_retirement_preserves_the_surviving_stream_and_its_borrow

end RegionalRetirement
