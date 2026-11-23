import RegionalRetirement

set_option warningAsError true

namespace FundedAppend

open SnapshotAdmission (setSlot)

variable {slots : Nat} {Payload Ticket : Type}

structure Window where
  stream : Nat
  placement : Kernel.Placement
  nextLsn : Nat
  spent : Nat

structure Book where
  windows : Nat → Option Window
  latest : Nat → Nat

structure Request (Payload Ticket : Type) where
  version : Nat
  writer : Kernel.Writer
  lsn : Nat
  offset : Nat
  payload : Payload
  evidence : Ticket

structure Rules (slots : Nat) (Payload Ticket : Type) where
  regional : RegionalRetirement.Rules slots Payload Ticket
  owner : Nat → Nat
  cost : Payload → Nat
  durable : Nat → Request Payload Ticket → Prop

structure State (slots : Nat) (Payload Ticket : Type) where
  regional : RegionalRetirement.State slots Payload Ticket
  book : Book

abbrev Source (slots : Nat) (Payload : Type) := UnifiedSource.State slots Nat Payload

def debitBytes (rules : Rules slots Payload Ticket) (version : Nat) : Nat :=
  rules.regional.layout.bytes version

def Backed (state : RegionalRetirement.State slots Payload Ticket) (version : Nat) : Prop :=
  version ∈ state.pools.ledger.debits ∧ (state.pools.ledger.provider version).present = true

structure LocalChecks (rules : Rules slots Payload Ticket) (stream : Nat) (source : Source slots Payload)
    (book : Book) (window : Window) (request : Request Payload Ticket) : Prop where
  owner : window.stream = stream
  current : book.latest stream = request.version
  placement : window.placement = request.writer.placement
  nextLsn : window.nextLsn = request.lsn
  offset : window.spent = request.offset
  positive : 0 < rules.cost request.payload
  fits : request.offset + rules.cost request.payload ≤ debitBytes rules request.version
  durable : rules.durable stream request
  streamAllowed :
    OrderedApplication.AppendAllowed (rules.regional.limits stream) source.core.stream request.writer request.lsn

private theorem exactCursor {rules : Rules slots Payload Ticket} {stream source book window request}
    (allowed : LocalChecks rules stream source book window request) : window.spent = request.offset := by
  exact allowed.offset

def appendCommand (request : Request Payload Ticket) : UnifiedSource.Command slots Nat Payload Ticket :=
  .stream (.append request.writer request.lsn request.payload)

def advanceWindow (rules : Rules slots Payload Ticket) (request : Request Payload Ticket)
    (book : Book) (window : Window) : Book :=
  let advanced := {window with nextLsn := request.lsn + 1, spent := request.offset + rules.cost request.payload}
  {book with windows := setSlot book.windows request.version (some advanced)}

noncomputable def decide (rules : Rules slots Payload Ticket) (stream : Nat)
    (source : Source slots Payload) (book : Book) (request : Request Payload Ticket) :
    Source slots Payload × Book × UnifiedSource.Reply Payload := by
  classical
  let refuse : Source slots Payload × Book × UnifiedSource.Reply Payload :=
    ({source with position := source.position + 1}, book, .refused)
  exact match book.windows request.version with
  | none => refuse
  | some window =>
      if LocalChecks rules stream source book window request then
        let result := UnifiedSource.replay (rules.regional.limits stream) (rules.regional.source stream)
          source [appendCommand request]
        (result.1, advanceWindow rules request book window,
          .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩))
      else refuse

def useDecision (state : State slots Payload Ticket) (stream : Nat)
    (result : Source slots Payload × Book × UnifiedSource.Reply Payload) : State slots Payload Ticket :=
  { regional := {state.regional with streams := setSlot state.regional.streams stream result.1}
    book := result.2.1 }

def PublishWindow (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (stream version : Nat) (writer : Kernel.Writer) : Prop :=
  rules.owner version = stream ∧ state.book.latest stream < version ∧ state.book.windows version = none ∧
  (state.regional.streams stream).core.stream.authority = .active writer ∧
  PoolIncarnations.Eligible state.regional.pools (rules.regional.layout.pool version) ∧
  Backed state.regional version

def openWindow (state : State slots Payload Ticket) (stream version : Nat)
    (writer : Kernel.Writer) : State slots Payload Ticket :=
  let lsn := (state.regional.streams stream).core.stream.history.length
  {state with book := ⟨setSlot state.book.windows version (some ⟨stream, writer.placement, lsn, 0⟩),
                        setSlot state.book.latest stream version⟩}

def pruneWindow (state : State slots Payload Ticket) (version : Nat) : State slots Payload Ticket :=
  {state with book := {state.book with windows := setSlot state.book.windows version none}}

def Funded (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) : Prop :=
  ∀ version window, state.book.windows version = some window →
    Backed state.regional version ∧ window.spent ≤ debitBytes rules version ∧
    rules.owner version = window.stream ∧ version ≤ state.book.latest window.stream

variable [DecidableEq Ticket]

inductive Step (rules : Rules slots Payload Ticket) :
    State slots Payload Ticket → State slots Payload Ticket → Prop
  | regional {state next} (event : RegionalRetirement.Step rules.regional state.regional next)
      (noAppend : ∀ stream, (next.streams stream).core.stream.history =
        (state.regional.streams stream).core.stream.history)
      (keepsWindows : ∀ version window, state.book.windows version = some window → Backed next version) :
      Step rules state {state with regional := next}
  | publish {state} (stream version : Nat) (writer : Kernel.Writer)
      (allowed : PublishWindow rules state stream version writer) :
      Step rules state (openWindow state stream version writer)
  | prune {state} (version : Nat) (window : Window) (current : state.book.windows version = some window)
      (releasable : window.nextLsn ≤ (state.regional.streams window.stream).core.stream.firstRetained ∨
        RegionalRetirement.Retired state.regional window.stream) :
      Step rules state (pruneWindow state version)
  | append {state} (stream : Nat) (request : Request Payload Ticket) :
      Step rules state (useDecision state stream
        (decide rules stream (state.regional.streams stream) state.book request))

inductive Trace (rules : Rules slots Payload Ticket) :
    State slots Payload Ticket → State slots Payload Ticket → Prop
  | same (state : State slots Payload Ticket) : Trace rules state state
  | next {first before after} : Trace rules first before → Step rules before after → Trace rules first after

omit [DecidableEq Ticket] in
theorem eligible_append_uses_the_original_ordered_reducer
    {rules : Rules slots Payload Ticket} {stream : Nat} {source : Source slots Payload}
    {request : Request Payload Ticket} {window : Window} {book : Book}
    (present : book.windows request.version = some window)
    (allowed : LocalChecks rules stream source book window request) :
    decide rules stream source book request =
      ((UnifiedSource.replay (rules.regional.limits stream) (rules.regional.source stream)
        source [appendCommand request]).1, advanceWindow rules request book window,
        .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩)) := by
  simp [decide, present, allowed]

omit [DecidableEq Ticket] in
theorem original_reducer_has_the_same_receipt
    {rules : Rules slots Payload Ticket} {stream : Nat} {source : Source slots Payload}
    {request : Request Payload Ticket} {window : Window} {book : Book}
    (present : book.windows request.version = some window)
    (allowed : LocalChecks rules stream source book window request) :
    let replayed := UnifiedSource.replay (rules.regional.limits stream) (rules.regional.source stream)
      source [appendCommand request]
    replayed.2 = [(decide rules stream source book request).2.2] ∧
      replayed.1.core.stream.history = source.core.stream.history ++ [⟨request.writer.epoch, request.payload⟩] := by
  rw [eligible_append_uses_the_original_ordered_reducer present allowed]
  simp [appendCommand, UnifiedSource.replay, UnifiedSource.decide, UnifiedSource.Routine,
    OrderedApplication.decideCommand, allowed.streamAllowed]

omit [DecidableEq Ticket] in
theorem no_window_means_no_append_payment_or_receipt
    {rules : Rules slots Payload Ticket} {stream : Nat} {source : Source slots Payload} {book : Book}
    {request : Request Payload Ticket} (missing : book.windows request.version = none) :
    decide rules stream source book request = ({source with position := source.position + 1}, book, .refused) := by
  simp [decide, missing]

omit [DecidableEq Ticket] in
theorem refusal_does_not_spend_the_window
    {rules : Rules slots Payload Ticket} {stream : Nat} {source : Source slots Payload} {book : Book}
    {request : Request Payload Ticket} (refused : (decide rules stream source book request).2.2 = .refused) :
    decide rules stream source book request = ({source with position := source.position + 1}, book, .refused) := by
  cases present : book.windows request.version with
  | none => exact no_window_means_no_append_payment_or_receipt present
  | some window =>
    by_cases allowed : LocalChecks rules stream source book window request
    · rw [eligible_append_uses_the_original_ordered_reducer present allowed] at refused
      cases refused
    · simp [decide, present, allowed]

theorem regional_steps_preserve_every_window_charge
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket}
    (funded : Funded rules state) (event : Step rules state next) : Funded rules next := by
  intro version window live
  cases event with
  | regional _ _ keeps =>
      obtain ⟨_, fits, owner, bounded⟩ := funded version window live
      exact ⟨keeps version window live, fits, owner, bounded⟩
  | publish stream fresh writer allowed =>
      by_cases same : version = fresh
      · subst version
        simp [openWindow, setSlot] at live
        subst window
        exact ⟨allowed.2.2.2.2.2, Nat.zero_le _, allowed.1, by simp [openWindow, setSlot]⟩
      · have existing : state.book.windows version = some window := by
          simpa [openWindow, setSlot, same] using live
        obtain ⟨paid, fits, owner, bounded⟩ := funded version window existing
        refine ⟨paid, fits, owner, ?_⟩
        by_cases sameOwner : window.stream = stream
        · have freshEnough := allowed.2.1
          simp [openWindow, setSlot, sameOwner] at bounded ⊢
          omega
        · simpa [openWindow, setSlot, sameOwner] using bounded
  | prune removed prior _ _ =>
      by_cases same : version = removed
      · simp [pruneWindow, setSlot, same] at live
      · exact funded version window (by simpa [pruneWindow, setSlot, same] using live)
  | append stream request =>
      cases present : state.book.windows request.version with
      | none =>
        simp only [useDecision, decide, present] at live ⊢
        exact funded version window live
      | some current =>
        by_cases allowed : LocalChecks rules stream (state.regional.streams stream) state.book current request
        · rw [eligible_append_uses_the_original_ordered_reducer present allowed] at live ⊢
          simp only [useDecision] at live ⊢
          by_cases same : version = request.version
          · subst version
            simp [advanceWindow, setSlot] at live
            subst window
            obtain ⟨paid, _, owner, bounded⟩ := funded request.version current present
            exact ⟨paid, allowed.fits, owner, bounded⟩
          · exact funded version window (by simpa [advanceWindow, setSlot, same] using live)
        · simp only [useDecision, decide, present, ite_eq_right allowed] at live ⊢
          exact funded version window live

theorem funding_is_preserved_across_arbitrary_traces
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket}
    (funded : Funded rules state) (trace : Trace rules state next) : Funded rules next := by
  induction trace with
  | same => exact funded
  | next _ event previous => exact regional_steps_preserve_every_window_charge previous event

omit [DecidableEq Ticket] in
theorem a_successful_append_spends_only_its_own_prepaid_range
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {stream : Nat}
    {request : Request Payload Ticket} (funded : Funded rules state)
    (receipt : (decide rules stream (state.regional.streams stream) state.book request).2.2 =
      .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩)) :
    ∃ window, state.book.windows request.version = some window ∧ Backed state.regional request.version ∧
      rules.owner request.version = stream ∧ request.offset = window.spent ∧
      window.spent < request.offset + rules.cost request.payload ∧
      request.offset + rules.cost request.payload ≤ debitBytes rules request.version := by
  simp only [decide] at receipt
  split at receipt
  · cases receipt
  · rename_i window present
    split at receipt
    · rename_i allowed
      obtain ⟨paid, _, owner, _⟩ := funded request.version window present
      have offset := exactCursor allowed
      exact ⟨window, present, paid, owner.trans allowed.owner, offset.symm,
        by have positive := allowed.positive; omega, allowed.fits⟩
    · cases receipt

omit [DecidableEq Ticket] in
theorem replay_recovers_the_same_outcome_under_any_current_pool
    {rules : Rules slots Payload Ticket} {original reopened : State slots Payload Ticket}
    (stream : Nat) (request : Request Payload Ticket)
    (source : original.regional.streams stream = reopened.regional.streams stream)
    (book : original.book = reopened.book) :
    decide rules stream (original.regional.streams stream) original.book request =
      decide rules stream (reopened.regional.streams stream) reopened.book request := by
  rw [source, book]

omit [DecidableEq Ticket] in
theorem another_append_cannot_reuse_the_spent_offset
    {rules : Rules slots Payload Ticket} {stream : Nat} {source : Source slots Payload} {book : Book}
    {request retry : Request Payload Ticket} {window : Window}
    (present : book.windows request.version = some window)
    (allowed : LocalChecks rules stream source book window request)
    (sameWindow : retry.version = request.version) (sameOffset : retry.offset = request.offset) :
    let after := decide rules stream source book request
    (decide rules stream after.1 after.2.1 retry).2.2 = .refused := by
  rw [eligible_append_uses_the_original_ordered_reducer present allowed]
  have positive := allowed.positive
  have stale : ¬ LocalChecks rules stream
      (UnifiedSource.replay (rules.regional.limits stream) (rules.regional.source stream)
        source [appendCommand request]).1 (advanceWindow rules request book window)
      {window with nextLsn := request.lsn + 1, spent := request.offset + rules.cost request.payload} retry := by
    intro checked
    have offset := exactCursor checked
    simp at offset
    omega
  have advanced : (advanceWindow rules request book window).windows retry.version =
      some {window with nextLsn := request.lsn + 1, spent := request.offset + rules.cost request.payload} := by
    simp [advanceWindow, setSlot, sameWindow]
  simp [decide, advanced, stale]

private theorem refused_append_projects {rules : Rules slots Payload Ticket}
    (state : State slots Payload Ticket) (stream : Nat) (writer : Kernel.Writer) :
    let source := state.regional.streams stream
    RegionalRetirement.Step rules.regional state.regional
      (useDecision state stream ({source with position := source.position + 1}, state.book, .refused)).regional := by
  let command : UnifiedSource.Command slots Nat Payload Ticket := .stream (.read writer 0)
  let applied := (UnifiedSource.replay (rules.regional.limits stream) (rules.regional.source stream)
    (state.regional.streams stream) [command]).1
  have event : RegionalRetirement.Step rules.regional state.regional
      {state.regional with streams := setSlot state.regional.streams stream applied} :=
    .ordered stream command
  simpa [useDecision, applied, command, UnifiedSource.replay, UnifiedSource.decide,
    UnifiedSource.Routine, OrderedApplication.decideCommand] using event

theorem every_funded_step_refines_the_regional_authority
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket}
    (step : Step rules state next) :
    next.regional = state.regional ∨ RegionalRetirement.Step rules.regional state.regional next.regional := by
  cases step with
  | regional event _ _ => exact .inr event
  | publish => exact .inl rfl
  | prune => exact .inl rfl
  | append stream request =>
      cases present : state.book.windows request.version with
      | none =>
        rw [no_window_means_no_append_payment_or_receipt present]
        exact .inr (refused_append_projects state stream request.writer)
      | some window =>
        by_cases allowed : LocalChecks rules stream (state.regional.streams stream) state.book window request
        · rw [eligible_append_uses_the_original_ordered_reducer present allowed]
          exact .inr (.ordered stream (appendCommand request))
        · have refused : (decide rules stream (state.regional.streams stream) state.book request).2.2 = .refused :=
            by simp [decide, present, allowed]
          rw [refusal_does_not_spend_the_window refused]
          exact .inr (refused_append_projects state stream request.writer)

theorem every_funded_trace_preserves_regional_and_append_bounds
    {rules : Rules slots Payload Ticket} {initial final : State slots Payload Ticket}
    (safe : RegionalRetirement.Sound rules.regional initial.regional) (funded : Funded rules initial)
    (trace : Trace rules initial final) :
    RegionalRetirement.Sound rules.regional final.regional ∧ Funded rules final := by
  refine ⟨?_, funding_is_preserved_across_arbitrary_traces funded trace⟩
  induction trace with
  | same => exact safe
  | next _ step previous =>
      rcases every_funded_step_refines_the_regional_authority step with same | event
      · exact same.symm ▸ previous
      · exact RegionalRetirement.the_regional_machine_preserves_stream_and_pool_bounds previous event

def Consumed (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (version offset : Nat) : Prop :=
  version ≤ state.book.latest (rules.owner version) ∧
    ∀ window, state.book.windows version = some window → offset ≤ window.spent

private theorem consumed_survives_step
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket}
    {version offset : Nat} (consumed : Consumed rules state version offset)
    (step : Step rules state next) : Consumed rules next version offset := by
  cases step with
  | regional => exact consumed
  | publish stream fresh writer allowed =>
      have notSame : version ≠ fresh := by
        intro same
        subst fresh
        have already := consumed.1
        rw [allowed.1] at already
        exact Nat.not_lt_of_ge already allowed.2.1
      refine ⟨?_, ?_⟩
      · by_cases owner : rules.owner version = stream
        · have advances := allowed.2.1
          have before := consumed.1
          rw [owner] at before
          simp [openWindow, setSlot, owner]
          omega
        · simpa [openWindow, setSlot, owner] using consumed.1
      · intro window live
        exact consumed.2 window (by simpa [openWindow, setSlot, notSame] using live)
  | prune removed =>
      refine ⟨consumed.1, ?_⟩
      intro window live
      by_cases same : version = removed
      · simp [pruneWindow, setSlot, same] at live
      · exact consumed.2 window (by simpa [pruneWindow, setSlot, same] using live)
  | append stream request =>
      cases present : state.book.windows request.version with
      | none => simpa [useDecision, decide, present, Consumed] using consumed
      | some current =>
        by_cases allowed : LocalChecks rules stream (state.regional.streams stream) state.book current request
        · rw [eligible_append_uses_the_original_ordered_reducer present allowed]
          refine ⟨consumed.1, ?_⟩
          intro window live
          by_cases same : version = request.version
          · subst version
            have before := consumed.2 current present
            have sameOffset := exactCursor allowed
            simp [useDecision, advanceWindow, setSlot] at live
            subst window
            simp
            omega
          · exact consumed.2 window (by simpa [useDecision, advanceWindow, setSlot, same] using live)
        · simpa [useDecision, decide, present, allowed, Consumed] using consumed

theorem an_append_range_stays_unavailable_through_all_later_steps
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket} {stream : Nat}
    {request : Request Payload Ticket} {window : Window}
    (funded : Funded rules state) (present : state.book.windows request.version = some window)
    (allowed : LocalChecks rules stream (state.regional.streams stream) state.book window request)
    (later : Trace rules (useDecision state stream
      (decide rules stream (state.regional.streams stream) state.book request)) next) :
    Consumed rules next request.version (request.offset + rules.cost request.payload) := by
  have initial : Consumed rules (useDecision state stream
      (decide rules stream (state.regional.streams stream) state.book request))
      request.version (request.offset + rules.cost request.payload) := by
    rw [eligible_append_uses_the_original_ordered_reducer present allowed]
    obtain ⟨_, _, owner, issued⟩ := funded request.version window present
    refine ⟨by simpa [useDecision, advanceWindow, owner] using issued, ?_⟩
    intro updated exactWindow
    simp [useDecision, advanceWindow, setSlot] at exactWindow
    subst updated
    exact Nat.le_refl _
  induction later with
  | same => exact initial
  | next _ step previous => exact consumed_survives_step previous step

theorem any_history_growth_uses_the_funded_decision
    {rules : Rules slots Payload Ticket} {state next : State slots Payload Ticket} {stream : Nat}
    (step : Step rules state next)
    (grows : (next.regional.streams stream).core.stream.history ≠
      (state.regional.streams stream).core.stream.history) :
    ∃ request,
      next = useDecision state stream (decide rules stream (state.regional.streams stream) state.book request) ∧
      (decide rules stream (state.regional.streams stream) state.book request).2.2 =
        .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩) := by
  cases step with
  | regional _ same _ => exact False.elim (grows (same stream))
  | publish => exact False.elim (grows rfl)
  | prune => exact False.elim (grows rfl)
  | append origin request =>
      by_cases same : stream = origin
      · subst origin
        refine ⟨request, rfl, ?_⟩
        cases present : state.book.windows request.version with
        | none =>
          rw [no_window_means_no_append_payment_or_receipt present] at grows
          exact False.elim (grows (by simp [useDecision, setSlot]))
        | some window =>
          by_cases allowed : LocalChecks rules stream (state.regional.streams stream) state.book window request
          · rw [eligible_append_uses_the_original_ordered_reducer present allowed]
          · have refused : (decide rules stream (state.regional.streams stream) state.book request).2.2 = .refused :=
              by simp [decide, present, allowed]
            rw [refusal_does_not_spend_the_window refused] at grows
            exact False.elim (grows (by simp [useDecision, setSlot]))
      · exact False.elim (grows (by simp [useDecision, setSlot, same]))

#print axioms eligible_append_uses_the_original_ordered_reducer
#print axioms original_reducer_has_the_same_receipt
#print axioms no_window_means_no_append_payment_or_receipt
#print axioms refusal_does_not_spend_the_window
#print axioms regional_steps_preserve_every_window_charge
#print axioms funding_is_preserved_across_arbitrary_traces
#print axioms a_successful_append_spends_only_its_own_prepaid_range
#print axioms replay_recovers_the_same_outcome_under_any_current_pool
#print axioms another_append_cannot_reuse_the_spent_offset
#print axioms every_funded_step_refines_the_regional_authority
#print axioms every_funded_trace_preserves_regional_and_append_bounds
#print axioms an_append_range_stays_unavailable_through_all_later_steps
#print axioms any_history_growth_uses_the_funded_decision

end FundedAppend
