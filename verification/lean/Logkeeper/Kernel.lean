import Std

namespace Logkeeper

set_option warningAsError true

namespace Kernel

structure Placement where
  group : Nat
  generation : Nat
  deriving DecidableEq

structure Writer where
  placement : Placement
  epoch : Nat
  holder : Nat
  deriving DecidableEq

inductive Authority where
  | active (writer : Writer)
  | vacant (previous : Writer)
  | sealed (target : Placement) (priorWriter : Writer)
  | retired
  deriving DecidableEq

def AtWriter (authority : Authority) (writer : Writer) : Prop :=
  authority = .active writer ∨ authority = .vacant writer

@[simp] theorem atWriter_active (current expected : Writer) :
    AtWriter (.active current) expected ↔ current = expected := by
  simp [AtWriter]

@[simp] theorem atWriter_vacant (previous expected : Writer) :
    AtWriter (.vacant previous) expected ↔ previous = expected := by
  simp [AtWriter]

structure Entry (Payload : Type) where
  epoch : Nat
  bytes : Payload

structure Limits where
  recovery : Nat
  retained : Nat

inductive ReplayStatus where
  | unused
  | prepared (firstLsn : Nat)
  | holding (firstLsn : Nat)
  deriving DecidableEq

def replaceReplay (table : Nat → ReplayStatus) (id : Nat) (status : ReplayStatus) :
    Nat → ReplayStatus :=
  fun queried => if queried = id then status else table queried

structure State (Payload : Type) where
  authority : Authority
  history : List (Entry Payload) := []
  checkpointEnd : Nat := 0
  firstRetained : Nat := 0
  replays : Nat → ReplayStatus := fun _ => .unused
  replayIssued : Nat := 0

def initial {Payload : Type} (writer : Writer) : State Payload :=
  {authority := .active writer}

def RecoverableAt {Payload : Type} (state : State Payload) (lsn : Nat) : Prop :=
  state.firstRetained ≤ lsn

def MatchesReceipt {Payload : Type}
    (state : State Payload) (lsn : Nat) (entry : Entry Payload) : Prop :=
  RecoverableAt state lsn ∧ state.history[lsn]? = some entry

def barrier {Payload : Type} (state : State Payload) (writer : Writer) : Option Nat :=
  if state.authority = .active writer then some state.history.length else none

structure Valid {Payload : Type} (limits : Limits) (state : State Payload) : Prop where
  trimCertified : state.firstRetained ≤ state.checkpointEnd
  checkpointCommitted : state.checkpointEnd ≤ state.history.length
  replaySafe : ∀ id lsn, state.replays id = .holding lsn → state.firstRetained ≤ lsn
  recoveryBound : state.history.length - state.checkpointEnd ≤ limits.recovery
  retainedBound : state.history.length - state.firstRetained ≤ limits.retained

structure AppendAdmissible {Payload : Type} (limits : Limits) (state : State Payload)
    (writer : Writer) (lsn : Nat) : Prop where
  authorized : state.authority = .active writer
  ordered : lsn = state.history.length
  recoveryRoom : state.history.length + 1 - state.checkpointEnd ≤ limits.recovery
  retainedRoom : state.history.length + 1 - state.firstRetained ≤ limits.retained

theorem wrong_lsn_refused {Payload : Type} {limits : Limits} {state : State Payload}
    {writer : Writer} {lsn : Nat} (stale : lsn ≠ state.history.length) :
    ¬ AppendAdmissible limits state writer lsn := fun admitted => stale admitted.ordered

theorem stale_writer_refused {Payload : Type} {limits : Limits} {state : State Payload}
    {writer : Writer} {lsn : Nat} (stale : state.authority ≠ .active writer) :
    ¬ AppendAdmissible limits state writer lsn := fun admitted => stale admitted.authorized

inductive Step {Payload : Type} (limits : Limits) : State Payload → State Payload → Prop
  | append {state writer} (lsn : Nat) (payload : Payload)
      (admitted : AppendAdmissible limits state writer lsn) :
      Step limits state {state with history := state.history ++ [⟨writer.epoch, payload⟩]}
  | publish {state writer} (checkpoint : Nat)
      (authorized : state.authority = .active writer)
      (advances : state.checkpointEnd ≤ checkpoint)
      (committed : checkpoint ≤ state.history.length) :
      Step limits state {state with checkpointEnd := checkpoint}
  | prepareReplay {state writer} (lsn : Nat)
      (authorized : state.authority = .active writer) :
      Step limits state {state with
        replayIssued := state.replayIssued + 1
        replays := replaceReplay state.replays (state.replayIssued + 1) (.prepared lsn)}
  | admitReplay {state writer} (id lsn : Nat)
      (authorized : state.authority = .active writer)
      (reserved : state.replays id = .prepared lsn)
      (available : state.firstRetained ≤ lsn) (contains : lsn < state.history.length) :
      Step limits state {state with replays := replaceReplay state.replays id (.holding lsn)}
  | releaseReplay {state} (id : Nat) (issued : id ≤ state.replayIssued) :
      Step limits state {state with replays := replaceReplay state.replays id .unused}
  | trim {state writer} (cut : Nat)
      (authorized : state.authority = .active writer)
      (advances : state.firstRetained ≤ cut)
      (published : cut ≤ state.checkpointEnd)
      (protects : ∀ id lsn, state.replays id = .holding lsn → cut ≤ lsn) :
      Step limits state {state with firstRetained := cut}
  | withdrawWriter {state writer} (authorized : state.authority = .active writer) :
      Step limits state {state with authority := .vacant writer}
  | fenceWriter {state priorWriter} (newWriter : Writer)
      (authorized : AtWriter state.authority priorWriter)
      (samePlacement : newWriter.placement = priorWriter.placement)
      (higher : priorWriter.epoch < newWriter.epoch) :
      Step limits state {state with authority := .active newWriter}
  | freeze {state writer} (target : Placement)
      (authorized : state.authority = .active writer)
      (advances : writer.placement.generation < target.generation)
      (relocates : writer.placement.group ≠ target.group) :
      Step limits state {state with authority := .sealed target writer}
  | activate {state target priorWriter} (installed : List (Entry Payload))
      (sealed : state.authority = .sealed target priorWriter)
      (exactCut : installed = state.history) :
      Step limits state {state with history := installed,
                                    authority := .active {priorWriter with placement := target}}
  | retire {state writer} (authorized : AtWriter state.authority writer) :
      Step limits state {state with authority := .retired}

theorem step_preserves_valid {Payload : Type} {limits : Limits} {before after : State Payload}
    (valid : Valid limits before) (step : Step limits before after) : Valid limits after := by
  obtain ⟨trimCertified, checkpointCommitted, replaySafe, recoveryBound, retainedBound⟩ := valid
  cases step with
  | append _ _ admitted =>
      refine ⟨trimCertified, ?_, replaySafe, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · simpa only [List.length_append, List.length_singleton] using admitted.recoveryRoom
      · simpa only [List.length_append, List.length_singleton] using admitted.retainedRoom
  | publish checkpoint _ advances committed =>
      refine ⟨Nat.le_trans trimCertified advances, committed, replaySafe, ?_, retainedBound⟩
      change before.history.length - checkpoint ≤ limits.recovery
      omega
  | prepareReplay lsn _ =>
      refine ⟨trimCertified, checkpointCommitted, ?_, recoveryBound, retainedBound⟩
      intro id first live
      by_cases same : id = before.replayIssued + 1
      · simp [replaceReplay, same] at live
      · exact replaySafe id first (by simpa [replaceReplay, same] using live)
  | admitReplay id lsn _ _ available _ =>
      refine ⟨trimCertified, checkpointCommitted, ?_, recoveryBound, retainedBound⟩
      intro found first live
      by_cases same : found = id
      · have exactLsn : lsn = first := ReplayStatus.holding.inj (by simpa [replaceReplay, same] using live)
        exact exactLsn ▸ available
      · exact replaySafe found first (by simpa [replaceReplay, same] using live)
  | releaseReplay id _ =>
      refine ⟨trimCertified, checkpointCommitted, ?_, recoveryBound, retainedBound⟩
      intro found first live
      by_cases same : found = id
      · simp [replaceReplay, same] at live
      · exact replaySafe found first (by simpa [replaceReplay, same] using live)
  | trim cut _ advances published protects =>
      refine ⟨published, checkpointCommitted, protects, recoveryBound, ?_⟩
      change before.history.length - cut ≤ limits.retained
      omega
  | withdrawWriter | fenceWriter => exact ⟨trimCertified, checkpointCommitted, replaySafe, recoveryBound, retainedBound⟩
  | freeze => exact ⟨trimCertified, checkpointCommitted, replaySafe, recoveryBound, retainedBound⟩
  | activate _ _ exactCut =>
      subst_vars
      exact ⟨trimCertified, checkpointCommitted, replaySafe, recoveryBound, retainedBound⟩
  | retire => exact ⟨trimCertified, checkpointCommitted, replaySafe, recoveryBound, retainedBound⟩

inductive Trace {Payload : Type} (limits : Limits) : State Payload → State Payload → Prop
  | same (state : State Payload) : Trace limits state state
  | next {first before after} : Trace limits first before → Step limits before after →
      Trace limits first after

theorem every_trace_preserves_bounds {Payload : Type} {limits : Limits}
    {first last : State Payload} (valid : Valid limits first) (trace : Trace limits first last) :
    Valid limits last := by
  induction trace with
  | same => exact valid
  | next _ step prior => exact step_preserves_valid prior step

theorem initial_valid {Payload : Type} (limits : Limits) (writer : Writer) :
    Valid limits (initial writer : State Payload) := by
  constructor <;> simp [initial]

theorem step_extends_history {Payload : Type} {limits : Limits} {before after : State Payload}
    (step : Step limits before after) : ∃ suffix, after.history = before.history ++ suffix := by
  cases step with
  | append _ payload _ => exact ⟨[⟨_, payload⟩], rfl⟩
  | activate _ _ exactCut => exact ⟨[], by simpa using exactCut⟩
  | _ => exact ⟨[], by simp⟩

theorem trace_extends_history {Payload : Type} {limits : Limits} {first last : State Payload}
    (trace : Trace limits first last) : ∃ suffix, last.history = first.history ++ suffix := by
  induction trace with
  | same => exact ⟨[], by simp⟩
  | next _ step prior =>
      obtain ⟨earlier, prefixEq⟩ := prior
      obtain ⟨later, suffixEq⟩ := step_extends_history step
      exact ⟨earlier ++ later, by simp [suffixEq, prefixEq, List.append_assoc]⟩

theorem retired_absorbs_steps {Payload : Type} {limits : Limits} {before after : State Payload}
    (closed : before.authority = .retired) (step : Step limits before after) :
    after.authority = .retired := by
  cases step <;> simp_all [AtWriter]

theorem retired_absorbs_trace {Payload : Type} {limits : Limits} {first last : State Payload}
    (closed : first.authority = .retired) (trace : Trace limits first last) :
    last.authority = .retired := by
  induction trace with
  | same => exact closed
  | next _ step prior => exact retired_absorbs_steps prior step

theorem receipt_committed_exact {Payload : Type}
    {state : State Payload} {lsn : Nat} {entry : Entry Payload}
    (receipt : MatchesReceipt state lsn entry) :
    lsn < state.history.length ∧ state.history[lsn]? = some entry := by
  obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp receipt.2
  exact ⟨inRange, receipt.2⟩

theorem barrier_reports_committed_end {Payload : Type}
    {state : State Payload} {writer : Writer} {cut : Nat}
    (response : barrier state writer = some cut) :
    state.authority = .active writer ∧ cut = state.history.length := by
  unfold barrier at response
  split at response
  next authorized => exact ⟨authorized, (Option.some.inj response).symm⟩
  next => simp at response

theorem append_receipt_program {Payload : Type} {limits : Limits} {state : State Payload}
    {writer : Writer} (payload : Payload) (valid : Valid limits state)
    (authorized : state.authority = .active writer)
    (recoveryRoom : state.history.length + 1 - state.checkpointEnd ≤ limits.recovery)
    (retainedRoom : state.history.length + 1 - state.firstRetained ≤ limits.retained) :
    ∃ after, Step limits state after ∧
      MatchesReceipt after state.history.length ⟨writer.epoch, payload⟩ := by
  let after : State Payload := {state with history := state.history ++ [⟨writer.epoch, payload⟩]}
  refine ⟨after, .append (writer := writer) state.history.length payload
    ⟨authorized, rfl, recoveryRoom, retainedRoom⟩, ?_⟩
  refine ⟨Nat.le_trans valid.trimCertified valid.checkpointCommitted, ?_⟩
  change (state.history ++ [⟨writer.epoch, payload⟩])[state.history.length]? = _
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem retained_receipt_survives {Payload : Type} {limits : Limits}
    {first last : State Payload} {lsn : Nat} {entry : Entry Payload}
    (trace : Trace limits first last) (receipt : MatchesReceipt first lsn entry)
    (stillRetained : last.firstRetained ≤ lsn) : MatchesReceipt last lsn entry := by
  obtain ⟨inRange, committed⟩ := receipt_committed_exact receipt
  obtain ⟨suffix, later⟩ := trace_extends_history trace
  refine ⟨stillRetained, ?_⟩
  rw [later, List.getElem?_append_left inRange]
  exact committed

theorem two_durable_locations_survive_one_loss {Zone : Type} {stored : Zone → Prop}
    {first other : Zone} (distinct : first ≠ other) (atFirst : stored first)
    (atOther : stored other) (lost : Zone) : ∃ zone, zone ≠ lost ∧ stored zone := by
  classical
  by_cases dropsFirst : first = lost
  · exact ⟨other, (dropsFirst ▸ distinct).symm, atOther⟩
  · exact ⟨first, dropsFirst, atFirst⟩

theorem replay_issuance_is_monotone {Payload : Type} {limits : Limits}
    {before after : State Payload} (step : Step limits before after) :
    before.replayIssued ≤ after.replayIssued := by
  cases step <;> simp

theorem spent_replay_stays_unused {Payload : Type} {limits : Limits}
    {before after : State Payload} {id : Nat} (old : id ≤ before.replayIssued)
    (unused : before.replays id = .unused) (step : Step limits before after) :
    after.replays id = .unused := by
  cases step with
  | prepareReplay lsn _ =>
      have fresh : id ≠ before.replayIssued + 1 := by omega
      simpa [replaceReplay, fresh] using unused
  | admitReplay admitted lsn _ reserved _ _ =>
      have matching : before.replays admitted = .prepared lsn := reserved
      have separate : id ≠ admitted := by
        intro same
        rw [← same, unused] at matching
        contradiction
      simpa [replaceReplay, separate] using unused
  | releaseReplay released _ => simp [replaceReplay, unused]
  | _ => exact unused

theorem close_permanently_refuses_delayed_admission {Payload : Type} {limits : Limits}
    {first last : State Payload} {id : Nat} (old : id ≤ first.replayIssued)
    (unused : first.replays id = .unused) (trace : Trace limits first last) :
    last.replays id = .unused := by
  have staysUnused : id ≤ last.replayIssued ∧ last.replays id = .unused := by
    induction trace with
    | same => exact ⟨old, unused⟩
    | next _ step prior =>
        exact ⟨Nat.le_trans prior.1 (replay_issuance_is_monotone step),
          spent_replay_stays_unused prior.1 prior.2 step⟩
  exact staysUnused.2

theorem prepare_and_admit_replay_program {Payload : Type} {limits : Limits}
    {state : State Payload} {writer : Writer} (lsn : Nat)
    (authorized : state.authority = .active writer)
    (available : state.firstRetained ≤ lsn) (contains : lsn < state.history.length) :
    ∃ after, Trace limits state after ∧ after.replays (state.replayIssued + 1) = .holding lsn := by
  let id := state.replayIssued + 1
  let reservation : State Payload := {state with
    replayIssued := id
    replays := replaceReplay state.replays id (.prepared lsn)}
  let admitted : State Payload := {reservation with
    replays := replaceReplay reservation.replays id (.holding lsn)}
  have issued : Step limits state reservation := .prepareReplay lsn authorized
  have admittedStep : Step limits reservation admitted :=
    .admitReplay id lsn authorized (by simp [reservation, replaceReplay]) available contains
  exact ⟨admitted, .next (.next (.same state) issued) admittedStep, by simp [admitted, replaceReplay, id]⟩

theorem closing_replay_preserves_others {Payload : Type} {limits : Limits}
    {state : State Payload} (id : Nat) (issued : id ≤ state.replayIssued) :
    ∃ after, Step limits state after ∧ after.replays id = .unused ∧
      ∀ other, other ≠ id → after.replays other = state.replays other := by
  refine ⟨_, .releaseReplay id issued, by simp [replaceReplay], ?_⟩
  intro other distinct
  simp [replaceReplay, distinct]

#print axioms initial_valid
#print axioms every_trace_preserves_bounds
#print axioms trace_extends_history
#print axioms retired_absorbs_trace
#print axioms receipt_committed_exact
#print axioms barrier_reports_committed_end
#print axioms append_receipt_program
#print axioms wrong_lsn_refused
#print axioms stale_writer_refused
#print axioms retained_receipt_survives
#print axioms two_durable_locations_survive_one_loss
#print axioms replay_issuance_is_monotone
#print axioms spent_replay_stays_unused
#print axioms close_permanently_refuses_delayed_admission
#print axioms prepare_and_admit_replay_program
#print axioms closing_replay_preserves_others

end Kernel

end Logkeeper
