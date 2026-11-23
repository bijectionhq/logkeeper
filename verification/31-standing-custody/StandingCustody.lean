import ReconfiguredReads

set_option warningAsError true

namespace StandingCustody

inductive Phase where
  | open
  | sealed
  | released
  deriving DecidableEq

inductive Status where
  | fresh
  | using
  | finished
  | stopped
  deriving DecidableEq

structure Basis (Extent : Type) where
  root : Extent
  suffix : List Extent

def Basis.Needs (basis : Basis Extent) (extent : Extent) : Prop :=
  extent = basis.root ∨ extent ∈ basis.suffix

structure Window (Extent : Type) where
  basis : Basis Extent
  session : Nat

structure State (Reader Extent : Type) where
  phase : Phase
  currentSession : Nat
  status : Reader → Status
  resident : Extent → Prop

def put [DecidableEq Reader] (status : Reader → Status) (read : Reader) (next : Status) :
    Reader → Status :=
  fun id => if id = read then next else status id

def stopAll (status : Reader → Status) : Reader → Status :=
  fun id => if status id = .using then .stopped else status id

def CanRelease (state : State Reader Extent) : Prop :=
  state.phase = .sealed ∧ ∀ id, state.status id ≠ .using

def CanReclaim (window : Window Extent) (state : State Reader Extent) (extent : Extent) : Prop :=
  state.phase = .released ∨ ¬ window.basis.Needs extent

def Charged (state : State Reader Extent) : Prop :=
  state.phase ≠ .released

def Held (window : Window Extent) (state : State Reader Extent) : Prop :=
  ∀ extent, window.basis.Needs extent → state.resident extent

structure Sound (window : Window Extent) (state : State Reader Extent) : Prop where
  coverage : Charged state → Held window state
  liveCharge : ∀ id, state.status id = .using → Charged state

inductive Step [DecidableEq Reader] (window : Window Extent)
    (effectiveStop : State Reader Extent → Prop) : State Reader Extent → State Reader Extent → Prop
  | admit {state} (id : Reader) (openGate : state.phase = .open)
      (sameSession : state.currentSession = window.session) (fresh : state.status id = .fresh) :
      Step window effectiveStop state {state with status := put state.status id .using}
  | finish {state} (id : Reader) (inUse : state.status id = .using) :
      Step window effectiveStop state {state with status := put state.status id .finished}
  | closeEntrance {state} (openGate : state.phase = .open) :
      Step window effectiveStop state {state with phase := .sealed}
  | stop {state} (closedGate : state.phase = .sealed) (attested : effectiveStop state) :
      Step window effectiveStop state {state with status := stopAll state.status}
  | release {state} (ready : CanRelease state) :
      Step window effectiveStop state {state with phase := .released}
  | restart {state} :
      Step window effectiveStop state {state with currentSession := state.currentSession + 1}
  | reclaim {state} (extent : Extent) (allowed : CanReclaim window state extent) :
      Step window effectiveStop state {state with resident := fun item => state.resident item ∧ item ≠ extent}

inductive Trace [DecidableEq Reader] (window : Window Extent)
    (effectiveStop : State Reader Extent → Prop) : State Reader Extent → State Reader Extent → Prop
  | same (state : State Reader Extent) : Trace window effectiveStop state state
  | next {first before after} : Trace window effectiveStop first before → Step window effectiveStop before after →
      Trace window effectiveStop first after

variable {Reader Extent Replica Payload : Type} [DecidableEq Reader]

theorem step_preserves_coverage_and_charges {window : Window Extent} {before after : State Reader Extent}
    {stop : State Reader Extent → Prop} (sound : Sound window before) (step : Step window stop before after) :
    Sound window after := by
  cases step with
  | admit read openGate _ _ =>
      exact ⟨sound.coverage, fun _ _ => by simp [Charged, openGate]⟩
  | finish read _ =>
      refine ⟨sound.coverage, ?_⟩
      intro id live
      by_cases same : id = read
      · simp [put, same] at live
      · exact sound.liveCharge id (by simpa [put, same] using live)
  | closeEntrance openGate =>
      exact ⟨fun _ => sound.coverage (by simp [Charged, openGate]), fun _ _ => by simp [Charged]⟩
  | stop closedGate _ =>
      exact ⟨sound.coverage, fun _ _ => by simp [Charged, closedGate]⟩
  | release ready =>
      refine ⟨fun charged => False.elim (charged rfl), ?_⟩
      intro id live
      have drained : before.status id ≠ .using := by
        exact ready.2 id
      exact False.elim (drained live)
  | restart =>
      exact ⟨sound.coverage, sound.liveCharge⟩
  | reclaim extent allowed =>
      refine ⟨?_, sound.liveCharge⟩
      intro charged item needed
      have preserves : ¬ window.basis.Needs extent := by
        exact allowed.resolve_left charged
      exact ⟨sound.coverage charged item needed, fun equal => preserves (equal ▸ needed)⟩

theorem trace_preserves_coverage_and_charges {window : Window Extent}
    {initial current : State Reader Extent} {stop : State Reader Extent → Prop}
    (sound : Sound window initial) (trace : Trace window stop initial current) : Sound window current := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact step_preserves_coverage_and_charges prior step

theorem arbitrary_trace_retains_complete_basis {window : Window Extent}
    {initial current : State Reader Extent} {stop : State Reader Extent → Prop}
    (sound : Sound window initial) (trace : Trace window stop initial current) (id : Reader)
    (usingBasis : current.status id = .using) : Held window current := by
  have safe := trace_preserves_coverage_and_charges sound trace
  exact safe.coverage (safe.liveCharge id usingBasis)

theorem closing_entrance_leaves_its_charge {window : Window Extent} {before : State Reader Extent}
    {stop : State Reader Extent → Prop} (openGate : before.phase = .open) :
    ∃ after, Step window stop before after ∧ Charged after ∧ after.status = before.status :=
  ⟨{before with phase := .sealed}, .closeEntrance openGate, by simp [Charged], rfl⟩

theorem closed_gate_cannot_reopen {window : Window Extent} {before after : State Reader Extent}
    {stop : State Reader Extent → Prop} (closed : before.phase ≠ .open)
    (trace : Trace window stop before after) : after.phase ≠ .open := by
  induction trace with
  | same => exact closed
  | next _ step prior =>
      cases step <;> first | exact prior | simp

theorem stopped_reader_cannot_resume {window : Window Extent} {before after : State Reader Extent}
    {stop : State Reader Extent → Prop} (id : Reader) (stopped : before.status id = .stopped)
    (trace : Trace window stop before after) : after.status id = .stopped := by
  induction trace with
  | same => exact stopped
  | next _ step prior =>
      cases step with
      | admit other _ _ fresh =>
          by_cases same : id = other
          · subst other
            simp [prior] at fresh
          · simpa [put, same] using prior
      | finish other active =>
          by_cases same : id = other
          · subst other
            simp [prior] at active
          · simpa [put, same] using prior
      | stop _ _ => simp [stopAll, prior]
      | _ => exact prior

theorem restart_preserves_old_borrow_and_excludes_its_gate {window : Window Extent}
    {before : State Reader Extent} {stop : State Reader Extent → Prop}
    (sameSession : before.currentSession = window.session) (id : Reader) (live : before.status id = .using) :
    ∃ after, Step window stop before after ∧ after.currentSession ≠ window.session ∧ after.status id = .using :=
  ⟨{before with currentSession := before.currentSession + 1}, .restart, by simp [sameSession], live⟩

theorem two_reads_share_one_registration {window : Window Extent} {before : State Reader Extent}
    {stop : State Reader Extent → Prop} (first second : Reader) (distinct : first ≠ second)
    (openGate : before.phase = .open) (sameSession : before.currentSession = window.session)
    (firstFresh : before.status first = .fresh) (secondFresh : before.status second = .fresh) :
    ∃ after, Trace window stop before after ∧ after.phase = .open ∧
      after.status first = .using ∧ after.status second = .using := by
  let middle := {before with status := put before.status first .using}
  let after := {middle with status := put middle.status second .using}
  have firstStep : Step window stop before middle := .admit first openGate sameSession firstFresh
  have staysFresh : middle.status second = .fresh := by
    simpa [middle, put, Ne.symm distinct] using secondFresh
  have secondStep : Step window stop middle after := .admit second openGate sameSession staysFresh
  exact ⟨after, .next (.next (.same _) firstStep) secondStep, openGate,
    by simp [after, middle, put, distinct], by simp [after, put]⟩

abbrev Command := OrderedApplication.Command
abbrev ChoiceTrace := ReadIndexProof.ChoiceTrace
abbrev Invocation := ReadIndexProof.Invocation
abbrev Round := ReadIndexProof.Round

def CoversFloor (observed : Nat) (applied : List (Command Payload)) : Prop :=
  observed ≤ applied.length

def PinsSnapshot (window : Window Extent) (resolve : SnapshotAdmission.Basis → Basis Extent)
    (view : SnapshotAdmission.View) : Prop :=
  window.basis = resolve (SnapshotAdmission.currentBasis view)

theorem standing_read_refines_the_captured_cut
    {limits : Kernel.Limits} {initial : Kernel.State Payload} {writer : Kernel.Writer}
    {trace : ChoiceTrace (Command Payload)} {call : Invocation} {round : Round Replica (Command Payload)}
    {scope : ReadIndexProof.Scope} {instant : Nat} {snapshot : List (Command Payload)}
    {view : SnapshotAdmission.View} {window : Window Extent}
    {resolve : SnapshotAdmission.Basis → Basis Extent}
    {before now : State Reader Extent} {stop : State Reader Extent → Prop}
    (floor : ReconfiguredReads.VerifiedFloor trace call round)
    (unit : ReadIndexProof.UnitChoices trace)
    (certified : ReconfiguredReads.Reservation trace call round scope limits initial writer instant snapshot view)
    (registered : PinsSnapshot window resolve view)
    (sound : Sound window before) (history : Trace window stop before now)
    (id : Reader) (borrowed : now.status id = .using) :
    ∃ point, call.started ≤ point ∧ point ≤ instant ∧ instant ≤ call.replied ∧
      round.invocation = call.nonce ∧ trace.chosen point = snapshot ∧
      Kernel.barrier (OrderedApplication.replay limits initial (trace.chosen point)).1 writer =
        some (SnapshotAdmission.currentBasis view).stop ∧
      ∀ extent, (resolve (SnapshotAdmission.currentBasis view)).Needs extent → now.resident extent := by
  obtain ⟨opening, covers, applied⟩ := ReconfiguredReads.reservation_covers_invocation_choice floor certified
  obtain ⟨point, inside, beforeReserve, exactLength⟩ :=
    ReadIndexProof.any_intermediate_length_occurs trace unit certified.afterRound
      (Nat.le_trans opening covers) applied.length_le
  have exactState := ReadIndexProof.matching_prefix_is_exact_at_cut beforeReserve exactLength applied
  have holds := arbitrary_trace_retains_complete_basis sound history id borrowed
  have sameBasis : window.basis = resolve (SnapshotAdmission.currentBasis view) := by
    exact registered
  refine ⟨point, Nat.le_trans floor.fresh inside, beforeReserve, certified.beforeReply,
    floor.invocation, exactState, ?_, fun extent needed => holds extent (sameBasis.symm ▸ needed)⟩
  simp [exactState, Kernel.barrier, certified.authorized, SnapshotAdmission.currentBasis,
    certified.materialized]

theorem fresh_floor_excludes_new_invocations_after_terminal
    {limits : Kernel.Limits} {initial : Kernel.State Payload} {writer : Kernel.Writer}
    {trace : ChoiceTrace (Command Payload)} {call : Invocation} {round : Round Replica (Command Payload)}
    {retiredAt instant : Nat} {snapshot : List (Command Payload)}
    (checked : ReconfiguredReads.VerifiedFloor trace call round)
    (terminalBeforeInvocation : retiredAt ≤ call.started)
    (afterRound : round.opened ≤ instant)
    (closed : (OrderedApplication.replay limits initial (trace.chosen retiredAt)).1.authority = .retired)
    (applied : snapshot <+: trace.chosen instant)
    (covers : CoversFloor round.target.length snapshot)
    (active : (OrderedApplication.replay limits initial snapshot).1.authority = .active writer) : False := by
  have beforeRound : retiredAt ≤ round.opened := Nat.le_trans terminalBeforeInvocation checked.fresh
  have includesTerminalLength : (trace.chosen retiredAt).length ≤ snapshot.length := by
    have opening := (trace.extendsEarlier retiredAt round.opened beforeRound).length_le
    have ready : round.target.length ≤ snapshot.length := by
      exact covers
    exact Nat.le_trans opening (Nat.le_trans checked.coversOpening ready)
  have includesTerminal := List.prefix_of_prefix_length_le
    (trace.extendsEarlier retiredAt instant (Nat.le_trans beforeRound afterRound))
    applied includesTerminalLength
  obtain ⟨suffix, rfl⟩ := includesTerminal
  rw [OrderedApplication.replay_append] at active
  have remainsClosed := Kernel.retired_absorbs_trace closed
    (OrderedApplication.replay_projects_to_kernel limits
      (OrderedApplication.replay limits initial (trace.chosen retiredAt)).1 suffix)
  rw [remainsClosed] at active
  cases active

theorem strict_local_admission_deadline_requires_observable_fence
    {LocalObservation : Type} (admit : LocalObservation → Prop) {before after : LocalObservation}
    (unchanged : before = after) (useful : admit before) (hardDeadline : ¬ admit after) : False :=
  hardDeadline (unchanged ▸ useful)

#print axioms step_preserves_coverage_and_charges
#print axioms trace_preserves_coverage_and_charges
#print axioms arbitrary_trace_retains_complete_basis
#print axioms closing_entrance_leaves_its_charge
#print axioms closed_gate_cannot_reopen
#print axioms stopped_reader_cannot_resume
#print axioms restart_preserves_old_borrow_and_excludes_its_gate
#print axioms two_reads_share_one_registration
#print axioms standing_read_refines_the_captured_cut
#print axioms fresh_floor_excludes_new_invocations_after_terminal
#print axioms strict_local_admission_deadline_requires_observable_fence

end StandingCustody
