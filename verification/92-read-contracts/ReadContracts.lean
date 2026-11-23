import StandingCustody
import RetainedDelivery

set_option warningAsError true

namespace ReadContracts

open StandingCustody (Basis Phase State Status Window)
open DeliveryBook (Book Entry atKey)

variable {Reader Scope Extent Payload Signature Observation Reply : Type}
variable {capacity limit : Nat}

structure Probe (Reader Scope : Type) where
  invocation : Reader
  scope : Scope
  orderedFloor : Nat

structure Applied (Scope Extent : Type) where
  scope : Scope
  orderedPosition : Nat
  live : Bool
  basis : Basis Extent

structure FreshGate (verified : Probe Reader Scope → Prop) (id : Reader) (installed : Scope)
    (probe : Probe Reader Scope) (view : Applied Scope Extent)
    (window : Window Extent) (state : State Reader Extent) : Prop where
  authentic : verified probe
  invocation : probe.invocation = id
  probeScope : probe.scope = installed
  viewScope : view.scope = installed
  applied : probe.orderedFloor ≤ view.orderedPosition
  live : view.live = true
  basis : window.basis = view.basis
  openGate : state.phase = .open
  session : state.currentSession = window.session
  fresh : state.status id = .fresh

theorem the_gate_checks_the_current_process_session
    (verified : Probe Reader Scope → Prop) (id : Reader) (installed : Scope)
    (probe : Probe Reader Scope) (view : Applied Scope Extent) (window : Window Extent)
    (state : State Reader Extent) (admitted : FreshGate verified id installed probe view window state) :
    state.currentSession = window.session := by
  exact admitted.session

noncomputable def admitFresh [DecidableEq Reader] (verified : Probe Reader Scope → Prop)
    (id : Reader) (installed : Scope) (probe : Probe Reader Scope) (view : Applied Scope Extent)
    (window : Window Extent) (state : State Reader Extent) : Option (State Reader Extent) := by
  classical
  exact if FreshGate verified id installed probe view window state then
    some {state with status := StandingCustody.put state.status id .using}
  else none

theorem fresh_observation_admission_is_one_exact_standing_gate_transition [DecidableEq Reader]
    (verified : Probe Reader Scope → Prop) (installed : Scope) (id : Reader) (probe : Probe Reader Scope)
    (view : Applied Scope Extent) (window : Window Extent) (before after : State Reader Extent)
    (stop : State Reader Extent → Prop)
    (admitted : admitFresh verified id installed probe view window before = some after) :
    FreshGate verified id installed probe view window before ∧
      StandingCustody.Step window stop before after ∧ after.status id = .using := by
  unfold admitFresh at admitted
  split at admitted
  · next guard =>
      cases admitted
      have sameSession := the_gate_checks_the_current_process_session verified id installed probe view window before guard
      exact ⟨guard, .admit id guard.openGate sameSession guard.fresh, by simp [StandingCustody.put]⟩
  · contradiction

theorem an_exact_fresh_probe_and_live_standing_window_can_admit [DecidableEq Reader]
    (verified : Probe Reader Scope → Prop) (installed : Scope) (id : Reader) (probe : Probe Reader Scope)
    (view : Applied Scope Extent) (window : Window Extent) (before : State Reader Extent)
    (ready : FreshGate verified id installed probe view window before) :
    admitFresh verified id installed probe view window before =
      some {before with status := StandingCustody.put before.status id .using} := by
  simp only [admitFresh, ite_eq_left ready]

theorem a_late_process_or_foreign_scope_cannot_admit_fresh_work [DecidableEq Reader]
    (verified : Probe Reader Scope → Prop) (installed : Scope) (id : Reader) (probe : Probe Reader Scope)
    (view : Applied Scope Extent) (window : Window Extent) (before : State Reader Extent)
    (stale : before.currentSession ≠ window.session ∨ probe.scope ≠ installed) :
    admitFresh verified id installed probe view window before = none := by
  have refused : ¬ FreshGate verified id installed probe view window before := by
    intro ready
    rcases stale with process | scope
    · exact process (the_gate_checks_the_current_process_session verified id installed probe view window before ready)
    · exact scope ready.probeScope
  simp only [admitFresh, ite_eq_right refused]

noncomputable def finishFresh (id : Reader) (window : Window Extent) (state : State Reader Extent) :
    Option (Basis Extent) := by
  classical
  exact if state.status id = .using then some window.basis else none

theorem a_fresh_observation_keeps_its_exact_basis_through_authorizer_loss [DecidableEq Reader]
    (verified : Probe Reader Scope → Prop) (installed : Scope) (id : Reader) (probe : Probe Reader Scope)
    (view : Applied Scope Extent) (window : Window Extent) (before after final : State Reader Extent)
    {stop : State Reader Extent → Prop}
    (sound : StandingCustody.Sound window before)
    (admitted : admitFresh verified id installed probe view window before = some after)
    (later : StandingCustody.Trace window stop after final)
    (held : final.status id = .using) :
    finishFresh id window final = some view.basis ∧
      ∀ extent, view.basis.Needs extent → final.resident extent := by
  obtain ⟨guard, step, _⟩ := fresh_observation_admission_is_one_exact_standing_gate_transition
    verified installed id probe view window before after stop admitted
  have exactBasis := guard.basis
  have coverage := StandingCustody.arbitrary_trace_retains_complete_basis
    (StandingCustody.step_preserves_coverage_and_charges sound step) later id held
  exact ⟨by simp [finishFresh, held, exactBasis], fun extent needed => coverage extent (exactBasis.symm ▸ needed)⟩

theorem a_certified_latest_read_admitted_at_the_gate_has_a_linearization_witness
    {Replica : Type} {limits : Kernel.Limits} {origin : Kernel.State Payload} {writer : Kernel.Writer}
    {trace : ReadIndexProof.ChoiceTrace (OrderedApplication.Command Payload)}
    {call : ReadIndexProof.Invocation} {round : ReadIndexProof.Round Replica (OrderedApplication.Command Payload)}
    {instant : Nat} {snapshot : List (OrderedApplication.Command Payload)} {view : SnapshotAdmission.View}
    {window : Window Extent} {resolve : SnapshotAdmission.Basis → Basis Extent}
    {before after : State Nat Extent} {stop : State Nat Extent → Prop}
    (floor : ReconfiguredReads.VerifiedFloor trace call round)
    (unit : ReadIndexProof.UnitChoices trace)
    (certified : ReconfiguredReads.Reservation trace call round round.scope limits origin writer instant snapshot view)
    (sound : StandingCustody.Sound window before)
    (admitted : admitFresh (fun probe => probe = ⟨round.invocation, round.scope, round.target.length⟩)
      call.nonce round.scope ⟨round.invocation, round.scope, round.target.length⟩
      ⟨round.scope, snapshot.length, true, resolve (SnapshotAdmission.currentBasis view)⟩ window before = some after) :
    ∃ point, call.started ≤ point ∧ point ≤ instant ∧ instant ≤ call.replied ∧
      trace.chosen point = snapshot ∧
      Kernel.barrier (OrderedApplication.replay limits origin (trace.chosen point)).1 writer =
        some (SnapshotAdmission.currentBasis view).stop ∧
      ∀ extent, (resolve (SnapshotAdmission.currentBasis view)).Needs extent → after.resident extent := by
  obtain ⟨guard, borrowed, usingBasis⟩ := fresh_observation_admission_is_one_exact_standing_gate_transition
    (fun probe => probe = ⟨round.invocation, round.scope, round.target.length⟩)
    round.scope call.nonce ⟨round.invocation, round.scope, round.target.length⟩
    ⟨round.scope, snapshot.length, true, resolve (SnapshotAdmission.currentBasis view)⟩ window before after stop admitted
  obtain ⟨point, started, reserved, replied, _, chosen, cut, present⟩ :=
    StandingCustody.standing_read_refines_the_captured_cut floor unit certified guard.basis sound
      (StandingCustody.Trace.next (.same before) borrowed) call.nonce usingBasis
  exact ⟨point, started, reserved, replied, chosen, cut, present⟩

theorem effective_stop_excludes_later_fresh_result_delivery [DecidableEq Reader]
    (id : Reader) (window : Window Extent) (before after : State Reader Extent)
    {stop : State Reader Extent → Prop}
    (stopped : before.status id = .stopped) (later : StandingCustody.Trace window stop before after) :
    finishFresh id window after = none := by
  have exhausted := StandingCustody.stopped_reader_cannot_resume id stopped later
  simp [finishFresh, exhausted]

theorem same_recovered_observation_cannot_supply_two_distinct_original_answers
    (resume : Observation → Option Reply) (left right : Observation) (same : left = right)
    (originalLeft originalRight : Reply) (distinct : originalLeft ≠ originalRight) :
    ¬ (resume left = some originalLeft ∧ resume right = some originalRight) := by
  rintro ⟨first, other⟩
  subst right
  exact distinct (Option.some.inj (first.symm.trans other))

noncomputable def recoverExact (width : Nat) (book : Book limit capacity) (key : SourceOutcomes.Key limit)
    (invocation : RTDBFailover.Invocation) (authenticated : RTDBFailover.Invocation → Prop)
    (held : SourceOutcomes.Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature) :
    Option (AppliedBarrierReceipt.Packet Signature) :=
  RetainedDelivery.finish width book key invocation authenticated held sign

theorem missing_exact_receipt_has_no_fallback_to_a_fresh_answer
    (width : Nat) (book : Book limit capacity) (key : SourceOutcomes.Key limit)
    (invocation : RTDBFailover.Invocation) (authenticated : RTDBFailover.Invocation → Prop)
    (held : SourceOutcomes.Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature) (absent : atKey book key = none) :
    recoverExact width book key invocation authenticated held sign = none := by
  simp [recoverExact, RetainedDelivery.finish, absent]

theorem an_exact_retained_answer_survives_authority_loss_without_resampling
    (width : Nat) (book : Book limit capacity) (key : SourceOutcomes.Key limit) (original : Entry capacity)
    (authenticated : RTDBFailover.Invocation → Prop)
    (held : SourceOutcomes.Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature)
    (retained : atKey book key = some original) (caller : authenticated original.reply.invocation)
    (physical : held key original.borrow original.request) :
    let exactBytes := AppliedBarrierReceipt.encode width original.reply
    recoverExact width book key original.reply.invocation authenticated held sign =
      some ⟨exactBytes, sign (AppliedBarrierReceipt.sourceOf original.reply.invocation) exactBytes⟩ :=
  RetainedDelivery.a_retained_result_completes_from_the_original_live_borrow_without_the_old_frame
    width book key original authenticated held sign retained caller physical

#print axioms the_gate_checks_the_current_process_session
#print axioms fresh_observation_admission_is_one_exact_standing_gate_transition
#print axioms an_exact_fresh_probe_and_live_standing_window_can_admit
#print axioms a_late_process_or_foreign_scope_cannot_admit_fresh_work
#print axioms a_fresh_observation_keeps_its_exact_basis_through_authorizer_loss
#print axioms a_certified_latest_read_admitted_at_the_gate_has_a_linearization_witness
#print axioms effective_stop_excludes_later_fresh_result_delivery
#print axioms same_recovered_observation_cannot_supply_two_distinct_original_answers
#print axioms missing_exact_receipt_has_no_fallback_to_a_fresh_answer
#print axioms an_exact_retained_answer_survives_authority_loss_without_resampling

end ReadContracts
