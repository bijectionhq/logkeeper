import ConfigurationClosure
import OrderedApplication
import ProviderIOClosure

set_option warningAsError true

namespace RecoveryCapacity

open ConfigurationClosure (Generation Certificate InstalledOnQuorum)
open OrderedApplication (Command Outcome)
open PrefixAgreement (Chosen Vote)

variable {Payload Voter Ticket : Type}

structure Budget where
  ordinary : Nat
  workspace : Nat
  envelope : Nat

structure Context (Payload Voter : Type) where
  source : Generation Voter (Command Payload)
  origin : Kernel.State Payload
  target : Kernel.Placement
  authorizedTarget : Generation Voter (Command Payload) → Prop
  limits : Kernel.Limits
  budget : Budget
  footprint : List (Command Payload) → Nat

structure Envelope (context : Context Payload Voter) : Prop where
  basis : context.footprint context.source.basis ≤ context.budget.envelope
  votes : ∀ voter ∈ context.source.ledger.members, ∀ vote, context.source.ledger.voted voter vote →
    context.footprint vote.history ≤ context.budget.envelope

inductive MeteredVoter (context : Context Payload Voter) (authorized : Nat → Prop) :
    ConfigurationClosure.VoterState (Command Payload) → Prop
  | initial : MeteredVoter context authorized ConfigurationClosure.initial
  | step {before after} (trace : MeteredVoter context authorized before)
      (transition : ConfigurationClosure.Step authorized before after)
      (fitsNew : ∀ vote, after.acceptor.votes vote → ¬ before.acceptor.votes vote →
        context.footprint vote.history ≤ context.budget.envelope) :
      MeteredVoter context authorized after

theorem vote_admission_preserves_the_envelope_and_scoped_trace
    {context : Context Payload Voter} {authorized : Nat → Prop}
    {state : ConfigurationClosure.VoterState (Command Payload)}
    (trace : MeteredVoter context authorized state) :
    ConfigurationClosure.Trace authorized ConfigurationClosure.initial state ∧
    ∀ vote, state.acceptor.votes vote → context.footprint vote.history ≤ context.budget.envelope := by
  have preserveBound {before after : ConfigurationClosure.VoterState (Command Payload)}
      (prior : ∀ vote, before.acceptor.votes vote → context.footprint vote.history ≤ context.budget.envelope)
      (fits : ∀ vote, after.acceptor.votes vote → ¬ before.acceptor.votes vote →
        context.footprint vote.history ≤ context.budget.envelope) :
      ∀ vote, after.acceptor.votes vote → context.footprint vote.history ≤ context.budget.envelope := by
    intro vote recorded
    classical
    by_cases older : before.acceptor.votes vote
    · exact prior vote older
    · exact fits vote recorded older
  induction trace with
  | initial => exact ⟨.same _, fun _ impossible => False.elim impossible⟩
  | step _ transition fits prior =>
      exact ⟨.next prior.1 transition, preserveBound prior.2 fits⟩

theorem metered_voters_and_exact_basis_establish_the_source_envelope
    (context : Context Payload Voter) (authorized : Nat → Prop)
    (replicas : Voter → ConfigurationClosure.VoterState (Command Payload))
    (reached : ∀ voter ∈ context.source.ledger.members, MeteredVoter context authorized (replicas voter))
    (boundVotes : ∀ voter ∈ context.source.ledger.members, ∀ vote, context.source.ledger.voted voter vote →
      (replicas voter).acceptor.votes vote)
    (basisFits : context.footprint context.source.basis ≤ context.budget.envelope) : Envelope context := by
  refine ⟨basisFits, ?_⟩
  intro voter member vote cast
  exact (vote_admission_preserves_the_envelope_and_scoped_trace (reached voter member)).2 vote
    (boundVotes voter member vote cast)

structure ValidSeal (context : Context Payload Voter) (certificate : Certificate Voter (Command Payload)) : Prop where
  ranked : ConfigurationClosure.Ranked context.source.ledger certificate
  covers : ConfigurationClosure.CoversEveryVote context.source.ledger certificate
  targetScope : certificate.successor = context.target.generation
  terminal : ∃ writer, (OrderedApplication.replay context.limits context.origin
    (ConfigurationClosure.Recovered context.source.basis certificate)).1.authority = .sealed context.target writer

theorem every_eligible_ranked_cut_fits_the_committed_envelope
    (context : Context Payload Voter) (envelope : Envelope context)
    (certificate : Certificate Voter (Command Payload)) (valid : ValidSeal context certificate) :
    context.footprint (ConfigurationClosure.Recovered context.source.basis certificate) ≤ context.budget.envelope := by
  cases winner : certificate.winner with
  | none => simpa [ConfigurationClosure.Recovered, ConfigurationClosure.EmptyRecovery, winner] using envelope.basis
  | some accepted =>
      obtain ⟨voter, member, _, _, voted⟩ := valid.ranked.authenticated accepted winner
      have fits : context.footprint accepted.history ≤ context.budget.envelope := by
        exact envelope.votes voter member accepted voted
      simpa [ConfigurationClosure.Recovered, winner] using fits

structure Cut (context : Context Payload Voter) where
  certificate : Certificate Voter (Command Payload)
  valid : ValidSeal context certificate
  fits : context.footprint (ConfigurationClosure.Recovered context.source.basis certificate) ≤ context.budget.envelope

def Cut.history {context : Context Payload Voter} (cut : Cut context) : List (Command Payload) :=
  ConfigurationClosure.Recovered context.source.basis cut.certificate

def Cut.bytes {context : Context Payload Voter} (cut : Cut context) : Nat :=
  context.footprint cut.history

def fromSeal (context : Context Payload Voter) (certificate : Certificate Voter (Command Payload))
    (valid : ValidSeal context certificate) (bounded : Envelope context) : Cut context :=
  ⟨certificate, valid, every_eligible_ranked_cut_fits_the_committed_envelope context bounded certificate valid⟩

structure Installation {context : Context Payload Voter} (cut : Cut context) where
  family : Generation Voter (Command Payload)
  target : context.authorizedTarget family
  installed : InstalledOnQuorum family
  exact : family.basis = cut.history

theorem installation_keeps_the_exact_recovered_history {context : Context Payload Voter}
    {cut : Cut context} (installation : Installation cut) : installation.family.basis = cut.history := by
  exact installation.exact

inductive Phase (context : Context Payload Voter) where
  | idle
  | reserved
  | sealed (cut : Cut context)
  | holding (cut : Cut context)
  | ready (cut : Cut context)
  | installed (cut : Cut context) (installation : Installation cut) (holdsOld : Bool)

structure State (context : Context Payload Voter) (Ticket : Type) where
  otherOrdinary : Nat
  phase : Phase context
  incumbent : ProviderIOClosure.State Ticket

variable {context : Context Payload Voter}

def finalCharge : Phase context → Nat
  | .idle => 0
  | .installed cut _ _ => cut.bytes
  | _ => context.budget.envelope

def workspaceCharge : Phase context → Nat
  | .holding cut => cut.bytes
  | .ready cut => 2 * cut.bytes
  | .installed cut _ true => cut.bytes
  | _ => 0

def HasReservation : Phase context → Prop
  | .idle => False
  | _ => True

def KeepsIncumbent : Phase context → Prop
  | .holding _ | .ready _ | .installed _ _ true => True
  | _ => False

def NeedsIncumbent : Phase context → Prop
  | .holding _ | .ready _ => True
  | _ => False

def CanReserve (state : State context Ticket) : Prop :=
  state.otherOrdinary + context.budget.envelope ≤ context.budget.ordinary ∧
    2 * context.budget.envelope ≤ context.budget.workspace

def CanReleaseOld (state : State context Ticket) : Prop :=
  state.incumbent.erased = true

def initial (context : Context Payload Voter) : State context Ticket :=
  ⟨0, .idle, ProviderIOClosure.initial⟩

inductive Step [DecidableEq Ticket] (reserveProvider : ProviderIOClosure.Custody Ticket → Prop) :
    State context Ticket → State context Ticket → Prop
  | ordinary {state} (amount : Nat)
      (room : amount + finalCharge state.phase ≤ context.budget.ordinary) :
      Step reserveProvider state {state with otherOrdinary := amount}
  | reserve {state} (idle : state.phase = .idle) (room : CanReserve state) :
      Step reserveProvider state {state with phase := .reserved}
  | sealCut {state} (ready : state.phase = .reserved) (certificate : Certificate Voter (Command Payload))
      (valid : ValidSeal context certificate) (bounded : Envelope context) :
      Step reserveProvider state {state with phase := .sealed (fromSeal context certificate valid bounded)}
  | stageFirst {state} (cut : Cut context) (selected : state.phase = .sealed cut)
      (room : cut.bytes ≤ context.budget.workspace) (medium : ProviderIOClosure.State Ticket)
      (verified : ProviderIOClosure.Sound medium) (present : medium.present = true) :
      Step reserveProvider state {state with phase := .holding cut, incumbent := medium}
  | stageReplacement {state} (cut : Cut context) (held : state.phase = .holding cut)
      (room : 2 * cut.bytes ≤ context.budget.workspace) :
      Step reserveProvider state {state with phase := .ready cut}
  | install {state} (cut : Cut context) (ready : state.phase = .ready cut) (installed : Installation cut) :
      Step reserveProvider state {state with phase := .installed cut installed true}
  | originalCustody {state next} (held : KeepsIncumbent state.phase)
      (effect : ProviderIOClosure.Step reserveProvider state.incumbent next)
      (retains : NeedsIncumbent state.phase → next.present = true) :
      Step reserveProvider state {state with incumbent := next}
  | releaseOld {state} (cut : Cut context) (installed : Installation cut)
      (held : state.phase = .installed cut installed true) (absent : CanReleaseOld state) :
      Step reserveProvider state {state with phase := .installed cut installed false}
  | restart {state} :
      Step reserveProvider state state

inductive Trace [DecidableEq Ticket] (reserveProvider : ProviderIOClosure.Custody Ticket → Prop) :
    State context Ticket → State context Ticket → Prop
  | same (state) : Trace reserveProvider state state
  | next {first before after} :
      Trace reserveProvider first before → Step reserveProvider before after → Trace reserveProvider first after

structure Sound (state : State context Ticket) : Prop where
  ordinary : state.otherOrdinary + finalCharge state.phase ≤ context.budget.ordinary
  workspace : HasReservation state.phase → 2 * context.budget.envelope ≤ context.budget.workspace
  custody : ProviderIOClosure.Sound state.incumbent
  acceptedMedia : NeedsIncumbent state.phase → state.incumbent.present = true

theorem initial_sound (context : Context Payload Voter) : Sound (initial context : State context Ticket) :=
  ⟨Nat.zero_le _, fun none => False.elim none, ProviderIOClosure.initial_sound, fun none => False.elim none⟩

variable [DecidableEq Ticket]

theorem every_transition_preserves_ordinary_space_and_exact_custody
    {reserveProvider : ProviderIOClosure.Custody Ticket → Prop} {before after : State context Ticket}
    (sound : Sound before) (step : Step reserveProvider before after) : Sound after := by
  cases step with
  | ordinary _ room => exact ⟨room, sound.workspace, sound.custody, sound.acceptedMedia⟩
  | reserve _ room => exact ⟨room.1, fun _ => room.2, sound.custody, fun none => False.elim none⟩
  | sealCut ready _ _ _ =>
      refine ⟨?_, fun _ => sound.workspace (by simp [ready, HasReservation]), sound.custody, fun none => False.elim none⟩
      simpa [ready, finalCharge] using sound.ordinary
  | stageFirst _ chosen _ _ verified present =>
      refine ⟨?_, fun _ => sound.workspace (by simp [chosen, HasReservation]), verified, fun _ => present⟩
      simpa [chosen, finalCharge] using sound.ordinary
  | stageReplacement _ held _ =>
      refine ⟨?_, fun _ => sound.workspace (by simp [held, HasReservation]), sound.custody,
        fun _ => sound.acceptedMedia (by simp [held, NeedsIncumbent])⟩
      simpa [held, finalCharge] using sound.ordinary
  | install cut ready _ =>
      refine ⟨?_, fun _ => sound.workspace (by simp [ready, HasReservation]), sound.custody, fun none => False.elim none⟩
      have reserved : before.otherOrdinary + context.budget.envelope ≤ context.budget.ordinary := by
        simpa [ready, finalCharge] using sound.ordinary
      exact Nat.le_trans (Nat.add_le_add_left cut.fits _) reserved
  | originalCustody _ effect retains =>
      exact ⟨sound.ordinary, sound.workspace, ProviderIOClosure.sound_step sound.custody effect, retains⟩
  | releaseOld _ _ held _ =>
      refine ⟨?_, fun _ => sound.workspace (by simp [held, HasReservation]), sound.custody, fun none => False.elim none⟩
      simpa [held, finalCharge] using sound.ordinary
  | restart => exact sound

theorem every_trace_preserves_the_reservation
    {reserveProvider : ProviderIOClosure.Custody Ticket → Prop} {first last : State context Ticket}
    (sound : Sound first) (trace : Trace reserveProvider first last) : Sound last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact every_transition_preserves_ordinary_space_and_exact_custody prior step

omit [DecidableEq Ticket] in
theorem every_durable_candidate_fits_reserved_workspace
    {state : State context Ticket} (sound : Sound state) :
    workspaceCharge state.phase ≤ context.budget.workspace := by
  cases phase : state.phase with
  | idle => simp [workspaceCharge]
  | reserved => simp [workspaceCharge]
  | sealed _ => simp [workspaceCharge]
  | holding cut =>
      have room := sound.workspace (by simp [phase, HasReservation])
      simpa [phase, workspaceCharge] using
        (show cut.bytes ≤ context.budget.workspace from by
          have bound : cut.bytes ≤ context.budget.envelope := cut.fits
          omega)
  | ready cut =>
      have room := sound.workspace (by simp [phase, HasReservation])
      have bound : cut.bytes ≤ context.budget.envelope := cut.fits
      simpa [phase, workspaceCharge] using (show 2 * cut.bytes ≤ context.budget.workspace from by omega)
  | installed cut _ kept =>
      cases kept
      · simp [workspaceCharge]
      · have room := sound.workspace (by simp [phase, HasReservation])
        have bound : cut.bytes ≤ context.budget.envelope := cut.fits
        simpa [phase, workspaceCharge] using (show cut.bytes ≤ context.budget.workspace from by omega)

omit [DecidableEq Ticket] in
theorem old_charge_can_leave_only_after_exact_stable_absence
    {state : State context Ticket} (sound : Sound state) (proof : CanReleaseOld state) :
    ProviderIOClosure.StableAbsence state.incumbent := by
  exact sound.custody.erasure proof

theorem a_sealed_move_can_install_without_new_ordinary_or_custody_capacity
    (reserveProvider : ProviderIOClosure.Custody Ticket → Prop) (state : State context Ticket)
    (cut : Cut context) (installation : Installation cut)
    (sealed : state.phase = .sealed cut) (sound : Sound state)
    (medium : ProviderIOClosure.State Ticket) (verified : ProviderIOClosure.Sound medium)
    (present : medium.present = true) :
    ∃ after, Trace reserveProvider state after ∧ after.phase = .installed cut installation true ∧
      Sound after ∧ workspaceCharge after.phase ≤ context.budget.workspace ∧
      after.otherOrdinary = state.otherOrdinary ∧ after.incumbent = medium := by
  have reserved := sound.workspace (by simp [sealed, HasReservation])
  have bound : cut.bytes ≤ context.budget.envelope := cut.fits
  have firstFits : cut.bytes ≤ context.budget.workspace := by omega
  have bothFit : 2 * cut.bytes ≤ context.budget.workspace := by omega
  let held := {state with phase := .holding cut, incumbent := medium}
  let ready := {held with phase := .ready cut}
  let installed := {ready with phase := .installed cut installation true}
  have trace : Trace reserveProvider state installed :=
    .next (.next (.next (.same state) (.stageFirst cut sealed firstFits medium verified present))
      (.stageReplacement cut rfl bothFit)) (.install cut rfl installation)
  have finalSound := every_trace_preserves_the_reservation sound trace
  exact ⟨installed, trace, rfl, finalSound, every_durable_candidate_fits_reserved_workspace finalSound, rfl, rfl⟩

omit [DecidableEq Ticket] in
theorem every_recovery_majority_reads_the_exact_charged_cut
    {cut : Cut context} (installation : Installation cut)
    (available : Voter → Bool)
    (recovery : JournalRefinement.Majority installation.family.ledger.members available) :
    context.authorizedTarget installation.family ∧
    ∃ voter ∈ installation.family.ledger.members, available voter = true ∧
      installation.family.installed voter cut.history := by
  obtain ⟨holders, majority, exactCopy⟩ := installation.installed
  obtain ⟨voter, member, online, held⟩ :=
    JournalRefinement.majorities_overlap installation.family.ledger.members available holders recovery majority
  have copy := exactCopy voter member held
  have exactHistory := installation_keeps_the_exact_recovered_history installation
  have authorized : context.authorizedTarget installation.family := by
    exact installation.target
  exact ⟨authorized, voter, member, online, exactHistory ▸ copy⟩

omit [DecidableEq Ticket] in
theorem a_charged_install_keeps_the_source_results_and_activates_the_exact_stream
    {ballot : Nat} {chosen : List (Command Payload)}
    (old : Chosen context.source.ledger ballot chosen) (cut : Cut context) (installation : Installation cut)
    (valid : Kernel.Valid context.limits context.origin) :
    (OrderedApplication.replay context.limits context.origin chosen).2 <+:
      (OrderedApplication.replay context.limits context.origin cut.history).2 ∧
    ∃ (writer : Kernel.Writer) (resumed : Kernel.State Payload), Kernel.Trace context.limits context.origin resumed ∧
      resumed.authority = .active {writer with placement := context.target} ∧
      resumed.history = (OrderedApplication.replay context.limits context.origin installation.family.basis).1.history ∧
      Kernel.Valid context.limits resumed := by
  have inherited : chosen <+: cut.history :=
    ConfigurationClosure.ranked_cut_covers_every_old_quorum_even_if_learned_late
      context.source.rules cut.valid.ranked cut.valid.covers context.source.basis old
  refine ⟨OrderedApplication.outcomes_extend_with_commands context.limits context.origin inherited, ?_⟩
  obtain ⟨writer, sourceClosed⟩ := cut.valid.terminal
  let replayed := (OrderedApplication.replay context.limits context.origin cut.history).1
  let resumed := {replayed with authority := .active {writer with placement := context.target}}
  have trace : Kernel.Trace context.limits context.origin resumed :=
    .next (OrderedApplication.replay_projects_to_kernel context.limits context.origin cut.history)
      (.activate replayed.history sourceClosed rfl)
  have exactCut : resumed.history =
      (OrderedApplication.replay context.limits context.origin installation.family.basis).1.history := by
    rw [installation_keeps_the_exact_recovered_history installation]
  exact ⟨writer, resumed, trace, rfl, exactCut, Kernel.every_trace_preserves_bounds valid trace⟩

theorem a_full_pool_recovers_prior_outcomes_with_exact_quorum_and_retained_physical_custody
    {reserveProvider : ProviderIOClosure.Custody Ticket → Prop} {state : State context Ticket}
    {cut : Cut context} (installation : Installation cut)
    (sealed : state.phase = .sealed cut) (sound : Sound state)
    (full : state.otherOrdinary + finalCharge state.phase = context.budget.ordinary)
    (oldMedium : ProviderIOClosure.State Ticket) (physical : ProviderIOClosure.Sound oldMedium)
    (present : oldMedium.present = true)
    {ballot : Nat} {chosen : List (Command Payload)} (old : Chosen context.source.ledger ballot chosen)
    (valid : Kernel.Valid context.limits context.origin)
    (available : Voter → Bool)
    (recovery : JournalRefinement.Majority installation.family.ledger.members available) :
    ∃ after, Trace reserveProvider state after ∧ after.phase = .installed cut installation true ∧ Sound after ∧
      after.otherOrdinary + context.budget.envelope = context.budget.ordinary ∧
      workspaceCharge after.phase ≤ context.budget.workspace ∧ after.incumbent.present = true ∧
      (OrderedApplication.replay context.limits context.origin chosen).2 <+:
        (OrderedApplication.replay context.limits context.origin cut.history).2 ∧
      (∃ voter ∈ installation.family.ledger.members, available voter = true ∧
        installation.family.installed voter cut.history) ∧
      (∃ resumed, Kernel.Trace context.limits context.origin resumed ∧ Kernel.Valid context.limits resumed) := by
  obtain ⟨after, operational, installed, finalSound, workspaceKept, sameOrdinary, oldKept⟩ :=
    a_sealed_move_can_install_without_new_ordinary_or_custody_capacity
      reserveProvider state cut installation sealed sound oldMedium physical present
  obtain ⟨outcomes, _, resumed, trace, _, _, safe⟩ :=
    a_charged_install_keeps_the_source_results_and_activates_the_exact_stream old cut installation valid
  have retainedFull : after.otherOrdinary + context.budget.envelope = context.budget.ordinary := by
    rw [sameOrdinary]
    simpa [sealed, finalCharge] using full
  exact ⟨after, operational, installed, finalSound, retainedFull, workspaceKept,
    oldKept.symm ▸ present, outcomes, (every_recovery_majority_reads_the_exact_charged_cut installation available recovery).2,
    resumed, trace, safe⟩

omit [DecidableEq Ticket] in
theorem one_image_cannot_fund_two_disjoint_maximal_images {bytes workspace : Nat}
    (positive : 0 < bytes) (onlyOne : workspace = bytes) :
    ¬ 2 * bytes ≤ workspace := by
  omega

#print axioms vote_admission_preserves_the_envelope_and_scoped_trace
#print axioms metered_voters_and_exact_basis_establish_the_source_envelope
#print axioms every_eligible_ranked_cut_fits_the_committed_envelope
#print axioms installation_keeps_the_exact_recovered_history
#print axioms initial_sound
#print axioms every_transition_preserves_ordinary_space_and_exact_custody
#print axioms every_trace_preserves_the_reservation
#print axioms every_durable_candidate_fits_reserved_workspace
#print axioms old_charge_can_leave_only_after_exact_stable_absence
#print axioms a_sealed_move_can_install_without_new_ordinary_or_custody_capacity
#print axioms every_recovery_majority_reads_the_exact_charged_cut
#print axioms a_charged_install_keeps_the_source_results_and_activates_the_exact_stream
#print axioms a_full_pool_recovers_prior_outcomes_with_exact_quorum_and_retained_physical_custody
#print axioms one_image_cannot_fund_two_disjoint_maximal_images

end RecoveryCapacity
