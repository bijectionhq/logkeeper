import JointProtection
import MoveRecovery

set_option warningAsError true

namespace FullAdmission

open JournalRefinement (Majority)

variable {slots width : Nat} {Payload Ticket Voter Zone Claim : Type}

inductive Mode (Zone : Type) where
  | healthy
  | degraded (failed : Zone)

def Allowed : Mode Zone → Option Zone → Prop
  | .healthy, _ => True
  | .degraded actual, scenario => scenario = some actual

def currentFault : Mode Zone → Option Zone
  | .healthy => none
  | .degraded actual => some actual

def surviving [DecidableEq Zone] (reachable : Voter → Bool) (zoneOf : Voter → Zone)
    (scenario : Option Zone) (voter : Voter) : Bool :=
  reachable voter && decide (scenario ≠ some (zoneOf voter))

abbrev Frame (slots : Nat) (Payload Ticket : Type) := ChosenReplay.Frame slots Payload Ticket
abbrev SourceView (width slots : Nat) (Payload Ticket : Type) :=
  JointProtection.View width FundedAppend.Book (FundedAppend.Source slots Payload) (Frame slots Payload Ticket)

structure Current (width slots : Nat) (Payload Ticket Voter Zone Claim : Type) where
  state : FundedWindowMove.State slots Payload Ticket
  moves : FundedWindowMove.Rules slots Payload Ticket
  sourceEvidence : MoveRecovery.Evidence slots Payload Ticket
  initial : ChosenReplay.Image slots Payload
  lineage : ChosenReplay.Lineage
  generation : ConfigurationClosure.Generation Voter (Frame slots Payload Ticket)
  membershipRevision : Nat
  custodyRevision : Nat
  online : Voter → Bool
  voterZone : Voter → Zone
  poolZone : Nat → Zone
  mode : Mode Zone
  selectors : JointCheckpoint.Protection (JointProtection.Input width) Claim
  recoveryRules : JointProtection.Rules width FundedAppend.Book (FundedAppend.Source slots Payload)
    (Frame slots Payload Ticket)
  plan : JournalRotation.View → SourceView width slots Payload Ticket
  root : JournalRotation.View → Nat
  contains : Nat → JointProtection.Input width → Prop

structure Stamp (slots : Nat) (Payload Ticket Zone : Type) where
  lineage : ChosenReplay.Lineage
  membership : Nat
  custody : Nat
  mode : Mode Zone
  stable : JournalRotation.View
  visible : JournalRotation.View
  history : List (Frame slots Payload Ticket)
  window : Nat

def stamp (current : Current width slots Payload Ticket Voter Zone Claim) (version : Nat) :
    Stamp slots Payload Ticket Zone :=
  ⟨current.lineage, current.membershipRevision, current.custodyRevision, current.mode,
    current.selectors.stable, current.selectors.visible, current.generation.basis, version⟩

def ScopeMatches (observed expected : Stamp slots Payload Ticket Zone) : Prop :=
  observed = expected

abbrev PoolState (current : Current width slots Payload Ticket Voter Zone Claim) :=
  current.state.appends.regional.pools

def SourceAtCut (current : Current width slots Payload Ticket Voter Zone Claim) : Prop :=
  ∃ image outcomes, ChosenReplay.replay (MoveRecovery.sourceRules current.moves current.sourceEvidence)
      current.lineage current.initial current.generation.basis = some (image, outcomes) ∧
    image.source = current.state.appends.regional.streams current.lineage.stream ∧
    image.book.latest current.lineage.stream = current.state.appends.book.latest current.lineage.stream ∧
    ∀ version, current.moves.append.owner version = current.lineage.stream →
      image.book.windows version = current.state.appends.book.windows version

def HoldsInput (current : Current width slots Payload Ticket Voter Zone Claim)
    (scenario : Option Zone) (view : JournalRotation.View) (object : JointProtection.Input width)
    (version : Nat) : Prop :=
  let ledger := (PoolState current).ledger
  let pool := (FundedWindowMove.layout current.moves).pool version
  current.contains version object ∧
    ledger.catalog.roots (current.root view) = .live ∧
    current.moves.append.regional.needs (current.root view) version ∧
    PoolIncarnations.Eligible (PoolState current) pool ∧ scenario ≠ some (current.poolZone pool)

variable [DecidableEq Zone]

structure Coverage (current : Current width slots Payload Ticket Voter Zone Claim) (scenario : Option Zone) : Prop where
  quorum : Majority current.generation.ledger.members (surviving current.online current.voterZone scenario)
  inputs : ∀ view, JointCheckpoint.Selectable current.selectors view →
    ∀ object, JointProtection.Required current.recoveryRules.attachment (current.plan view) object →
      ∃ version, HoldsInput current scenario view object version

def Complete (current : Current width slots Payload Ticket Voter Zone Claim) (mode : Mode Zone) : Prop :=
  ∀ scenario, Allowed mode scenario → Coverage current scenario

structure Ready (current : Current width slots Payload Ticket Voter Zone Claim) (version : Nat) : Prop where
  sound : FundedWindowMove.Sound current.moves current.state
  applied : SourceAtCut current
  window : MoveRecovery.PhysicalWindow current.moves current.state current.lineage.stream version
  windowReachable : currentFault current.mode ≠ some (current.poolZone ((FundedWindowMove.layout current.moves).pool version))
  distinct : current.generation.ledger.members.Nodup
  installed : ConfigurationClosure.InstalledOnQuorum current.generation
  views : ∀ view, JointCheckpoint.Selectable current.selectors view →
    JointProtection.Bound current.recoveryRules (current.plan view) view current.generation.basis
  support : Complete current current.mode

def CanAdmit (current : Current width slots Payload Ticket Voter Zone Claim) (version : Nat)
    (observed : Stamp slots Payload Ticket Zone) : Prop :=
  ScopeMatches observed (stamp current version) ∧ Ready current version

noncomputable def admit (current : Current width slots Payload Ticket Voter Zone Claim) (version : Nat)
    (observed : Stamp slots Payload Ticket Zone) : Option (Stamp slots Payload Ticket Zone) := by
  classical
  exact if CanAdmit current version observed then some observed else none

theorem fresh_admission_uses_the_current_certified_scope
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    {observed : Stamp slots Payload Ticket Zone} (approved : CanAdmit current version observed) :
    observed = stamp current version := by
  exact approved.1

theorem a_successful_admission_certifies_window_and_complete_current_scope
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    {observed accepted : Stamp slots Payload Ticket Zone}
    (admitted : admit current version observed = some accepted) :
    accepted = stamp current version ∧ Ready current version := by
  unfold admit at admitted
  split at admitted
  · rename_i passes
    cases admitted
    exact ⟨fresh_admission_uses_the_current_certified_scope passes, passes.2⟩
  · cases admitted

theorem one_admission_covers_every_selectable_input_under_the_same_failure
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    {observed accepted : Stamp slots Payload Ticket Zone}
    (admitted : admit current version observed = some accepted)
    (scenario : Option Zone) (allowed : Allowed current.mode scenario) (view : JournalRotation.View)
    (selectable : JointCheckpoint.Selectable current.selectors view) :
    JointProtection.Bound current.recoveryRules (current.plan view) view current.generation.basis ∧
    Majority current.generation.ledger.members (surviving current.online current.voterZone scenario) ∧
    (∀ responders, Majority current.generation.ledger.members responders →
      (∀ voter ∈ current.generation.ledger.members, responders voter = true →
        surviving current.online current.voterZone scenario voter = true) →
      ∃ voter ∈ current.generation.ledger.members,
        responders voter = true ∧ surviving current.online current.voterZone scenario voter = true ∧
          current.generation.installed voter current.generation.basis) ∧
    (∀ object, JointProtection.Required current.recoveryRules.attachment (current.plan view) object →
      ∃ allocation, HoldsInput current scenario view object allocation ∧
        ((PoolState current).ledger.provider allocation).present = true ∧
        allocation ∈ (PoolState current).ledger.debits) := by
  have ready := (a_successful_admission_certifies_window_and_complete_current_scope admitted).2
  have available := ready.support scenario allowed
  refine ⟨ready.views view selectable, available.quorum, ?_, ?_⟩
  · intro responders voting live
    obtain ⟨installed, quorum, exactBasis⟩ := ready.installed
    obtain ⟨voter, member, responded, holds⟩ :=
      JournalRefinement.majorities_overlap current.generation.ledger.members responders installed voting quorum
    exact ⟨voter, member, responded, live voter member responded, exactBasis voter member holds⟩
  · intro object required
    obtain ⟨allocation, held⟩ := available.inputs view selectable object required
    have paid := SharedExtentAccounting.a_live_checkpoint_or_evidence_root_has_charged_provider_bytes
      ready.sound.regional.pools.funded held.2.1 held.2.2.1
    exact ⟨allocation, held, paid⟩

theorem an_original_activation_attachment_is_required_for_fresh_service
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    {observed accepted : Stamp slots Payload Ticket Zone}
    (admitted : admit current version observed = some accepted)
    (scenario : Option Zone) (allowed : Allowed current.mode scenario) (view : JournalRotation.View)
    (selectable : JointCheckpoint.Selectable current.selectors view)
    {command : Frame slots Payload Ticket} (member : command ∈ (current.plan view).tail)
    {object : JointProtection.Input width} (needed : current.recoveryRules.attachment command object) :
    ∃ allocation, HoldsInput current scenario view object allocation ∧
      ((PoolState current).ledger.provider allocation).present = true ∧
      allocation ∈ (PoolState current).ledger.debits := by
  have ready := one_admission_covers_every_selectable_input_under_the_same_failure
    admitted scenario allowed view selectable
  exact ready.2.2.2 object (.tailInput command member needed)

theorem a_stale_observation_cannot_admit
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    {observed : Stamp slots Payload Ticket Zone} (stale : observed ≠ stamp current version) :
    admit current version observed = none := by
  have unsupported : ¬ CanAdmit current version observed :=
    fun approved => stale (fresh_admission_uses_the_current_certified_scope approved)
  simp [admit, unsupported]

theorem a_window_in_the_existing_failed_zone_cannot_admit
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    {observed : Stamp slots Payload Ticket Zone}
    (lost : currentFault current.mode = some (current.poolZone ((FundedWindowMove.layout current.moves).pool version))) :
    admit current version observed = none := by
  have denied : ¬ CanAdmit current version observed := fun approved => approved.2.windowReachable lost
  simp [admit, denied]

noncomputable def beginAppend
    (current : Current width slots Payload Ticket Voter Zone Claim) (observed : Stamp slots Payload Ticket Zone)
    (frame : Frame slots Payload Ticket) : Option (FundedAppend.Request Payload Ticket) := by
  classical
  exact match frame.command with
  | .append request =>
      if ChosenReplay.eligibleFrame current.lineage (MoveRecovery.sourceImage current.state current.lineage.stream) frame
      then (admit current request.version observed).map (fun _ => request)
      else none
  | _ => none

theorem an_admitted_append_proposal_uses_the_recovered_scope_and_window
    {current : Current width slots Payload Ticket Voter Zone Claim}
    {observed : Stamp slots Payload Ticket Zone} {frame : Frame slots Payload Ticket}
    {request : FundedAppend.Request Payload Ticket}
    (started : beginAppend current observed frame = some request) :
    frame.command = .append request ∧
      ChosenReplay.eligibleFrame current.lineage (MoveRecovery.sourceImage current.state current.lineage.stream) frame ∧
      CanAdmit current request.version observed := by
  generalize onFrame : frame.command = command at started
  cases command with
  | append exactRequest =>
      simp only [beginAppend, onFrame] at started
      split at started
      · rename_i matchesScope
        cases checked : admit current exactRequest.version observed with
        | none => simp [checked] at started
        | some authorized =>
            simp [checked] at started
            subst request
            have ready := a_successful_admission_certifies_window_and_complete_current_scope checked
            have identifies : authorized = observed := by
              unfold admit at checked
              split at checked <;> cases checked
              rfl
            have same := identifies.symm.trans ready.1
            exact ⟨rfl, matchesScope, by rw [same]; simp [ScopeMatches], ready.2⟩
      · cases started
  | _ => simp [beginAppend, onFrame] at started

theorem a_degraded_scope_checks_its_existing_failure_once
    {current : Current width slots Payload Ticket Voter Zone Claim} (failed : Zone)
    (available : Coverage current (some failed)) : Complete current (.degraded failed) := by
  intro scenario allowed
  change scenario = some failed at allowed
  exact allowed.symm ▸ available

theorem a_ready_degraded_scope_admits_without_refreshing_the_fault_allowance
    {current : Current width slots Payload Ticket Voter Zone Claim} {version : Nat}
    (ready : Ready current version) :
    admit current version (stamp current version) = some (stamp current version) := by
  have passes : CanAdmit current version (stamp current version) := ⟨by simp [ScopeMatches], ready⟩
  simp [admit, passes]

noncomputable def renewHealthy (current : Current width slots Payload Ticket Voter Zone Claim) :
    Option (Current width slots Payload Ticket Voter Zone Claim) := by
  classical
  exact if Complete current .healthy then some {current with mode := .healthy} else none

theorem a_healthy_renewal_requires_every_single_failure_case
    {current next : Current width slots Payload Ticket Voter Zone Claim}
    (renewed : renewHealthy current = some next) :
    next.mode = .healthy ∧ ∀ failed, Coverage next (some failed) := by
  unfold renewHealthy at renewed
  split at renewed
  · rename_i restored
    cases renewed
    refine ⟨rfl, ?_⟩
    intro failed
    have covered := restored (some failed) trivial
    exact ⟨covered.quorum, covered.inputs⟩
  · cases renewed

omit [DecidableEq Zone] in
theorem losing_one_of_three_voters_can_preserve_a_majority_but_requiring_another_loss_cannot :
    let voters : List Nat := [0, 1, 2]
    let live : Nat → Bool := fun voter => voter != 0
    Majority voters (surviving live id (some 0)) ∧
      ¬ Majority voters (surviving live id (some 1)) := by
  constructor <;> unfold Majority <;> decide

#print axioms fresh_admission_uses_the_current_certified_scope
#print axioms a_successful_admission_certifies_window_and_complete_current_scope
#print axioms one_admission_covers_every_selectable_input_under_the_same_failure
#print axioms an_original_activation_attachment_is_required_for_fresh_service
#print axioms a_stale_observation_cannot_admit
#print axioms a_window_in_the_existing_failed_zone_cannot_admit
#print axioms an_admitted_append_proposal_uses_the_recovered_scope_and_window
#print axioms a_degraded_scope_checks_its_existing_failure_once
#print axioms a_ready_degraded_scope_admits_without_refreshing_the_fault_allowance
#print axioms a_healthy_renewal_requires_every_single_failure_case
#print axioms losing_one_of_three_voters_can_preserve_a_majority_but_requiring_another_loss_cannot

end FullAdmission
