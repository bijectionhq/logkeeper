import EnvelopeRecovery
import PoolEvacuation

set_option warningAsError true

namespace JointProtection

open EnvelopeCodec
open JournalRefinement (Majority)
open ConfigurationClosure (Generation InstalledOnQuorum)

variable {width : Nat} {Control Data Command Voter Pool Zone Ticket Claim : Type}

inductive Input (width : Nat) where
  | envelope (name : Field width)
  | control (name : Field width)
  | data (name : Field width)
  | evidenceManifest (name : Field width)
  | dependency (name : Field width)

structure View (width : Nat) (Control Data Command : Type) where
  envelopeName : Field width
  wire : Bytes
  header : Envelope width
  contents : EnvelopeRecovery.Contents width Control Data
  base : List Command
  tail : List Command

structure Rules (width : Nat) (Control Data Command : Type) where
  catalog : EnvelopeRecovery.Catalog width Control Data
  authenticated : Bytes → Prop
  envelopeAt : Field width → Option Bytes
  selectorName : JournalRotation.View → Field width
  anchor : List Command → EnvelopeRecovery.Anchor width
  necessary : EnvelopeRecovery.Contents width Control Data → Field width → Prop
  attachment : Command → Input width → Prop

structure Bound (rules : Rules width Control Data Command) (view : View width Control Data Command)
    (selector : JournalRotation.View) (basis : List Command) : Prop where
  selectorIdentity : rules.selectorName selector = view.envelopeName
  envelopeIdentity : rules.envelopeAt view.envelopeName = some view.wire
  checkpointPosition : view.base.length = selector.cut
  opened : EnvelopeRecovery.Opened rules.catalog rules.authenticated (rules.anchor view.base)
    (rules.necessary view.contents) view.wire view.header view.contents
  exactPrefix : view.base ++ view.tail = basis

inductive Required (attachment : Command → Input width → Prop) (view : View width Control Data Command) :
    Input width → Prop
  | envelope : Required attachment view (.envelope view.envelopeName)
  | control : Required attachment view (.control view.header.control)
  | data : Required attachment view (.data view.header.data)
  | manifest : Required attachment view (.evidenceManifest view.header.evidence)
  | dependency {object} (listed : object ∈ view.contents.dependencies) :
      Required attachment view (.dependency object)
  | tailInput {object} (command : Command) (inTail : command ∈ view.tail)
      (needed : attachment command object) : Required attachment view object

structure Scope (Command : Type) where
  revision : Nat
  history : List Command

def currentScope (revision : Nat) (generation : Generation Voter Command) : Scope Command :=
  ⟨revision, generation.basis⟩

def CanCertify (observed current : Scope Command) (ready : Prop) : Prop :=
  observed = current ∧ ready

theorem accepted_certificate_uses_current_scope {observed current : Scope Command} {ready : Prop}
    (accepted : CanCertify observed current ready) : observed = current := by
  exact accepted.1

def withInput (state : PoolEvacuation.State Pool Ticket) (contains : Nat → Input width → Prop)
    (object : Input width) : PoolEvacuation.State Pool Ticket :=
  {state with placed := fun version => state.placed version ∧ contains version object}

def Readable (layout : SharedExtentAccounting.Layout Pool) (poolZone : Pool → Zone)
    (state : PoolEvacuation.State Pool Ticket) (contains : Nat → Input width → Prop)
    (failed : Zone) (object : Input width) : Prop :=
  ∃ version, state.placed version ∧ contains version object ∧
    state.reachable (layout.pool version) ∧ poolZone (layout.pool version) ≠ failed ∧
    (state.accounting.provider version).present = true ∧ version ∈ state.accounting.debits

def survivingVoters [DecidableEq Zone] (online : Voter → Bool)
    (voterZone : Voter → Zone) (failed : Zone) (voter : Voter) : Bool :=
  online voter && decide (voterZone voter ≠ failed)

structure Ready [DecidableEq Pool] [DecidableEq Zone]
    (rules : Rules width Control Data Command) (generation : Generation Voter Command)
    (online : Voter → Bool) (voterZone : Voter → Zone)
    (layout : SharedExtentAccounting.Layout Pool) (poolZone : Pool → Zone)
    (needs : SharedCustody.Dependencies) (state : PoolEvacuation.State Pool Ticket)
    (contains : Nat → Input width → Prop) (selectors : JointCheckpoint.Protection (Input width) Claim)
    (plan : JournalRotation.View → View width Control Data Command) : Prop where
  distinctVoters : generation.ledger.members.Nodup
  installed : InstalledOnQuorum generation
  afterLoss : ∀ fault, Majority generation.ledger.members (survivingVoters online voterZone fault)
  viewBinding : ∀ choice, JointCheckpoint.Selectable selectors choice →
    Bound rules (plan choice) choice generation.basis
  accounting : SharedExtentAccounting.Sound layout needs state.accounting
  registered : ∀ version, state.placed version → state.accounting.catalog.physical version = true
  coverage : ∀ choice, JointCheckpoint.Selectable selectors choice →
    ∀ object, Required rules.attachment (plan choice) object →
      PoolEvacuation.Protected layout poolZone (withInput state contains object)

variable [DecidableEq Pool] [DecidableEq Zone]
variable {rules : Rules width Control Data Command} {generation : Generation Voter Command}
variable {online : Voter → Bool} {voterZone : Voter → Zone}
variable {layout : SharedExtentAccounting.Layout Pool} {poolZone : Pool → Zone}
variable {needs : SharedCustody.Dependencies} {state : PoolEvacuation.State Pool Ticket}
variable {contains : Nat → Input width → Prop} {selectors : JointCheckpoint.Protection (Input width) Claim}
variable {plan : JournalRotation.View → View width Control Data Command}

private theorem exact_object_survives
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    {choice : JournalRotation.View} (selected : JointCheckpoint.Selectable selectors choice)
    (failed : Zone) {object : Input width} (needed : Required rules.attachment (plan choice) object) :
    Readable layout poolZone state contains failed object := by
  have sound : PoolEvacuation.Sound layout needs (fun _ => ()) () (withInput state contains object) :=
    ⟨ready.accounting, fun version placed => ⟨rfl, ready.registered version placed.1⟩⟩
  obtain ⟨version, remains, _, present, charged⟩ :=
    PoolEvacuation.protection_covers_any_single_zone_failure sound (ready.coverage choice selected object needed) failed
  exact ⟨version, remains.1.1, remains.1.2, remains.2.1, remains.2.2, present, charged⟩

theorem each_selectable_view_can_recover_after_the_same_fault
    {observed : Scope Command} {revision : Nat}
    (certified : CanCertify observed (currentScope revision generation)
      (Ready rules generation online voterZone layout poolZone needs state contains selectors plan))
    {choice : JournalRotation.View} (selected : JointCheckpoint.Selectable selectors choice)
    (failed : Zone) :
    Bound rules (plan choice) choice generation.basis ∧
    Majority generation.ledger.members (survivingVoters online voterZone failed) ∧
    (∀ responders, Majority generation.ledger.members responders →
      (∀ voter ∈ generation.ledger.members, responders voter = true →
        survivingVoters online voterZone failed voter = true) →
      ∃ voter ∈ generation.ledger.members, responders voter = true ∧
        survivingVoters online voterZone failed voter = true ∧ generation.installed voter generation.basis) ∧
    ∀ object, Required rules.attachment (plan choice) object →
      Readable layout poolZone state contains failed object := by
  have ready := certified.2
  refine ⟨ready.viewBinding choice selected, ready.afterLoss failed, ?_, fun _ required =>
    exact_object_survives ready selected failed required⟩
  intro responders majority available
  obtain ⟨holders, installedQuorum, exactInstall⟩ := ready.installed
  obtain ⟨voter, member, responded, holds⟩ :=
    JournalRefinement.majorities_overlap generation.ledger.members responders holders majority installedQuorum
  exact ⟨voter, member, responded, available voter member responded, exactInstall voter member holds⟩

theorem every_required_manifest_descendant_is_readable
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    {choice : JournalRotation.View} (selected : JointCheckpoint.Selectable selectors choice)
    (failed : Zone) {object : Field width} (needed : rules.necessary (plan choice).contents object) :
    Readable layout poolZone state contains failed (.dependency object) := by
  have included := (ready.viewBinding choice selected).opened.manifestCovers object needed
  exact exact_object_survives ready selected failed (.dependency included)

theorem a_bound_tail_attachment_is_required
    (rules : Rules width Control Data Command) (view : View width Control Data Command) :
    ∀ command ∈ view.tail, ∀ object, rules.attachment command object →
      Required rules.attachment view object := by
  intro command member object needed
  exact Required.tailInput command member needed

theorem the_old_selectable_tail_still_has_exact_coverage
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    (failed : Zone) {command : Command} (member : command ∈ (plan selectors.stable).tail)
    {object : Input width} (needed : rules.attachment command object) :
    Readable layout poolZone state contains failed object := by
  exact exact_object_survives ready (.inl rfl) failed
    (a_bound_tail_attachment_is_required rules (plan selectors.stable) command member object needed)

theorem publishing_a_candidate_preserves_the_stable_recovery_path
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    {candidate : JournalRotation.View} (bound : Bound rules (plan candidate) candidate generation.basis)
    (covered : ∀ object, Required rules.attachment (plan candidate) object →
      PoolEvacuation.Protected layout poolZone (withInput state contains object)) :
    Ready rules generation online voterZone layout poolZone needs state contains
      {selectors with visible := candidate} plan := by
  refine ⟨ready.distinctVoters, ready.installed, ready.afterLoss, ?_, ready.accounting,
    ready.registered, ?_⟩
  · intro choice selected
    rcases selected with stable | visible
    · exact ready.viewBinding choice (.inl stable)
    · change choice = candidate at visible
      subst choice
      exact bound
  · intro choice selected object needed
    rcases selected with stable | visible
    · exact ready.coverage choice (.inl stable) object needed
    · change choice = candidate at visible
      subst choice
      exact covered object needed

theorem choosing_one_durable_selector_preserves_the_protected_cut
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    (retained : JointCheckpoint.Sound selectors) {selected : JournalRotation.View}
    (allowed : JointCheckpoint.Selectable selectors selected) :
    Ready rules generation online voterZone layout poolZone needs state contains
      {selectors with stable := selected, visible := selected} plan ∧
    JointCheckpoint.Sound {selectors with stable := selected, visible := selected} := by
  have remained : ∀ choice, JointCheckpoint.Selectable
      {selectors with stable := selected, visible := selected} choice →
      JointCheckpoint.Selectable selectors choice := by
    intro choice chosen
    have same : choice = selected := chosen.elim id id
    exact same.symm ▸ allowed
  refine ⟨⟨ready.distinctVoters, ready.installed, ready.afterLoss, ?_, ready.accounting,
    ready.registered, ?_⟩, JointCheckpoint.selecting_a_covered_base_preserves_all_evidence retained allowed⟩
  · exact fun choice chosen => ready.viewBinding choice (remained choice chosen)
  · exact fun choice chosen => ready.coverage choice (remained choice chosen)

theorem after_reconfiguration_the_recovered_cut_contains_earlier_choices
    {old first : Generation Voter Command} (handoff : ConfigurationClosure.Handoff old first)
    (later : ConfigurationClosure.Changes first generation)
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    {ballot : Nat} {earlier : List Command} (chosen : PrefixAgreement.Chosen old.ledger ballot earlier)
    {choice : JournalRotation.View} (selected : JointCheckpoint.Selectable selectors choice) (failed : Zone) :
    ∃ voter ∈ generation.ledger.members,
      survivingVoters online voterZone failed voter = true ∧
      generation.installed voter ((plan choice).base ++ (plan choice).tail) ∧
      earlier <+: (plan choice).base ++ (plan choice).tail := by
  rw [(ready.viewBinding choice selected).exactPrefix]
  exact ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority handoff later
    ready.installed (survivingVoters online voterZone failed) (ready.afterLoss failed) chosen

theorem a_certified_view_replays_the_same_ordered_input
    (ready : Ready rules generation online voterZone layout poolZone needs state contains selectors plan)
    {choice : JournalRotation.View} (selected : JointCheckpoint.Selectable selectors choice)
    {Result : Type} (replay : List Command → Result) :
    replay ((plan choice).base ++ (plan choice).tail) = replay generation.basis := by
  exact congrArg replay (ready.viewBinding choice selected).exactPrefix

#print axioms accepted_certificate_uses_current_scope
#print axioms each_selectable_view_can_recover_after_the_same_fault
#print axioms every_required_manifest_descendant_is_readable
#print axioms a_bound_tail_attachment_is_required
#print axioms the_old_selectable_tail_still_has_exact_coverage
#print axioms publishing_a_candidate_preserves_the_stable_recovery_path
#print axioms choosing_one_durable_selector_preserves_the_protected_cut
#print axioms after_reconfiguration_the_recovered_cut_contains_earlier_choices
#print axioms a_certified_view_replays_the_same_ordered_input

end JointProtection
