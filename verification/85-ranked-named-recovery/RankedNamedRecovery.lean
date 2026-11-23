import InvocationFloorProof
import ActivationSlot

set_option warningAsError true

namespace RankedNamedRecovery

open ChosenReplay (Lineage)
open EnvelopeCodec (Bytes Field readWord)
open OrderedReadReplay (Frame Image Rules replay)
open ConfigurationClosure (Certificate Generation Ranked Recovered VoterState)

variable {width slots capacity : Nat} {Payload Ticket Voter : Type}

structure Capture (source : Generation Voter (Frame slots capacity Payload Ticket)) where
  certificate : Certificate Voter (Frame slots capacity Payload Ticket)
  authorized : Nat → Prop
  atFence : Voter → VoterState (Frame slots capacity Payload Ticket)
  afterward : Voter → VoterState (Frame slots capacity Payload Ticket)
  ranked : Ranked source.ledger certificate
  reached : ∀ voter ∈ source.ledger.members, certificate.replied voter = true →
    ConfigurationClosure.Trace authorized ConfigurationClosure.initial (atFence voter)
  fenced : ∀ voter ∈ source.ledger.members, certificate.replied voter = true →
    (atFence voter).closedFor = some certificate.successor
  duringDelivery : ∀ voter ∈ source.ledger.members, certificate.replied voter = true →
    ConfigurationClosure.Trace authorized (atFence voter) (afterward voter)
  scopedReports : ∀ voter ∈ source.ledger.members, certificate.replied voter = true →
    certificate.captured voter = (atFence voter).acceptor.latest
  voted : ∀ voter ∈ source.ledger.members, ∀ vote,
    source.ledger.voted voter vote → (afterward voter).acceptor.votes vote

def cutoff {source : Generation Voter (Frame slots capacity Payload Ticket)} (capture : Capture source) :
    List (Frame slots capacity Payload Ticket) :=
  Recovered source.basis capture.certificate

theorem the_ranked_cutoff_inherits_every_choice_even_if_the_learner_died
    {source : Generation Voter (Frame slots capacity Payload Ticket)} (capture : Capture source)
    {ballot : Nat} {history : List (Frame slots capacity Payload Ticket)}
    (chosen : PrefixAgreement.Chosen source.ledger ballot history) :
    history <+: cutoff capture := by
  have covers := ConfigurationClosure.durable_fenced_reports_cover_even_delayed_certificate_assembly
    (ledger := source.ledger) (certificate := capture.certificate) capture.atFence capture.afterward
    capture.reached capture.fenced capture.duringDelivery capture.scopedReports capture.voted
  exact ConfigurationClosure.ranked_cut_covers_every_old_quorum_even_if_learned_late
    source.rules capture.ranked covers _ chosen

def CertifiedPrefix (source : Generation Voter (Frame slots capacity Payload Ticket))
    (history : List (Frame slots capacity Payload Ticket)) : Prop :=
  history <+: source.basis ∨ ∃ ballot, PrefixAgreement.Chosen source.ledger ballot history

theorem each_certified_base_is_a_prefix_of_the_exact_ranked_cutoff
    {source : Generation Voter (Frame slots capacity Payload Ticket)} (capture : Capture source)
    {history : List (Frame slots capacity Payload Ticket)} (certified : CertifiedPrefix source history) :
    history <+: cutoff capture := by
  rcases certified with inherited | ⟨ballot, chosen⟩
  · cases selected : capture.certificate.winner with
    | none => simpa [cutoff, Recovered, ConfigurationClosure.EmptyRecovery, selected] using inherited
    | some winner =>
        obtain ⟨voter, _, _, _, accepted⟩ := capture.ranked.authenticated winner selected
        simpa [cutoff, Recovered, selected] using inherited.trans (source.startsFromBasis voter winner accepted)
  · exact the_ranked_cutoff_inherits_every_choice_even_if_the_learner_died capture chosen

abbrev Control (slots capacity : Nat) (Payload : Type) :=
  InvocationFloorProof.CheckpointControl slots capacity Payload

abbrev Catalog (width slots capacity : Nat) (Payload : Type) :=
  EnvelopeRecovery.Catalog width (Control slots capacity Payload) (FundedAppend.Source slots Payload)

structure Store (width slots capacity : Nat) (Payload Ticket : Type) where
  issued : Catalog width slots capacity Payload
  available : Catalog width slots capacity Payload
  authenticate : Bytes → Prop
  coreNeeds : Field width → Prop
  readNeeds : SnapshotAdmission.Basis → Field width → Prop
  format : UInt8
  lineageName : Lineage → Field width
  prefixName : Lineage → List (Frame slots capacity Payload Ticket) → Field width
  immutable : ∀ header first current,
    EnvelopeRecovery.readNamed issued header = some first →
    EnvelopeRecovery.readNamed available header = some current → first = current

noncomputable abbrev openOn (rules : Rules width slots capacity Payload Ticket)
    (store : Store width slots capacity Payload Ticket) (catalog : Catalog width slots capacity Payload)
    (anchor : EnvelopeRecovery.Anchor width) (wire : Bytes) : Option (Image slots capacity Payload) :=
  InvocationFloorProof.openCheckpoint rules catalog store.authenticate anchor store.coreNeeds store.readNeeds wire

theorem both_openings_of_the_same_named_checkpoint_restore_the_same_control
    (rules : Rules width slots capacity Payload Ticket)
    (store : Store width slots capacity Payload Ticket) (anchor : EnvelopeRecovery.Anchor width) (wire : Bytes)
    (issued current : Image slots capacity Payload)
    (original : openOn rules store store.issued anchor wire = some issued)
    (reopened : openOn rules store store.available anchor wire = some current) :
    issued = current := by
  let project := fun control : Control slots capacity Payload => control.body.protectedReads
  let openReads := fun catalog : Catalog width slots capacity Payload =>
    JointReadRecovery.openNamedReads catalog project store.authenticate anchor store.coreNeeds store.readNeeds wire
  cases first : openReads store.issued with
  | none =>
      change JointReadRecovery.openNamedReads store.issued project store.authenticate anchor store.coreNeeds
        store.readNeeds wire = none at first
      simp [openOn, InvocationFloorProof.openCheckpoint, project, first] at original
  | some before =>
      obtain ⟨firstContents, firstReads⟩ := before
      cases second : openReads store.available with
      | none =>
          change JointReadRecovery.openNamedReads store.available project store.authenticate anchor store.coreNeeds
            store.readNeeds wire = none at second
          simp [openOn, InvocationFloorProof.openCheckpoint, project, second] at reopened
      | some after =>
          obtain ⟨laterContents, laterReads⟩ := after
          obtain ⟨⟨olderHeader, older, readOld⟩, _⟩ :=
            JointReadRecovery.named_read_recovery_pins_all_original_dependencies store.issued project
              store.authenticate anchor store.coreNeeds store.readNeeds wire firstContents firstReads first
          obtain ⟨⟨laterHeader, later, readLater⟩, _⟩ :=
            JointReadRecovery.named_read_recovery_pins_all_original_dependencies store.available project
              store.authenticate anchor store.coreNeeds store.readNeeds wire laterContents laterReads second
          have header : olderHeader = laterHeader := Option.some.inj (older.canonical.symm.trans later.canonical)
          have body : firstContents = laterContents := store.immutable olderHeader _ _ older.named (header.symm ▸ later.named)
          have reads : firstReads = laterReads := Option.some.inj (readOld.symm.trans (body.symm ▸ readLater))
          subst laterContents
          subst laterReads
          change JointReadRecovery.openNamedReads store.issued project store.authenticate anchor store.coreNeeds
            store.readNeeds wire = some (firstContents, firstReads) at first
          change JointReadRecovery.openNamedReads store.available project store.authenticate anchor store.coreNeeds
            store.readNeeds wire = some (firstContents, firstReads) at second
          simp only [openOn, InvocationFloorProof.openCheckpoint, project, first, second] at original reopened
          exact Option.some.inj (original.symm.trans reopened)

structure Publication
    (rules : Rules width slots capacity Payload Ticket) (store : Store width slots capacity Payload Ticket)
    (source : Generation Voter (Frame slots capacity Payload Ticket))
    (lineage : Lineage) (origin : Image slots capacity Payload) where
  history : List (Frame slots capacity Payload Ticket)
  anchor : EnvelopeRecovery.Anchor width
  wire : Bytes
  image : Image slots capacity Payload
  certified : CertifiedPrefix source history
  applied : replay rules lineage origin history = some image
  issued : openOn rules store store.issued anchor wire = some image

def Publication.NamesCut
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    (publication : Publication rules store source lineage origin) : Prop :=
  publication.anchor.format = store.format ∧ publication.anchor.lineage = store.lineageName lineage ∧
    publication.anchor.prefixCommitment = store.prefixName lineage publication.history ∧
    readWord publication.anchor.position.val = OrderedReadReplay.position origin + publication.history.length ∧
    readWord publication.anchor.dataEnd.val = publication.image.reads.view.head

noncomputable def stage
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    (capture : Capture source) (successor : Nat)
    (publication : Publication rules store source lineage origin) (media : List (Frame slots capacity Payload Ticket)) :
    Option (Image slots capacity Payload) := by
  classical
  let suffix := (cutoff capture).drop publication.history.length
  exact if capture.certificate.successor = successor ∧ publication.NamesCut ∧ suffix <+: media then
    match openOn rules store store.available publication.anchor publication.wire with
    | none => none
    | some image => replay rules lineage image suffix
  else none

theorem staging_uses_the_named_checkpoint_and_the_exact_ranked_suffix
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    (capture : Capture source) (successor : Nat) (publication : Publication rules store source lineage origin)
    (media : List (Frame slots capacity Payload Ticket)) {image : Image slots capacity Payload}
    (staged : stage capture successor publication media = some image) :
    capture.certificate.successor = successor ∧ publication.NamesCut ∧
    (cutoff capture).drop publication.history.length <+: media ∧
    openOn rules store store.available publication.anchor publication.wire = some publication.image ∧
    replay rules lineage origin (cutoff capture) = some image := by
  classical
  unfold stage at staged
  dsimp only at staged
  split at staged
  · next checked =>
      cases opened : openOn rules store store.available publication.anchor publication.wire with
      | none => simp [opened] at staged
      | some base =>
          have same := both_openings_of_the_same_named_checkpoint_restore_the_same_control rules store
            publication.anchor publication.wire publication.image base publication.issued opened
          subst base
          simp only [opened] at staged
          obtain ⟨suffix, total⟩ := each_certified_base_is_a_prefix_of_the_exact_ranked_cutoff capture publication.certified
          refine ⟨checked.1, checked.2.1, checked.2.2, rfl, ?_⟩
          rw [← total, OrderedReadReplay.replay_after_a_certified_combined_base rules lineage _ _ publication.applied]
          simpa [← total] using staged
  · simp at staged

theorem an_exact_open_and_covered_ranked_suffix_can_stage_without_successor_installation
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    (capture : Capture source) (successor : Nat) (publication : Publication rules store source lineage origin)
    (media : List (Frame slots capacity Payload Ticket)) (image : Image slots capacity Payload)
    (addressed : capture.certificate.successor = successor) (named : publication.NamesCut)
    (covered : (cutoff capture).drop publication.history.length <+: media)
    (opened : openOn rules store store.available publication.anchor publication.wire = some publication.image)
    (recovered : replay rules lineage origin (cutoff capture) = some image) :
    stage capture successor publication media = some image := by
  have exactMedia := each_certified_base_is_a_prefix_of_the_exact_ranked_cutoff capture publication.certified
  obtain ⟨suffix, total⟩ := exactMedia
  have suffixResult := OrderedReadReplay.replay_after_a_certified_combined_base rules lineage
    publication.history suffix publication.applied
  rw [total, recovered] at suffixResult
  have applied : replay rules lineage publication.image ((cutoff capture).drop publication.history.length) = some image := by
    simpa [← total] using suffixResult.symm
  simp [stage, addressed, named, covered, opened, applied]

structure Seed (slots capacity : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  revision : Nat
  frames : List (Frame slots capacity Payload Ticket)
  image : Image slots capacity Payload

structure Target (Voter : Type) (slots capacity : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  revision : Nat
  frontier : List (Frame slots capacity Payload Ticket)
  ledger : PrefixAgreement.Ledger Voter (Seed slots capacity Payload Ticket)
  rules : PrefixAgreement.Rules ledger
  devices : Voter → ActivationSlot.Device (Seed slots capacity Payload Ticket)
  reachable : ∀ voter ∈ ledger.members, ActivationSlot.Reachable (devices voter)
  recorded : ∀ voter ∈ ledger.members, ∀ vote, ledger.voted voter vote → (devices voter).acceptor.votes vote
  certified : ∀ voter ∈ ledger.members, ∀ vote, (devices voter).acceptor.latest = some vote → ledger.voted voter vote
  online : Voter → Bool

def Target.IsCurrent (target : Target Voter slots capacity Payload Ticket) (lineage : Lineage) (successor : Nat)
    (frames : List (Frame slots capacity Payload Ticket)) : Prop :=
  target.lineage = lineage ∧ target.revision = successor ∧ target.frontier = frames

theorem the_current_target_checks_its_exact_lineage_revision_and_cutoff
    (target : Target Voter slots capacity Payload Ticket) (lineage : Lineage) (successor : Nat)
    (frames : List (Frame slots capacity Payload Ticket)) :
    target.IsCurrent lineage successor frames ↔
      target.lineage = lineage ∧ target.revision = successor ∧ target.frontier = frames := by
  exact Iff.rfl

def Target.Installed (target : Target Voter slots capacity Payload Ticket)
    (frames : List (Frame slots capacity Payload Ticket)) (image : Image slots capacity Payload) : Prop :=
  ∃ ballot, ActivationSlot.Decided target.ledger ballot ⟨target.lineage, target.revision, frames, image⟩

theorem any_live_recovery_quorum_can_open_the_exact_chosen_installation
    (target : Target Voter slots capacity Payload Ticket)
    (frames : List (Frame slots capacity Payload Ticket)) (image : Image slots capacity Payload)
    (quorum : JournalRefinement.Majority target.ledger.members target.online)
    (installed : target.Installed frames image) :
    ∃ voter ∈ target.ledger.members, target.online voter = true ∧
      ActivationSlot.LatestBinds (target.devices voter) ⟨target.lineage, target.revision, frames, image⟩ ∧
      (target.devices voter).resident ⟨target.lineage, target.revision, frames, image⟩ := by
  obtain ⟨_, chosen⟩ := installed
  exact ActivationSlot.every_recovery_majority_can_read_a_previously_chosen_seed target.rules target.devices
    target.reachable target.recorded target.certified target.online quorum chosen

theorem a_successor_cannot_choose_two_different_installations_for_one_intent
    (target : Target Voter slots capacity Payload Ticket)
    {first second : List (Frame slots capacity Payload Ticket)} {earlier later : Image slots capacity Payload}
    (alreadyChosen : target.Installed first earlier) (retried : target.Installed second later) :
    first = second ∧ earlier = later := by
  obtain ⟨_, old⟩ := alreadyChosen
  obtain ⟨_, new⟩ := retried
  have same := ActivationSlot.seed_certificates_agree target.rules old new
  exact ⟨congrArg Seed.frames same, congrArg Seed.image same⟩

structure Staged
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    (capture : Capture source) (successor : Nat) (publication : Publication rules store source lineage origin)
    (media : List (Frame slots capacity Payload Ticket)) where
  image : Image slots capacity Payload
  checked : stage capture successor publication media = some image

noncomputable def prepare
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    (capture : Capture source) (successor : Nat) (publication : Publication rules store source lineage origin)
    (media : List (Frame slots capacity Payload Ticket)) : Option (Staged capture successor publication media) :=
  match staged : stage capture successor publication media with
  | none => none
  | some image => some ⟨image, staged⟩

noncomputable def activate
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    {capture : Capture source} {successor : Nat} {publication : Publication rules store source lineage origin}
    {media : List (Frame slots capacity Payload Ticket)}
    (staged : Staged capture successor publication media) (current : Target Voter slots capacity Payload Ticket) :
    Option (Image slots capacity Payload) := by
  classical
  exact if current.IsCurrent lineage successor (cutoff capture) ∧
      JournalRefinement.Majority current.ledger.members current.online ∧ current.Installed (cutoff capture) staged.image then
    some staged.image
  else none

theorem activation_requires_current_quorum_installation_of_the_exact_recovered_image
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    {capture : Capture source} {successor : Nat} {publication : Publication rules store source lineage origin}
    {media : List (Frame slots capacity Payload Ticket)}
    (staged : Staged capture successor publication media) (current : Target Voter slots capacity Payload Ticket)
    {image : Image slots capacity Payload} (activated : activate staged current = some image) :
    capture.certificate.successor = successor ∧
    (current.lineage = lineage ∧ current.revision = successor ∧ current.frontier = cutoff capture) ∧
    current.Installed (cutoff capture) image ∧
    (∃ voter ∈ current.ledger.members, current.online voter = true ∧
      (current.devices voter).resident ⟨lineage, successor, cutoff capture, image⟩) ∧
    replay rules lineage origin (cutoff capture) = some image := by
  unfold activate at activated
  split at activated
  · next ready =>
      cases activated
      have exactImage := staging_uses_the_named_checkpoint_and_the_exact_ranked_suffix capture successor publication media staged.checked
      have exactScope := (the_current_target_checks_its_exact_lineage_revision_and_cutoff _ _ _ _).1 ready.1
      obtain ⟨voter, member, online, _, backed⟩ :=
        any_live_recovery_quorum_can_open_the_exact_chosen_installation current _ _ ready.2.1 ready.2.2
      refine ⟨exactImage.1, exactScope, ready.2.2, ⟨voter, member, online, ?_⟩, exactImage.2.2.2.2⟩
      simpa [exactScope.1, exactScope.2.1] using backed
  · simp at activated

theorem a_staged_image_can_activate_after_installation_without_recontacting_the_old_quorum
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    {capture : Capture source} {successor : Nat} {publication : Publication rules store source lineage origin}
    {media : List (Frame slots capacity Payload Ticket)}
    (staged : Staged capture successor publication media) (current : Target Voter slots capacity Payload Ticket)
    (same : current.IsCurrent lineage successor (cutoff capture))
    (quorum : JournalRefinement.Majority current.ledger.members current.online)
    (installed : current.Installed (cutoff capture) staged.image) :
    activate staged current = some staged.image := by
  simp [activate, same, quorum, installed]

theorem two_named_checkpoints_activate_the_same_complete_ranked_read_state
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    {capture : Capture source} {successor : Nat} {older newer : Publication rules store source lineage origin}
    {olderMedia newerMedia : List (Frame slots capacity Payload Ticket)}
    (before : Staged capture successor older olderMedia) (after : Staged capture successor newer newerMedia)
    (current : Target Voter slots capacity Payload Ticket) (first second : Image slots capacity Payload)
    (old : activate before current = some first)
    (new : activate after current = some second) :
    first = second := by
  have firstReplay := (activation_requires_current_quorum_installation_of_the_exact_recovered_image before current old).2.2.2.2
  have secondReplay := (activation_requires_current_quorum_installation_of_the_exact_recovered_image after current new).2.2.2.2
  exact Option.some.inj (firstReplay.symm.trans secondReplay)

theorem activated_recovery_keeps_a_spent_nonce_from_an_unseen_earlier_choice
    {rules : Rules width slots capacity Payload Ticket} {store : Store width slots capacity Payload Ticket}
    {source : Generation Voter (Frame slots capacity Payload Ticket)}
    {lineage : Lineage} {origin : Image slots capacity Payload}
    {capture : Capture source} {successor : Nat} {publication : Publication rules store source lineage origin}
    {media : List (Frame slots capacity Payload Ticket)}
    (staged : Staged capture successor publication media) (current : Target Voter slots capacity Payload Ticket)
    {image earlier : Image slots capacity Payload} (activated : activate staged current = some image)
    (ballot : Nat) (prior : List (Frame slots capacity Payload Ticket))
    (chosen : PrefixAgreement.Chosen source.ledger ballot prior)
    (applied : replay rules lineage origin prior = some earlier)
    (writer : Kernel.Writer) (nonce : Nat)
    (spent : ReadInvocationFloor.Spent (OrderedReadReplay.authority earlier) earlier.readThrough writer nonce) :
    ReadInvocationFloor.Spent (OrderedReadReplay.authority image) image.readThrough writer nonce := by
  have exactImage := (activation_requires_current_quorum_installation_of_the_exact_recovered_image staged current activated).2.2.2.2
  obtain ⟨suffix, full⟩ := the_ranked_cutoff_inherits_every_choice_even_if_the_learner_died capture chosen
  have replayed := OrderedReadReplay.replay_after_a_certified_combined_base rules lineage prior suffix applied
  rw [full, exactImage] at replayed
  exact InvocationFloorProof.replay_preserves_an_already_consumed_invocation rules lineage suffix earlier image
    writer nonce spent replayed.symm

#print axioms the_ranked_cutoff_inherits_every_choice_even_if_the_learner_died
#print axioms each_certified_base_is_a_prefix_of_the_exact_ranked_cutoff
#print axioms both_openings_of_the_same_named_checkpoint_restore_the_same_control
#print axioms staging_uses_the_named_checkpoint_and_the_exact_ranked_suffix
#print axioms an_exact_open_and_covered_ranked_suffix_can_stage_without_successor_installation
#print axioms the_current_target_checks_its_exact_lineage_revision_and_cutoff
#print axioms any_live_recovery_quorum_can_open_the_exact_chosen_installation
#print axioms a_successor_cannot_choose_two_different_installations_for_one_intent
#print axioms activation_requires_current_quorum_installation_of_the_exact_recovered_image
#print axioms a_staged_image_can_activate_after_installation_without_recontacting_the_old_quorum
#print axioms two_named_checkpoints_activate_the_same_complete_ranked_read_state
#print axioms activated_recovery_keeps_a_spent_nonce_from_an_unseen_earlier_choice

end RankedNamedRecovery
