import JointSource
import ConfigurationClosure

set_option warningAsError true

namespace RankedJointReplay

open JointSource (Frame Image Rules)
open ChosenReplay (Lineage)

variable {width slots : Nat} {Payload Ticket Voter : Type}

structure Base (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : List (Frame slots Payload Ticket)) where
  cut : Nat
  image : Image slots Payload
  within : cut ≤ chosen.length
  certified : JointSource.replay rules lineage origin (chosen.take cut) = some image

structure Cut (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)) where
  ballot : Nat
  frames : List (Frame slots Payload Ticket)
  chosen : PrefixAgreement.Chosen ledger ballot frames

noncomputable def recover (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (origin : Image slots Payload) (chosen : List (Frame slots Payload Ticket))
    (base : Base rules lineage origin chosen) (physical : List (Frame slots Payload Ticket)) :
    Option (Image slots Payload) := by
  classical
  exact if chosen.drop base.cut <+: physical then
    JointSource.replay rules lineage base.image (chosen.drop base.cut)
  else none

noncomputable def reopen {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (cut : Cut ledger) (base : Base rules lineage origin cut.frames) (physical : List (Frame slots Payload Ticket)) :
    Option (Image slots Payload) :=
  recover rules lineage origin cut.frames base physical

theorem a_rival_or_missing_augmented_suffix_is_refused
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen physical : List (Frame slots Payload Ticket)) (base : Base rules lineage origin chosen)
    (wrong : ¬ chosen.drop base.cut <+: physical) :
    recover rules lineage origin chosen base physical = none := by
  simp [recover, wrong]

theorem the_complete_historical_suffix_is_used
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen physical : List (Frame slots Payload Ticket)) (base : Base rules lineage origin chosen)
    (supplied : chosen.drop base.cut <+: physical) :
    recover rules lineage origin chosen base physical = JointSource.replay rules lineage origin chosen := by
  rw [recover, ite_eq_left supplied]
  rw [← JointSource.replay_after_any_exact_prefix rules lineage origin base.image _ _ base.certified]
  rw [List.take_append_drop]

theorem two_certified_bases_recover_the_same_complete_state
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : Cut ledger) (old new : Base rules lineage origin chosen.frames)
    (oldPhysical newPhysical : List (Frame slots Payload Ticket)) (left right : Image slots Payload)
    (oldRecovery : reopen rules lineage origin chosen old oldPhysical = some left)
    (newRecovery : reopen rules lineage origin chosen new newPhysical = some right) :
    left = right := by
  have exact {base : Base rules lineage origin chosen.frames} {physical recovered}
      (opened : reopen rules lineage origin chosen base physical = some recovered) :
      JointSource.replay rules lineage origin chosen.frames = some recovered := by
    classical
    by_cases supplied : chosen.frames.drop base.cut <+: physical
    · exact (the_complete_historical_suffix_is_used rules lineage origin chosen.frames physical base supplied).symm.trans opened
    · have refused := a_rival_or_missing_augmented_suffix_is_refused rules lineage origin chosen.frames physical base supplied
      have impossible : (none : Option (Image slots Payload)) = some recovered := refused.symm.trans opened
      cases impossible
  exact Option.some.inj ((exact oldRecovery).symm.trans (exact newRecovery))

structure Control (slots : Nat) (Payload : Type) where
  book : FundedAppend.Book
  plans : Fin slots → Option (AllocationVector.Plan slots)
  seals : Fin slots → Option JointSource.SealEvidence
  windows : Nat → Option CompleteSettlement.Window
  receipts : ReceiptReplay.Rows Payload
  workers : EnvelopeCodec.Bytes

def controlOf (width : Nat) (image : Image slots Payload) : Control slots Payload :=
  ⟨image.source.book, image.plans, image.seals, image.windows, image.receipts,
    WorkerRosterCodec.encode width image.workers⟩

noncomputable def imageOf (rules : Rules width slots Payload Ticket) (control : Control slots Payload)
    (data : FundedAppend.Source slots Payload) : Option (Image slots Payload) := do
  let workers ← JointSource.openWorkers rules control.workers
  pure ⟨⟨data, control.book⟩, control.plans, control.seals, control.windows, control.receipts, workers⟩

theorem decoded_image_has_its_exact_control
    (rules : Rules width slots Payload Ticket) (control : Control slots Payload)
    (data : FundedAppend.Source slots Payload) (image : Image slots Payload)
    (opened : imageOf rules control data = some image) :
    control = controlOf width image := by
  cases parsed : JointSource.openWorkers rules control.workers with
  | none => simp [imageOf, parsed] at opened
  | some workers =>
      have exactBytes := (WorkerRosterCodec.an_opened_roster_names_its_exact_bytes parsed).1
      simp [imageOf, parsed] at opened
      subst image
      cases control
      simp_all [controlOf]

abbrev Contents (width slots : Nat) (Payload : Type) :=
  EnvelopeRecovery.Contents width (Control slots Payload) (FundedAppend.Source slots Payload)

def namedBase (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : List (Frame slots Payload Ticket)) (cut : Nat) (contents : Contents width slots Payload)
    (within : cut ≤ chosen.length) (image : Image slots Payload)
    (_decoded : imageOf rules contents.control contents.data = some image)
    (exactBody : JointSource.replay rules lineage origin (chosen.take cut) = some image) :
    Base rules lineage origin chosen :=
  ⟨cut, image, within, exactBody⟩

theorem either_named_envelope_recovers_the_same_vector_window_and_receipt_book
    {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : Cut ledger)
    {catalog : EnvelopeRecovery.Catalog width (Control slots Payload) (FundedAppend.Source slots Payload)}
    {authenticated : EnvelopeCodec.Bytes → Prop}
    {oldExpected newExpected : EnvelopeRecovery.Anchor width} {oldNeeded newNeeded : EnvelopeCodec.Field width → Prop}
    {oldWire newWire : EnvelopeCodec.Bytes} {oldHeader newHeader : EnvelopeCodec.Envelope width}
    {oldContents newContents : Contents width slots Payload}
    (oldOpened : EnvelopeRecovery.Opened catalog authenticated oldExpected oldNeeded oldWire oldHeader oldContents)
    (newOpened : EnvelopeRecovery.Opened catalog authenticated newExpected newNeeded newWire newHeader newContents)
    (old new : Base rules lineage origin chosen.frames)
    (oldBody : imageOf rules oldContents.control oldContents.data = some old.image)
    (newBody : imageOf rules newContents.control newContents.data = some new.image)
    (olderFrames newerFrames : List (Frame slots Payload Ticket)) (left right : Image slots Payload)
    (oldRead : reopen rules lineage origin chosen old olderFrames = some left)
    (newRead : reopen rules lineage origin chosen new newerFrames = some right) :
    left = right ∧
    catalog.control oldHeader.control = some (controlOf width old.image) ∧
    catalog.control newHeader.control = some (controlOf width new.image) ∧
    (∀ dependency, oldNeeded dependency ∨ newNeeded dependency → catalog.retained dependency) := by
  have oldNamed := (EnvelopeRecovery.exact_loading_resolves_all_three_named_components oldOpened.named).1
  have newNamed := (EnvelopeRecovery.exact_loading_resolves_all_three_named_components newOpened.named).1
  refine ⟨two_certified_bases_recover_the_same_complete_state rules lineage origin chosen old new
    olderFrames newerFrames left right oldRead newRead, ?_, ?_, ?_⟩
  · rw [oldNamed, decoded_image_has_its_exact_control rules _ _ _ oldBody]
  · rw [newNamed, decoded_image_has_its_exact_control rules _ _ _ newBody]
  · intro dependency use
    rcases use with first | next
    · exact EnvelopeRecovery.opened_checkpoint_covers_every_required_object oldOpened dependency first
    · exact EnvelopeRecovery.opened_checkpoint_covers_every_required_object newOpened dependency next

theorem a_ranked_successor_covers_the_full_earlier_frame_including_its_attachment
    {initial next current : ConfigurationClosure.Generation Voter (Frame slots Payload Ticket)}
    (change : ConfigurationClosure.Handoff initial next) (later : ConfigurationClosure.Changes next current)
    (installed : ConfigurationClosure.InstalledOnQuorum current) (available : Voter → Bool)
    (quorum : JournalRefinement.Majority current.ledger.members available) (old : Cut initial.ledger)
    (position : Nat) (frame : Frame slots Payload Ticket) (previous : old.frames[position]? = some frame) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧ current.installed voter current.basis ∧
      current.basis[position]? = some frame := by
  obtain ⟨voter, member, online, copy, inherited⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority change later installed available quorum old.chosen
  obtain ⟨suffix, ranked⟩ := inherited
  refine ⟨voter, member, online, copy, ?_⟩
  rw [← ranked, List.getElem?_append_left (List.getElem?_eq_some_iff.mp previous).1]
  exact previous

theorem replay_of_a_ranked_installed_basis_includes_the_exact_earlier_effects
    {initial next current : ConfigurationClosure.Generation Voter (Frame slots Payload Ticket)}
    (change : ConfigurationClosure.Handoff initial next) (later : ConfigurationClosure.Changes next current)
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin earlier : Image slots Payload)
    (old : Cut initial.ledger) (applied : JointSource.replay rules lineage origin old.frames = some earlier) :
    ∃ suffix, current.basis = old.frames ++ suffix ∧
      JointSource.replay rules lineage origin current.basis = JointSource.replay rules lineage earlier suffix := by
  have inherited := (ConfigurationClosure.handoff_inherits_every_prior_choice change old.chosen).trans
    (ConfigurationClosure.arbitrarily_many_changes_keep_installed_prefix later)
  obtain ⟨suffix, whole⟩ := inherited
  refine ⟨suffix, whole.symm, ?_⟩
  rw [← whole]
  exact JointSource.replay_after_any_exact_prefix rules lineage origin earlier _ _ applied

#print axioms a_rival_or_missing_augmented_suffix_is_refused
#print axioms the_complete_historical_suffix_is_used
#print axioms two_certified_bases_recover_the_same_complete_state
#print axioms either_named_envelope_recovers_the_same_vector_window_and_receipt_book
#print axioms a_ranked_successor_covers_the_full_earlier_frame_including_its_attachment
#print axioms replay_of_a_ranked_installed_basis_includes_the_exact_earlier_effects

end RankedJointReplay
