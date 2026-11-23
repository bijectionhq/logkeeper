import RetainedDelivery
import InvocationFloorProof

set_option warningAsError true

namespace DeliveryRecovery

open ChosenReplay (Lineage)
open EnvelopeCodec (Bytes Field)
open RetainedDelivery (Rules Image Frame replay)
open DeliveryBook (Entry Book atKey)
open SourceOutcomes (Key)

variable {width slots capacity limit : Nat} {Payload Ticket Voter Signature : Type}

structure Control (width slots capacity limit : Nat) (Payload : Type) where
  ordered : InvocationFloorProof.CheckpointControl slots capacity Payload
  delivery : DeliveryBook.Section (width := width) limit

abbrev Catalog (width slots capacity limit : Nat) (Payload : Type) :=
  EnvelopeRecovery.Catalog width (Control width slots capacity limit Payload) (FundedAppend.Source slots Payload)

def project (catalog : Catalog width slots capacity limit Payload) :
    EnvelopeRecovery.Catalog width (InvocationFloorProof.CheckpointControl slots capacity Payload) (FundedAppend.Source slots Payload) :=
  ⟨fun name => (catalog.control name).map Control.ordered, catalog.data, catalog.manifests, catalog.retained⟩

def Needs (required : Entry capacity → Field width → Prop) (book : Book limit capacity)
    (object : Field width) : Prop :=
  ∃ slot entry, book.rows slot = some entry ∧ required entry object

noncomputable def openCheckpoint (rules : Rules width slots capacity limit Payload Ticket)
    (catalog : Catalog width slots capacity limit Payload) (authenticate : Bytes → Prop)
    (anchor : EnvelopeRecovery.Anchor width) (coreNeeds : Field width → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (deliveryNeeds : Entry capacity → Field width → Prop)
    (wire : Bytes) : Option (Image slots capacity limit Payload) := by
  classical
  exact do
    let (_, contents) ← EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire
    let delivery ← DeliveryBook.openSection (capacity := capacity) contents.control.delivery
    if ∀ object, Needs deliveryNeeds delivery object → object ∈ contents.dependencies then
      (InvocationFloorProof.openCheckpoint rules.ordered (project catalog) authenticate anchor coreNeeds readNeeds wire).map
        (fun ordered => ⟨ordered, delivery⟩)
    else none

private theorem open_from_named_book
    (rules : Rules width slots capacity limit Payload Ticket) (catalog : Catalog width slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width) (coreNeeds : Field width → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (deliveryNeeds : Entry capacity → Field width → Prop)
    (wire : Bytes) (header : EnvelopeCodec.Envelope width)
    (contents : EnvelopeRecovery.Contents width (Control width slots capacity limit Payload) (FundedAppend.Source slots Payload))
    (book : Book limit capacity)
    (named : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire = some (header, contents))
    (saved : DeliveryBook.openSection contents.control.delivery = some book) :
    openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire =
      (by
        classical
        exact if ∀ object, Needs deliveryNeeds book object → object ∈ contents.dependencies then
          (InvocationFloorProof.openCheckpoint rules.ordered (project catalog) authenticate anchor coreNeeds readNeeds wire).map
            (fun ordered => (⟨ordered, book⟩ : Image slots capacity limit Payload))
        else none) := by
  classical
  simp only [openCheckpoint, named]
  change (do
    let delivery ← DeliveryBook.openSection (capacity := capacity) contents.control.delivery
    if ∀ object, Needs deliveryNeeds delivery object → object ∈ contents.dependencies then
      (InvocationFloorProof.openCheckpoint rules.ordered (project catalog) authenticate anchor coreNeeds readNeeds wire).map
        (fun ordered => (⟨ordered, delivery⟩ : Image slots capacity limit Payload))
    else none) = _
  rw [saved]
  rfl

theorem a_verified_checkpoint_recovers_the_exact_ordered_book_and_bounded_deliveries
    (rules : Rules width slots capacity limit Payload Ticket) (catalog : Catalog width slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width) (coreNeeds : Field width → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (deliveryNeeds : Entry capacity → Field width → Prop)
    (wire : Bytes) (header : EnvelopeCodec.Envelope width)
    (contents : EnvelopeRecovery.Contents width (Control width slots capacity limit Payload) (FundedAppend.Source slots Payload))
    (image : Image slots capacity limit Payload)
    (opened : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire = some (header, contents))
    (ordered : InvocationFloorProof.openCheckpoint rules.ordered (project catalog) authenticate anchor coreNeeds readNeeds wire = some image.ordered)
    (saved : contents.control.delivery = DeliveryBook.capture width image.deliveries)
    (valid : image.deliveries.Valid width) (positive : 0 < width)
    (covers : ∀ object, Needs deliveryNeeds image.deliveries object → object ∈ contents.dependencies) :
    openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire = some image := by
  have exactBook : DeliveryBook.openSection contents.control.delivery = some image.deliveries := by
    rw [saved]
    exact DeliveryBook.the_bounded_delivery_book_reopens_from_its_exact_section image.deliveries positive valid
  rw [open_from_named_book rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire header contents
    image.deliveries opened exactBook, ite_eq_left covers, ordered]
  cases image
  rfl

theorem a_verified_open_keeps_independent_delivery_dependencies_even_if_the_logical_read_closed
    (rules : Rules width slots capacity limit Payload Ticket) (catalog : Catalog width slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width) (coreNeeds : Field width → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (deliveryNeeds : Entry capacity → Field width → Prop)
    (wire : Bytes) (image : Image slots capacity limit Payload)
    (opened : openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire = some image) :
    ∀ object, Needs deliveryNeeds image.deliveries object → catalog.retained object := by
  classical
  cases exact : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire with
  | none => simp [openCheckpoint, exact] at opened
  | some pair =>
      obtain ⟨header, contents⟩ := pair
      cases saved : DeliveryBook.openSection (capacity := capacity) contents.control.delivery with
      | none => simp [openCheckpoint, exact, saved] at opened
      | some book =>
          rw [open_from_named_book rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire header contents
            book exact saved] at opened
          by_cases covers : ∀ object, Needs deliveryNeeds book object → object ∈ contents.dependencies
          · rw [ite_eq_left covers] at opened
            cases ordered : InvocationFloorProof.openCheckpoint rules.ordered (project catalog) authenticate anchor coreNeeds readNeeds wire with
            | none => simp [ordered] at opened
            | some source =>
                rw [ordered] at opened
                have combined : (⟨source, book⟩ : Image slots capacity limit Payload) = image := by
                  exact Option.some.inj opened
                subst image
                have evidence := EnvelopeRecovery.a_successful_open_has_all_authentication_and_custody_checks exact
                exact fun object need => evidence.covered object (covers object need)
          · rw [ite_eq_right covers] at opened
            contradiction

structure Base (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload) (history : List (Frame slots capacity limit Payload Ticket)) where
  cut : Nat
  image : Image slots capacity limit Payload
  within : cut ≤ history.length
  certified : replay rules lineage origin (history.take cut) = some image

noncomputable def reopen (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload)
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    (cutoff : List (Frame slots capacity limit Payload Ticket)) {ballot : Nat}
    (_chosen : PrefixAgreement.Chosen ledger ballot cutoff) (base : Base rules lineage origin cutoff)
    (media : List (Frame slots capacity limit Payload Ticket)) : Option (Image slots capacity limit Payload) := by
  classical
  exact if cutoff.drop base.cut <+: media then replay rules lineage base.image (cutoff.drop base.cut) else none

theorem either_exact_base_reopens_the_same_delivery_lifecycle
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload)
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    (cutoff : List (Frame slots capacity limit Payload Ticket)) {ballot : Nat}
    (chosen : PrefixAgreement.Chosen ledger ballot cutoff)
    (old new : Base rules lineage origin cutoff) (oldMedia newMedia : List (Frame slots capacity limit Payload Ticket))
    (first second : Image slots capacity limit Payload)
    (older : reopen rules lineage origin cutoff chosen old oldMedia = some first)
    (newer : reopen rules lineage origin cutoff chosen new newMedia = some second) :
    first = second := by
  have exact (base : Base rules lineage origin cutoff)
      (media : List (Frame slots capacity limit Payload Ticket)) {returned : Image slots capacity limit Payload}
      (opened : reopen rules lineage origin cutoff chosen base media = some returned) :
      replay rules lineage origin cutoff = some returned := by
    classical
    by_cases supplied : cutoff.drop base.cut <+: media
    · have replayed : replay rules lineage base.image (cutoff.drop base.cut) = some returned := by
        simpa [reopen, supplied] using opened
      rw [RetainedDelivery.replay_after_any_certified_base rules lineage origin base.image _ _ base.certified,
        List.take_append_drop] at replayed
      exact replayed
    · simp [reopen, supplied] at opened
  exact Option.some.inj ((exact old oldMedia older).symm.trans (exact new newMedia newer))

noncomputable def finishFromCheckpoint
    (rules : Rules width slots capacity limit Payload Ticket) (catalog : Catalog width slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width) (coreNeeds : Field width → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (deliveryNeeds : Entry capacity → Field width → Prop)
    (wire : Bytes) (key : Key limit) (call : RTDBFailover.Invocation)
    (isCaller : RTDBFailover.Invocation → Prop) (held : Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → Bytes → Signature) : Option (AppliedBarrierReceipt.Packet Signature) := do
  let image ← openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire
  RetainedDelivery.finish width image.deliveries key call isCaller held sign

theorem a_checkpoint_can_complete_an_independent_delivery_with_no_source_frame
    (rules : Rules width slots capacity limit Payload Ticket) (catalog : Catalog width slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width) (coreNeeds : Field width → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (deliveryNeeds : Entry capacity → Field width → Prop)
    (wire : Bytes) (image : Image slots capacity limit Payload)
    (opened : openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire = some image)
    (key : Key limit) (row : Entry capacity) (found : atKey image.deliveries key = some row)
    (isCaller : RTDBFailover.Invocation → Prop) (held : Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → Bytes → Signature)
    (caller : isCaller row.reply.invocation) (physical : held key row.borrow row.request) :
    (∀ object, deliveryNeeds row object → catalog.retained object) ∧
    (let body := AppliedBarrierReceipt.encode width row.reply
     finishFromCheckpoint rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire key
       row.reply.invocation isCaller held sign =
       some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩) := by
  have inTable : image.deliveries.rows key.slot = some row := by
    cases stored : image.deliveries.rows key.slot with
    | none => simp [atKey, stored] at found
    | some entry =>
        have matchesRow : entry = row ∧ row.serial = key.serial := by simpa [atKey, stored] using found
        exact congrArg some matchesRow.1
  refine ⟨fun object necessary =>
    a_verified_open_keeps_independent_delivery_dependencies_even_if_the_logical_read_closed
      rules catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire image opened object ⟨_, row, inTable, necessary⟩, ?_⟩
  simpa [finishFromCheckpoint, opened] using
    RetainedDelivery.a_retained_result_completes_from_the_original_live_borrow_without_the_old_frame
      width image.deliveries key row isCaller held sign found caller physical

theorem a_raw_delivery_frame_can_leave_once_every_selectable_cut_covers_outstanding_results
    (state : JointCheckpoint.Protection Nat (Key limit × Entry capacity)) (raw : Nat)
    (sound : JointCheckpoint.Sound state) (past : JointCheckpoint.NoReplayUse state raw)
    (unpinned : ¬ state.borrowed raw)
    (recovered : ∀ claim, state.owes claim → ∀ view, JointCheckpoint.Selectable state view → state.certified view claim) :
    JointCheckpoint.Sound (JointCheckpoint.remove state raw) := by
  exact JointCheckpoint.an_attachment_can_leave_only_when_all_three_uses_remain_covered sound
    ⟨past, unpinned, fun claim owes view selected => Or.inl (recovered claim owes view selected)⟩

#print axioms DeliveryBook.an_exact_insert_keeps_the_bounded_book_well_formed
#print axioms DeliveryBook.exact_release_keeps_the_issuance_frontier_and_other_rows
#print axioms DeliveryBook.an_old_obligation_cannot_use_a_recycled_slot
#print axioms DeliveryBook.each_representable_delivery_row_is_exactly_one_fixed_size_body
#print axioms DeliveryBook.the_bounded_delivery_book_reopens_from_its_exact_section
#print axioms DeliveryBook.a_framed_book_fits_one_counter_and_its_fixed_number_of_cells
#print axioms RetainedDelivery.the_bare_delivery_command_cannot_bypass_the_retained_book
#print axioms RetainedDelivery.a_successful_grant_commits_its_retained_evidence_in_the_same_ordered_step
#print axioms RetainedDelivery.a_stale_or_occupied_delivery_slot_refuses_without_changing_the_book
#print axioms RetainedDelivery.an_immutable_funding_proof_cannot_be_rebound_to_another_delivery
#print axioms RetainedDelivery.closing_the_original_read_leaves_the_independent_delivery_record
#print axioms RetainedDelivery.exact_settlement_clears_only_the_named_delivery_after_original_custody_stops
#print axioms RetainedDelivery.a_retained_result_completes_from_the_original_live_borrow_without_the_old_frame
#print axioms RetainedDelivery.possession_of_the_retained_result_cannot_finish_after_its_borrow_stops
#print axioms RetainedDelivery.every_replayed_trace_preserves_the_fixed_delivery_book_bound
#print axioms a_verified_checkpoint_recovers_the_exact_ordered_book_and_bounded_deliveries
#print axioms a_verified_open_keeps_independent_delivery_dependencies_even_if_the_logical_read_closed
#print axioms either_exact_base_reopens_the_same_delivery_lifecycle
#print axioms a_checkpoint_can_complete_an_independent_delivery_with_no_source_frame
#print axioms a_raw_delivery_frame_can_leave_once_every_selectable_cut_covers_outstanding_results

end DeliveryRecovery
