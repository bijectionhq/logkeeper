import DeliveryRecovery

set_option warningAsError true

namespace SealedDeliveryHandoff

open ChosenReplay (Lineage)
open DeliveryBook (Book Entry atKey)
open EnvelopeCodec (Bytes Field readWord)
open RetainedDelivery (Rules Image)
open SourceOutcomes (Key)

variable {width slots capacity limit : Nat} {Payload Ticket Signature : Type}

structure Control (width capacity limit : Nat) where
  reads : JointReadRecovery.Section capacity
  readThrough : Field width
  delivery : DeliveryBook.Section (width := width) limit

abbrev Catalog (width capacity limit : Nat) :=
  EnvelopeRecovery.Catalog width (Control width capacity limit) Unit

abbrev Contents (width capacity limit : Nat) :=
  EnvelopeRecovery.Contents width (Control width capacity limit) Unit

structure Restored (capacity limit : Nat) where
  reads : RecoverableRead.State capacity
  readThrough : Nat
  delivery : Book limit capacity

def snapshot (image : Image slots capacity limit Payload) : Restored capacity limit :=
  ⟨image.ordered.reads, image.ordered.readThrough, image.deliveries⟩

def withJournal (restored : Restored capacity limit) (sealed : JointSource.Image slots Payload) :
    Image slots capacity limit Payload :=
  ⟨⟨sealed, restored.reads, restored.readThrough⟩, restored.delivery⟩

def capture (width : Nat) (restored : Restored capacity limit) : Control width capacity limit :=
  ⟨JointReadRecovery.encodeSection width restored.reads, EnvelopeCodec.word width restored.readThrough,
    DeliveryBook.capture width restored.delivery⟩

noncomputable def openDelivery (contents : Contents width capacity limit)
    (needs : Entry capacity → Field width → Prop) : Option (Book limit capacity) := by
  classical
  exact match DeliveryBook.openSection contents.control.delivery with
  | none => none
  | some book =>
      if ∀ object, DeliveryRecovery.Needs needs book object → object ∈ contents.dependencies then some book else none

theorem a_decoded_delivery_requires_its_own_manifest_entries
    (contents : Contents width capacity limit) (needs : Entry capacity → Field width → Prop)
    (book : Book limit capacity) (opened : openDelivery contents needs = some book) :
    DeliveryBook.openSection contents.control.delivery = some book ∧
      ∀ object, DeliveryRecovery.Needs needs book object → object ∈ contents.dependencies := by
  cases decoded : DeliveryBook.openSection (capacity := capacity) contents.control.delivery with
  | none => simp [openDelivery, decoded] at opened
  | some decodedBook =>
      simp only [openDelivery, decoded] at opened
      split at opened
      · next covers =>
          cases opened
          exact ⟨rfl, covers⟩
      · contradiction

noncomputable def openControl (catalog : Catalog width capacity limit) (authenticate : Bytes → Prop)
    (anchor : EnvelopeRecovery.Anchor width) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (deliveryNeeds : Entry capacity → Field width → Prop) (wire : Bytes) :
    Option (Contents width capacity limit × Restored capacity limit) :=
  match JointReadRecovery.openNamedReads catalog Control.reads authenticate anchor (fun _ => False) readNeeds wire with
  | none => none
  | some (contents, reads) =>
      (openDelivery contents deliveryNeeds).map (fun book =>
        (contents, ⟨reads, readWord contents.control.readThrough.val, book⟩))

theorem an_exact_control_opens_both_books_and_the_writer_floor
    {historical : RTDBFailover.Barrier → Prop} {env : SnapshotAdmission.Environment}
    (catalog : Catalog width capacity limit) (authenticate : Bytes → Prop)
    (anchor : EnvelopeRecovery.Anchor width) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (deliveryNeeds : Entry capacity → Field width → Prop) (wire : Bytes)
    (header : EnvelopeCodec.Envelope width) (contents : Contents width capacity limit)
    (restored : Restored capacity limit)
    (opened : EnvelopeRecovery.openChecked catalog authenticate anchor (fun _ => False) wire = some (header, contents))
    (exactControl : contents.control = capture width restored)
    (sound : RecoverableRead.SoundFor width env historical restored.reads)
    (valid : restored.delivery.Valid width)
    (readFloorFits : restored.readThrough < EnvelopeCodec.wordLimit width)
    (positive : 0 < width)
    (coversReads : ∀ object, JointReadRecovery.Needs readNeeds restored.reads object → object ∈ contents.dependencies)
    (coversDelivery : ∀ object, DeliveryRecovery.Needs deliveryNeeds restored.delivery object →
      object ∈ contents.dependencies) :
    openControl catalog authenticate anchor readNeeds deliveryNeeds wire = some (contents, restored) := by
  have read := JointReadRecovery.the_authenticated_named_control_opens_its_exact_read_section catalog Control.reads
    authenticate anchor (fun _ => False) readNeeds wire header contents restored.reads sound positive opened
    (congrArg Control.reads exactControl) coversReads
  have book : openDelivery contents deliveryNeeds = some restored.delivery := by
    simp only [openDelivery, exactControl, capture,
      DeliveryBook.the_bounded_delivery_book_reopens_from_its_exact_section restored.delivery positive valid]
    exact ite_eq_left coversDelivery
  have floor : readWord contents.control.readThrough.val = restored.readThrough := by
    rw [exactControl]
    exact EnvelopeCodec.fixed_width_words_roundtrip readFloorFits
  simp only [openControl, read, book, floor, Option.map_some]

theorem opening_one_control_authenticates_the_original_dependencies_of_both_books
    (catalog : Catalog width capacity limit) (authenticate : Bytes → Prop)
    (anchor : EnvelopeRecovery.Anchor width) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (deliveryNeeds : Entry capacity → Field width → Prop) (wire : Bytes)
    (contents : Contents width capacity limit) (restored : Restored capacity limit)
    (opened : openControl catalog authenticate anchor readNeeds deliveryNeeds wire = some (contents, restored)) :
    (∀ object, JointReadRecovery.Needs readNeeds restored.reads object → catalog.retained object) ∧
      ∀ object, DeliveryRecovery.Needs deliveryNeeds restored.delivery object → catalog.retained object := by
  cases named : JointReadRecovery.openNamedReads catalog Control.reads authenticate anchor
      (fun _ => False) readNeeds wire with
  | none => simp [openControl, named] at opened
  | some pair =>
      obtain ⟨namedContents, reads⟩ := pair
      cases book : openDelivery namedContents deliveryNeeds with
      | none => simp [openControl, named, book] at opened
      | some deliveries =>
          simp only [openControl, named, book, Option.map_some, Option.some.injEq, Prod.mk.injEq] at opened
          obtain ⟨rfl, rfl⟩ := opened
          obtain ⟨⟨_, authenticated, _⟩, readCoverage⟩ :=
            JointReadRecovery.named_read_recovery_pins_all_original_dependencies catalog Control.reads
              authenticate anchor (fun _ => False) readNeeds wire namedContents reads named
          have deliveryCoverage := (a_decoded_delivery_requires_its_own_manifest_entries
            namedContents deliveryNeeds deliveries book).2
          exact ⟨readCoverage, fun object needed => authenticated.covered object (deliveryCoverage object needed)⟩

structure Store (width capacity limit : Nat) where
  catalog : Catalog width capacity limit
  authenticated : Bytes → Prop
  readNeeds : SnapshotAdmission.Basis → Field width → Prop
  deliveryNeeds : Entry capacity → Field width → Prop

noncomputable def atPosition (anchor : EnvelopeRecovery.Anchor width) (position : Nat) : Bool :=
  decide (readWord anchor.position.val = position)

noncomputable def mount (rules : JointSource.Rules width slots Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width) :
    Option (Restored capacity limit) := do
  let (record, evidence, _) ← JointSource.openSeal rules lineage sealed key
  if atPosition anchor record.anchor.position then
    (openControl store.catalog store.authenticated anchor store.readNeeds store.deliveryNeeds evidence.readControl).map Prod.snd
  else none

theorem mount_uses_only_the_named_attachment_at_the_seal_position
    (rules : JointSource.Rules width slots Payload Ticket) (lineage : Lineage)
    (sealed : JointSource.Image slots Payload) (key : Key slots)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (restored : Restored capacity limit) (mounted : mount rules lineage sealed key store anchor = some restored) :
    ∃ record evidence workers contents,
      JointSource.openSeal rules lineage sealed key = some (record, evidence, workers) ∧
      readWord anchor.position.val = record.anchor.position ∧
      openControl store.catalog store.authenticated anchor store.readNeeds store.deliveryNeeds evidence.readControl =
        some (contents, restored) := by
  cases named : JointSource.openSeal rules lineage sealed key with
  | none => simp [mount, named] at mounted
  | some tuple =>
      obtain ⟨record, evidence, workers⟩ := tuple
      by_cases position : readWord anchor.position.val = record.anchor.position
      · cases opened : openControl store.catalog store.authenticated anchor store.readNeeds store.deliveryNeeds
            evidence.readControl with
        | none => simp [mount, named, atPosition, position, opened] at mounted
        | some pair =>
            obtain ⟨contents, image⟩ := pair
            simp [mount, named, atPosition, position, opened] at mounted
            cases mounted
            exact ⟨record, evidence, workers, contents, rfl, position, opened⟩
      · simp [mount, named, atPosition, position] at mounted

def MatchesCut (before after : Restored capacity limit) : Prop :=
  before.reads = after.reads ∧ before.readThrough = after.readThrough ∧ before.delivery = after.delivery

theorem matching_cut_must_compare_the_delivery_book
    (expected mounted : Restored capacity limit) (agreed : MatchesCut mounted expected) :
    mounted.delivery = expected.delivery := by
  exact agreed.2.2

def acceptedJournal (result : Image slots capacity limit Payload × RetainedDelivery.Reply Payload capacity) :
    Option (Image slots capacity limit Payload) :=
  match result with
  | (image, .source (.journal .accepted)) => some image
  | _ => none

theorem acceptedJournal_iff (result : Image slots capacity limit Payload × RetainedDelivery.Reply Payload capacity)
    (image : Image slots capacity limit Payload) :
    acceptedJournal result = some image ↔ result = (image, .source (.journal .accepted)) := by
  obtain ⟨state, outcome⟩ := result
  cases outcome <;> simp [acceptedJournal]
  case source reply =>
    cases reply <;> simp
    case journal response => cases response <;> simp

noncomputable def chooseSeal (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (source : Image slots capacity limit Payload) (writer : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width) := by
  classical
  exact match acceptedJournal (RetainedDelivery.decide rules lineage source
      (.source (.journal (.seal writer key vector body evidence)))) with
  | some sealed =>
      match mount rules.ordered.journal lineage sealed.ordered.journal key store anchor with
      | some restored =>
          if atPosition anchor (RetainedDelivery.position sealed) ∧ MatchesCut restored (snapshot sealed) then
            some sealed
          else none
      | none => none
  | none => none

theorem choosing_a_seal_checks_its_mounted_books_and_floor_against_the_applied_cut
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (source sealed : Image slots capacity limit Payload) (writer : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (accepted : chooseSeal rules lineage source writer key vector body evidence store anchor = some sealed) :
    RetainedDelivery.decide rules lineage source (.source (.journal (.seal writer key vector body evidence))) =
      (sealed, .source (.journal .accepted)) ∧
    readWord anchor.position.val = RetainedDelivery.position sealed ∧
    mount rules.ordered.journal lineage sealed.ordered.journal key store anchor = some (snapshot sealed) := by
  cases reduced : acceptedJournal (RetainedDelivery.decide rules lineage source
      (.source (.journal (.seal writer key vector body evidence)))) with
  | none => simp [chooseSeal, reduced] at accepted
  | some candidate =>
      cases mounted : mount rules.ordered.journal lineage candidate.ordered.journal key store anchor with
      | none => simp [chooseSeal, reduced, mounted] at accepted
      | some restored =>
          simp only [chooseSeal, reduced, mounted] at accepted
          split at accepted
          · next exactCut =>
              cases accepted
              have sameRead := exactCut.2.1
              have sameFloor := exactCut.2.2.1
              have sameDelivery := matching_cut_must_compare_the_delivery_book _ _ exactCut.2
              have same : restored = snapshot sealed := by
                cases restored
                cases sealed with
                | mk ordered delivery =>
                    cases ordered
                    simp only [snapshot, Restored.mk.injEq]
                    exact ⟨sameRead, sameFloor, sameDelivery⟩
              exact ⟨(acceptedJournal_iff _ _).mp reduced, of_decide_eq_true exactCut.1, same ▸ mounted⟩
          · contradiction

noncomputable def activate (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width) :
    Option (Image slots capacity limit Payload) :=
  match mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor with
  | none => none
  | some restored =>
      acceptedJournal (RetainedDelivery.decide rules lineage (withJournal restored sealed)
        (.source (.journal (.activate install))))

theorem activation_uses_the_existing_ordered_decision_and_preserves_the_delivery_book
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (target : Image slots capacity limit Payload)
    (installed : activate rules lineage sealed install store anchor = some target) :
    ∃ restored, mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor =
      some restored ∧
    RetainedDelivery.decide rules lineage (withJournal restored sealed) (.source (.journal (.activate install))) =
      (target, .source (.journal .accepted)) ∧ target.deliveries = restored.delivery := by
  cases mounted : mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor with
  | none => simp [activate, mounted] at installed
  | some restored =>
      have reduced := (acceptedJournal_iff _ target).mp (by simpa only [activate, mounted] using installed)
      have kept := congrArg (fun applied => applied.1.deliveries) reduced
      exact ⟨restored, rfl, reduced, kept.symm⟩

theorem a_local_mounted_cut_and_valid_install_are_sufficient_for_activation
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (restored : Restored capacity limit) (target : Image slots capacity limit Payload)
    (mounted : mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor =
      some restored)
    (installed : RetainedDelivery.decide rules lineage (withJournal restored sealed) (.source (.journal (.activate install))) =
      (target, .source (.journal .accepted))) :
    activate rules lineage sealed install store anchor = some target := by
  simp [activate, mounted, acceptedJournal_iff, installed]

theorem source_to_target_preserves_each_delivery_and_the_issuance_floor
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (source sealed target : Image slots capacity limit Payload) (writer : Kernel.Writer)
    (key : Key slots) (vector : RealizedSource.Vector) (body : JointSource.SealEvidence) (evidence : Ticket)
    (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (selected : chooseSeal rules lineage source writer key vector body evidence store anchor = some sealed)
    (sameMove : install.original.installation.anchor.decision.key = key)
    (activated : activate rules lineage sealed.ordered.journal install store anchor = some target) :
    target.deliveries = source.deliveries := by
  obtain ⟨applied, _, sealedCut⟩ := choosing_a_seal_checks_its_mounted_books_and_floor_against_the_applied_cut
    rules lineage source sealed writer key vector body evidence store anchor selected
  obtain ⟨restored, targetCut, _, kept⟩ := activation_uses_the_existing_ordered_decision_and_preserves_the_delivery_book
    rules lineage sealed.ordered.journal install store anchor target activated
  rw [sameMove, sealedCut] at targetCut
  have same : snapshot sealed = restored := Option.some.inj targetCut
  have unchanged : source.deliveries = sealed.deliveries :=
    congrArg (fun outcome => outcome.1.deliveries) applied
  rw [kept, ← same]
  exact unchanged.symm

theorem activation_refuses_a_missing_independent_delivery_extent
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width) (object : Field width)
    (missing : ¬ store.catalog.retained object)
    (needed : ∀ restored,
      mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor =
        some restored → DeliveryRecovery.Needs store.deliveryNeeds restored.delivery object) :
    activate rules lineage sealed install store anchor = none := by
  cases installed : activate rules lineage sealed install store anchor with
  | none => rfl
  | some target =>
      obtain ⟨restored, mounted, _, _⟩ := activation_uses_the_existing_ordered_decision_and_preserves_the_delivery_book
        rules lineage sealed install store anchor target installed
      obtain ⟨_, evidence, _, contents, _, _, opened⟩ := mount_uses_only_the_named_attachment_at_the_seal_position
        rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor restored mounted
      have coverage := (opening_one_control_authenticates_the_original_dependencies_of_both_books store.catalog
        store.authenticated anchor store.readNeeds store.deliveryNeeds evidence.readControl contents restored opened).2
      exact (missing (coverage object (needed restored mounted))).elim

theorem the_sealed_predecessor_cannot_order_settlement
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (image : Image slots capacity limit Payload) (key : Key limit) (borrow : PoolState.Identity)
    (evidence : Ticket) (target : Kernel.Placement) (writer : Kernel.Writer)
    (sealed : OrderedReadReplay.authority image.ordered = .sealed target writer) :
    RetainedDelivery.decide rules lineage image (.settle key borrow evidence) = (RetainedDelivery.advance image, .refused) := by
  cases found : atKey image.deliveries key <;> simp [RetainedDelivery.decide, found, sealed, OrderedReadReplay.deliveryOpen]

theorem an_activated_target_can_finish_the_original_paid_delivery
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (target : Image slots capacity limit Payload)
    (installed : activate rules lineage sealed install store anchor = some target)
    (restored : Restored capacity limit)
    (mounted : mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor =
      some restored)
    (key : Key limit) (row : Entry capacity) (found : atKey restored.delivery key = some row)
    (authenticate : RTDBFailover.Invocation → Prop)
    (held : Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → Bytes → Signature)
    (caller : authenticate row.reply.invocation) (paid : held key row.borrow row.request) :
    let body := AppliedBarrierReceipt.encode width row.reply
    RetainedDelivery.finish width target.deliveries key row.reply.invocation authenticate held sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ := by
  obtain ⟨original, exactMount, _, sameBook⟩ :=
    activation_uses_the_existing_ordered_decision_and_preserves_the_delivery_book
      rules lineage sealed install store anchor target installed
  cases Option.some.inj (exactMount.symm.trans mounted)
  rw [sameBook]
  exact RetainedDelivery.a_retained_result_completes_from_the_original_live_borrow_without_the_old_frame
    width restored.delivery key row authenticate held sign found caller paid

theorem an_activated_target_can_apply_the_original_providers_settlement
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (sealed : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (store : Store width capacity limit) (anchor : EnvelopeRecovery.Anchor width)
    (target : Image slots capacity limit Payload)
    (installed : activate rules lineage sealed install store anchor = some target)
    (restored : Restored capacity limit)
    (mounted : mount rules.ordered.journal lineage sealed install.original.installation.anchor.decision.key store anchor =
      some restored)
    (key : Key limit) (row : Entry capacity) (found : atKey restored.delivery key = some row)
    (evidence : Ticket)
    (openTarget : OrderedReadReplay.deliveryOpen (OrderedReadReplay.authority target.ordered) = true)
    (stop : rules.settled lineage key row evidence) :
    ∃ after, RetainedDelivery.decide rules lineage target (.settle key row.borrow evidence) = (after, .settled) ∧
      after.deliveries = DeliveryBook.clear restored.delivery key ∧ after.deliveries.issued = restored.delivery.issued := by
  obtain ⟨original, exactMount, _, sameBook⟩ :=
    activation_uses_the_existing_ordered_decision_and_preserves_the_delivery_book
      rules lineage sealed install store anchor target installed
  cases Option.some.inj (exactMount.symm.trans mounted)
  refine ⟨{RetainedDelivery.advance target with deliveries := DeliveryBook.clear restored.delivery key}, ?_, rfl, rfl⟩
  simp [RetainedDelivery.decide, sameBook, found, openTarget, stop]

#print axioms a_decoded_delivery_requires_its_own_manifest_entries
#print axioms an_exact_control_opens_both_books_and_the_writer_floor
#print axioms opening_one_control_authenticates_the_original_dependencies_of_both_books
#print axioms mount_uses_only_the_named_attachment_at_the_seal_position
#print axioms matching_cut_must_compare_the_delivery_book
#print axioms choosing_a_seal_checks_its_mounted_books_and_floor_against_the_applied_cut
#print axioms activation_uses_the_existing_ordered_decision_and_preserves_the_delivery_book
#print axioms a_local_mounted_cut_and_valid_install_are_sufficient_for_activation
#print axioms source_to_target_preserves_each_delivery_and_the_issuance_floor
#print axioms activation_refuses_a_missing_independent_delivery_extent
#print axioms the_sealed_predecessor_cannot_order_settlement
#print axioms an_activated_target_can_finish_the_original_paid_delivery
#print axioms an_activated_target_can_apply_the_original_providers_settlement

end SealedDeliveryHandoff
