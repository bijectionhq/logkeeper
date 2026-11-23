import RecoverableRead

set_option warningAsError true

namespace JointReadRecovery

open ChosenReplay (Lineage)
open RecoverableRead (Row State Permit)
open EnvelopeCodec (Bytes Field)
open JointSource (Rules SealEvidence)

variable {width capacity slots : Nat} {Payload Ticket Voter : Type}

structure Section (capacity : Nat) where
  holds : SnapshotAdmission.View
  results : Fin capacity → Option Bytes

def encodeSection (width : Nat) (reads : State capacity) : Section capacity :=
  ⟨reads.view, fun slot => (reads.rows slot).map (RecoverableRead.encodeRow width)⟩

def decodeRows (width : Nat) (capture : Section capacity) : State capacity :=
  ⟨capture.holds, fun slot => (capture.results slot).bind (RecoverableRead.decodeRow width)⟩

def AllRowsDecode (width : Nat) (capture : Section capacity) : Prop :=
  ∀ slot wire, capture.results slot = some wire →
    ∃ row, RecoverableRead.decodeRow width wire = some row

def Paired (reads : State capacity) : Prop :=
  ∀ slot row, reads.rows slot = some row →
    ∃ basis, reads.view.snapshots row.serial = some basis ∧ basis.stop = row.reply.cut ∧
      SnapshotAdmission.Protected reads.view basis

noncomputable def openSection (width : Nat) (capture : Section capacity) : Option (State capacity) := by
  classical
  exact if AllRowsDecode width capture ∧ Paired (decodeRows width capture) then
    some (decodeRows width capture)
  else none

theorem a_sound_read_book_roundtrips_through_its_checkpoint_section
    {historical : RTDBFailover.Barrier → Prop} {env : SnapshotAdmission.Environment}
    (state : State capacity) (valid : RecoverableRead.SoundFor width env historical state)
    (positive : 0 < width) :
    openSection width (encodeSection width state) = some state := by
  have row (slot : Fin capacity) (result : Row) (found : state.rows slot = some result) :
      RecoverableRead.decodeRow width (RecoverableRead.encodeRow width result) = some result := by
    obtain ⟨fits, serial, _, _, _, _⟩ := valid.rows slot result found
    exact (RecoverableRead.a_live_result_row_has_an_exact_fixed_width_checkpoint_body result positive serial fits).1
  have restored : decodeRows width (encodeSection width state) = state := by
    rcases state with ⟨view, results⟩
    have equalRows : (fun slot => ((results slot).map (RecoverableRead.encodeRow width)).bind
        (RecoverableRead.decodeRow width)) = results := by
      funext slot
      cases found : results slot with
      | none => simp
      | some result => simp [row slot result found]
    exact congrArg (State.mk view) equalRows
  have complete : AllRowsDecode width (encodeSection width state) := by
    intro slot wire atSlot
    cases found : state.rows slot with
    | none => simp [encodeSection, found] at atSlot
    | some result =>
        have same : RecoverableRead.encodeRow width result = wire := by
          simpa [encodeSection, found] using atSlot
        exact ⟨result, same ▸ row slot result found⟩
  have paired : Paired state := by
    intro slot result found
    obtain ⟨_, _, _, basis, held, cut⟩ := valid.rows slot result found
    exact ⟨basis, held, cut, valid.snapshot.live result.serial basis held⟩
  simp [openSection, complete, restored, paired]

theorem opening_a_section_requires_all_present_rows_and_exact_holds
    (width : Nat) (capture : Section capacity) (reads : State capacity)
    (opened : openSection width capture = some reads) : AllRowsDecode width capture ∧ Paired reads := by
  unfold openSection at opened
  split at opened
  · cases opened
    assumption
  · contradiction

theorem a_malformed_occupied_slot_cannot_disappear_at_open
    (width : Nat) (capture : Section capacity) (slot : Fin capacity) (wire : Bytes)
    (present : capture.results slot = some wire) (broken : RecoverableRead.decodeRow width wire = none) :
    openSection width capture = none := by
  have absent : ¬ AllRowsDecode width capture := by
    intro all
    obtain ⟨row, found⟩ := all slot wire present
    rw [broken] at found
    cases found
  simp [openSection, absent]

def Needs (needs : SnapshotAdmission.Basis → Field width → Prop) (reads : State capacity)
    (object : Field width) : Prop :=
  ∃ slot row basis, reads.rows slot = some row ∧
    reads.view.snapshots row.serial = some basis ∧ needs basis object

noncomputable def openNamedReads
    (catalog : EnvelopeRecovery.Catalog width Control Data) (project : Control → Section capacity)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) : Option (EnvelopeRecovery.Contents width Control Data × State capacity) := by
  classical
  exact match EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire with
  | none => none
  | some (_, contents) =>
      match openSection width (project contents.control) with
      | none => none
      | some reads =>
          if ∀ object, Needs readNeeds reads object → object ∈ contents.dependencies then some (contents, reads)
          else none

theorem named_read_recovery_pins_all_original_dependencies
    (catalog : EnvelopeRecovery.Catalog width Control Data) (project : Control → Section capacity)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (contents : EnvelopeRecovery.Contents width Control Data) (reads : State capacity)
    (opened : openNamedReads catalog project authenticate anchor coreNeeds readNeeds wire = some (contents, reads)) :
    (∃ header, EnvelopeRecovery.Opened catalog authenticate anchor coreNeeds wire header contents ∧
      openSection width (project contents.control) = some reads) ∧
    ∀ object, Needs readNeeds reads object → catalog.retained object := by
  cases primary : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire with
  | none => simp [openNamedReads, primary] at opened
  | some both =>
      rcases both with ⟨header, body⟩
      cases secondary : openSection width (project body.control) with
      | none => simp [openNamedReads, primary, secondary] at opened
      | some restored =>
          simp only [openNamedReads, primary, secondary] at opened
          split at opened
          · next complete =>
              cases opened
              have exact := EnvelopeRecovery.a_successful_open_has_all_authentication_and_custody_checks primary
              exact ⟨⟨header, exact, secondary⟩, fun object necessary => exact.covered object (complete object necessary)⟩
          · contradiction

theorem the_authenticated_named_control_opens_its_exact_read_section
    {historical : RTDBFailover.Barrier → Prop} {env : SnapshotAdmission.Environment}
    (catalog : EnvelopeRecovery.Catalog width Control Data) (project : Control → Section capacity)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (header : EnvelopeCodec.Envelope width) (contents : EnvelopeRecovery.Contents width Control Data)
    (reads : State capacity) (sound : RecoverableRead.SoundFor width env historical reads) (positive : 0 < width)
    (opened : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire = some (header, contents))
    (exactSection : project contents.control = encodeSection width reads)
    (complete : ∀ object, Needs readNeeds reads object → object ∈ contents.dependencies) :
    openNamedReads catalog project authenticate anchor coreNeeds readNeeds wire = some (contents, reads) := by
  have decoded := a_sound_read_book_roundtrips_through_its_checkpoint_section reads sound positive
  simp only [openNamedReads, opened, exactSection, decoded, ite_eq_left complete]

theorem a_required_old_read_extent_missing_from_custody_prevents_open
    (catalog : EnvelopeRecovery.Catalog width Control Data) (project : Control → Section capacity)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (object : Field width) (lost : ¬ catalog.retained object)
    (everyCandidateNeeds : ∀ contents reads,
      openNamedReads catalog project authenticate anchor coreNeeds readNeeds wire = some (contents, reads) →
        Needs readNeeds reads object) :
    openNamedReads catalog project authenticate anchor coreNeeds readNeeds wire = none := by
  cases result : openNamedReads catalog project authenticate anchor coreNeeds readNeeds wire with
  | none => rfl
  | some both =>
      rcases both with ⟨contents, reads⟩
      exact False.elim (lost ((named_read_recovery_pins_all_original_dependencies catalog project authenticate anchor
        coreNeeds readNeeds wire contents reads result).2 object (everyCandidateNeeds contents reads result)))

structure Control (capacity slots : Nat) (Payload : Type) where
  source : RankedJointReplay.Control slots Payload
  protectedReads : Section capacity

noncomputable def recoverCheckpoint (rules : Rules width slots Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (Control capacity slots Payload) (FundedAppend.Source slots Payload))
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) : Option (JointSource.Image slots Payload × State capacity) := by
  classical
  exact match openNamedReads catalog Control.protectedReads authenticate anchor coreNeeds readNeeds wire with
  | none => none
  | some (contents, reads) =>
      match RankedJointReplay.imageOf rules contents.control.source contents.data with
      | none => none
      | some source =>
          if source.source.source.position = EnvelopeCodec.readWord anchor.position.val ∧
              reads.view.head = source.source.source.core.stream.history.length then
            some (source, reads)
          else none

theorem an_exact_checkpoint_restores_the_read_book_and_the_journal_together
    (rules : Rules width slots Payload Ticket)
    {historical : RTDBFailover.Barrier → Prop} {env : SnapshotAdmission.Environment}
    (catalog : EnvelopeRecovery.Catalog width (Control capacity slots Payload) (FundedAppend.Source slots Payload))
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (header : EnvelopeCodec.Envelope width)
    (contents : EnvelopeRecovery.Contents width (Control capacity slots Payload) (FundedAppend.Source slots Payload))
    (source : JointSource.Image slots Payload) (reads : State capacity)
    (sound : RecoverableRead.SoundFor width env historical reads) (positive : 0 < width)
    (opened : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire = some (header, contents))
    (exactSection : contents.control.protectedReads = encodeSection width reads)
    (complete : ∀ object, Needs readNeeds reads object → object ∈ contents.dependencies)
    (journal : RankedJointReplay.imageOf rules contents.control.source contents.data = some source)
    (orderedCut : source.source.source.position = EnvelopeCodec.readWord anchor.position.val)
    (dataCut : reads.view.head = source.source.source.core.stream.history.length) :
    recoverCheckpoint rules catalog authenticate anchor coreNeeds readNeeds wire = some (source, reads) := by
  have exactReads := the_authenticated_named_control_opens_its_exact_read_section catalog Control.protectedReads
    authenticate anchor coreNeeds readNeeds wire header contents reads sound positive opened exactSection complete
  simp [recoverCheckpoint, exactReads, journal, orderedCut, dataCut]

theorem the_same_checkpoint_bytes_cannot_recover_a_different_result_or_hold
    (rules : Rules width slots Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (Control capacity slots Payload) (FundedAppend.Source slots Payload))
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (first second : JointSource.Image slots Payload × State capacity)
    (a : recoverCheckpoint rules catalog authenticate anchor coreNeeds readNeeds wire = some first)
    (b : recoverCheckpoint rules catalog authenticate anchor coreNeeds readNeeds wire = some second) :
    first.1 = second.1 ∧ first.2.rows = second.2.rows ∧ first.2.view.snapshots = second.2.view.snapshots := by
  cases Option.some.inj (a.symm.trans b)
  exact ⟨rfl, rfl, rfl⟩

theorem a_source_refuses_a_seal_with_an_unbound_read_attachment
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (source : JointSource.Image slots Payload)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key slots) (vector : RealizedSource.Vector)
    (evidence : SealEvidence) (ticket : Ticket)
    (unbound : ∀ position, ¬ rules.sealedReads lineage position evidence.readControl) :
    JointSource.decide rules lineage source (.seal writer key vector evidence ticket) = JointSource.refuses source := by
  cases planned : source.plans key.slot with
  | none => simp [JointSource.decide, planned]
  | some plan =>
      by_cases scope : plan.move = key
      · cases chosen : RealizedSource.chooseSeal rules.source ⟨source.source, lineage, plan⟩ writer vector
            (rules.preparation ticket) <;>
          simp [JointSource.decide, planned, scope, chosen, unbound]
      · simp [JointSource.decide, planned, scope]

noncomputable def activateReadTarget (rules : Rules width slots Payload Ticket)
    (lineage : Lineage) (source : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (Section capacity) Unit)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) : Option (JointSource.Image slots Payload × State capacity) := by
  classical
  let key := install.original.installation.anchor.decision.key
  exact match JointSource.openSeal rules lineage source key with
  | none => none
  | some (record, evidence, _) =>
      if EnvelopeCodec.readWord anchor.position.val = record.anchor.position then
        match openNamedReads catalog id authenticate anchor (fun _ => False) readNeeds evidence.readControl with
        | none => none
        | some (_, reads) =>
            let chosen := JointSource.decide rules lineage source (.activate install)
            match chosen.2 with
            | .accepted => some (chosen.1, reads)
            | _ => none
      else none

theorem activation_uses_the_retained_attachment_from_exactly_the_sealed_cut
    (rules : Rules width slots Payload Ticket)
    (lineage : Lineage) (source : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (Section capacity) Unit)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (after : JointSource.Image slots Payload)
    (reads : State capacity)
    (activated : activateReadTarget rules lineage source install catalog authenticate anchor readNeeds = some (after, reads)) :
    ∃ record evidence workers contents,
      JointSource.openSeal rules lineage source install.original.installation.anchor.decision.key =
        some (record, evidence, workers) ∧
      EnvelopeCodec.readWord anchor.position.val = record.anchor.position ∧
      openNamedReads catalog id authenticate anchor (fun _ => False) readNeeds evidence.readControl = some (contents, reads) ∧
      JointSource.decide rules lineage source (.activate install) = (after, .accepted) := by
  cases sealed : JointSource.openSeal rules lineage source install.original.installation.anchor.decision.key with
  | none => simp [activateReadTarget, sealed] at activated
  | some found =>
      rcases found with ⟨record, evidence, workers⟩
      by_cases exactCut : EnvelopeCodec.readWord anchor.position.val = record.anchor.position
      · cases opened : openNamedReads catalog id authenticate anchor (fun _ => False) readNeeds evidence.readControl with
        | none => simp [activateReadTarget, sealed, exactCut, opened] at activated
        | some restored =>
            rcases restored with ⟨contents, original⟩
            cases result : JointSource.decide rules lineage source (.activate install) with
            | mk destination reply =>
                cases reply <;> simp [activateReadTarget, sealed, exactCut, opened, result] at activated
                case accepted =>
                  obtain ⟨rfl, rfl⟩ := activated
                  exact ⟨record, evidence, workers, contents, rfl, exactCut, opened, rfl⟩
      · simp [activateReadTarget, sealed, exactCut] at activated

theorem an_exact_mounted_read_image_can_activate_without_source_recontact
    (rules : Rules width slots Payload Ticket)
    (lineage : Lineage) (source : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (Section capacity) Unit)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop) (after : JointSource.Image slots Payload)
    (reads : State capacity) (record : RealizedSource.Record slots) (evidence : SealEvidence)
    (workers : JointSource.Workers) (contents : EnvelopeRecovery.Contents width (Section capacity) Unit)
    (sealed : JointSource.openSeal rules lineage source install.original.installation.anchor.decision.key =
      some (record, evidence, workers))
    (atCut : EnvelopeCodec.readWord anchor.position.val = record.anchor.position)
    (opened : openNamedReads catalog id authenticate anchor (fun _ => False) readNeeds evidence.readControl =
      some (contents, reads))
    (installed : JointSource.decide rules lineage source (.activate install) = (after, .accepted)) :
    activateReadTarget rules lineage source install catalog authenticate anchor readNeeds = some (after, reads) := by
  simp [activateReadTarget, sealed, atCut, opened, installed]

theorem the_installed_target_reissues_the_original_result_with_its_retained_custody
    (rules : Rules width slots Payload Ticket)
    {ledger : PrefixAgreement.Ledger Voter (JointSource.Frame slots Payload Ticket)}
    {origin : JointSource.Image slots Payload} {env : SnapshotAdmission.Environment}
    (lineage : Lineage) (source : JointSource.Image slots Payload) (install : RealizedSource.Install slots Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (Section capacity) Unit)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (after : JointSource.Image slots Payload) (reads : State capacity)
    (activated : activateReadTarget rules lineage source install catalog authenticate anchor readNeeds = some (after, reads))
    (sound : RecoverableRead.Sound env rules ledger origin reads)
    (slot : Fin capacity) (row : Row) (retained : reads.rows slot = some row)
    (callAuthenticated : RTDBFailover.Invocation → Prop) (authorized : callAuthenticated row.reply.invocation)
    (sign : RTDBFailover.Route → Bytes → Signature) :
    (∀ object, Needs readNeeds reads object → catalog.retained object) ∧
    let body := AppliedBarrierReceipt.encode width row.reply
    RecoverableRead.recoverInvocation width reads row.reply.invocation callAuthenticated sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ := by
  obtain ⟨_, evidence, _, contents, _, _, opened, _⟩ :=
    activation_uses_the_retained_attachment_from_exactly_the_sealed_cut rules lineage source install catalog
      authenticate anchor readNeeds after reads activated
  refine ⟨(named_read_recovery_pins_all_original_dependencies catalog id authenticate anchor
    (fun _ => False) readNeeds evidence.readControl contents reads opened).2, ?_⟩
  exact RecoverableRead.the_original_invocation_can_recover_even_if_the_permit_reply_was_lost
    sound slot row callAuthenticated sign retained authorized

noncomputable def orderClose (authority : Kernel.Authority) (env : SnapshotAdmission.Environment)
    (reads : State capacity) (permit : Permit capacity) : Option (State capacity) :=
  match authority with
  | .sealed _ _ => none
  | _ => RecoverableRead.close env reads permit

theorem only_the_current_owner_can_acknowledge_a_logical_close_during_handoff
    (target : Kernel.Placement) (previous : Kernel.Writer) (env : SnapshotAdmission.Environment)
    (reads : State capacity) (permit : Permit capacity) :
    orderClose (.sealed target previous) env reads permit = none ∧
    ∀ current, orderClose (.active current) env reads permit = RecoverableRead.close env reads permit := by
  exact ⟨rfl, fun _ => rfl⟩

#print axioms a_sound_read_book_roundtrips_through_its_checkpoint_section
#print axioms opening_a_section_requires_all_present_rows_and_exact_holds
#print axioms a_malformed_occupied_slot_cannot_disappear_at_open
#print axioms named_read_recovery_pins_all_original_dependencies
#print axioms the_authenticated_named_control_opens_its_exact_read_section
#print axioms a_required_old_read_extent_missing_from_custody_prevents_open
#print axioms an_exact_checkpoint_restores_the_read_book_and_the_journal_together
#print axioms the_same_checkpoint_bytes_cannot_recover_a_different_result_or_hold
#print axioms a_source_refuses_a_seal_with_an_unbound_read_attachment
#print axioms activation_uses_the_retained_attachment_from_exactly_the_sealed_cut
#print axioms an_exact_mounted_read_image_can_activate_without_source_recontact
#print axioms the_installed_target_reissues_the_original_result_with_its_retained_custody
#print axioms only_the_current_owner_can_acknowledge_a_logical_close_during_handoff

end JointReadRecovery
