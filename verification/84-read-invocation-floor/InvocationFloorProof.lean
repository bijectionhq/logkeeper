import OrderedReadReplay

set_option warningAsError true

namespace InvocationFloorProof

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Barrier)
open OrderedReadReplay (Image Command Frame Rules Cut Base authority journalAuthority decide advance step replay reopen)
open RecoverableRead (Permit)
open ReadInvocationFloor (Fresh Spent Preserves)

variable {width slots capacity : Nat} {Payload Ticket Voter : Type}

theorem exact_unordered_deduplication_distinguishes_every_spent_subset
    {Identity Stored : Type} (store : (Identity → Bool) → Stored)
    (allows : Stored → Identity → Bool)
    (exactly : ∀ used key, allows (store used) key = Bool.not (used key)) :
    Function.Injective store := by
  intro first second equal
  funext key
  have sameBit : Bool.not (first key) = Bool.not (second key) := by
    rw [← exactly first key, ← exactly second key, equal]
  cases firstBit : first key <;> cases secondBit : second key <;> simp_all

def WellSealed (source : Kernel.Authority) : Prop :=
  ∀ target writer, source = .sealed target writer → writer.placement.generation < target.generation

theorem ordinary_kernel_writer_transitions_allow_the_floor_to_be_carried
    {limits : Kernel.Limits} {before after : Kernel.State Payload}
    (sound : WellSealed before.authority) (step : Kernel.Step limits before after) :
    ReadInvocationFloor.CanCarry before.authority after.authority ∧ WellSealed after.authority := by
  cases step
  case withdrawWriter current =>
    rw [current]
    exact ⟨Or.inl rfl, by simp [WellSealed]⟩
  case fenceWriter new authorized placement epoch =>
    rename_i prior
    have original : ReadInvocationFloor.grant before.authority = some prior := by
      rcases authorized with active | vacant
      · simp [active, ReadInvocationFloor.grant]
      · simp [vacant, ReadInvocationFloor.grant]
    refine ⟨?_, by simp [WellSealed]⟩
    apply Or.inr
    rw [original]
    exact Or.inr ⟨placement.symm, epoch⟩
  case freeze authorized generation _ =>
    rw [authorized]
    refine ⟨Or.inl rfl, ?_⟩
    intro target writer same
    cases same
    exact generation
  case activate _ sealed _ =>
    refine ⟨Or.inr ?_, by simp [WellSealed]⟩
    rw [sealed]
    exact Or.inl (sound _ _ sealed)
  case retire authorized =>
    refine ⟨Or.inr ?_, by simp [WellSealed]⟩
    rcases authorized with active | vacant
    · simp [active, ReadInvocationFloor.grant, ReadInvocationFloor.Advances]
    · simp [vacant, ReadInvocationFloor.grant, ReadInvocationFloor.Advances]
  all_goals exact ⟨Or.inl rfl, sound⟩

private theorem a_read_marker_leaves_its_grant
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (call : Invocation) (exact : call.lineage = lineage)
    (active : authority before = .active call.writer) :
    journalAuthority (JointSource.decide rules.journal lineage before.journal
      (AppliedBarrierReceipt.readCommand call)).1 = authority before := by
  rw [← exact]
  rw [AppliedBarrierReceipt.readCommand,
    RTDBFailover.the_joint_marker_returns_the_current_cut_and_spends_no_append_credit rules.journal before.journal call active]
  rfl

private def FencePreserved (before after : Image slots capacity Payload) : Prop :=
  Preserves (authority before) (authority after) before.readThrough after.readThrough

private theorem every_decision_preserves_the_invocation_fence
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (command : Command slots capacity Payload Ticket) :
    FencePreserved before (decide rules lineage before command).1 := by
  have refused : FencePreserved before (advance before) :=
    Or.inl ⟨rfl, Nat.le_refl _⟩
  cases command with
  | journal effect =>
      simp only [OrderedReadReplay.decide]
      split
      · cases next : rules.nextView lineage before (JointSource.decide rules.journal lineage before.journal effect).1 effect with
        | none => simpa [next] using refused
        | some view =>
            dsimp only
            split
            · next checked =>
                exact ReadInvocationFloor.a_carried_floor_preserves_consumption _ _ _ checked.2.2
            · exact refused
      · exact refused
  | admit call slot evidence =>
      simp only [OrderedReadReplay.decide]
      split
      · next checked =>
          have fresh := checked.2.2.2.2
          refine Or.inl ⟨(a_read_marker_leaves_its_grant rules lineage before call checked.1 fresh.1 ▸ rfl), ?_⟩
          change before.readThrough ≤ call.nonce
          have next := fresh.2.1
          omega
      · exact refused
  | close permit evidence =>
      simp only [OrderedReadReplay.decide]
      split
      · cases JointReadRecovery.orderClose (authority before) rules.snapshot before.reads permit <;> exact refused
      · exact refused
  | abandon call evidence =>
      simp only [OrderedReadReplay.decide]
      split
      · next checked =>
          refine Or.inl ⟨rfl, ?_⟩
          change before.readThrough ≤ call.nonce
          have next := checked.2.2.2.1
          omega
      · exact refused
  | deliver _ _ => exact refused

theorem every_ordered_decision_uses_the_same_or_a_newer_grant
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (command : Command slots capacity Payload Ticket) :
    ReadInvocationFloor.CanCarry (authority before) (authority (decide rules lineage before command).1) := by
  rcases every_decision_preserves_the_invocation_fence rules lineage before command with ⟨same, _⟩ | later
  · exact .inl same
  · exact .inr later

theorem accepting_the_exact_call_consumes_its_nonce_with_the_read
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity Payload) (call : Invocation) (slot : Fin capacity)
    (proof : Ticket) (permit : Permit capacity) (reply : Barrier)
    (admitted : decide rules lineage before (.admit call slot proof) = (after, .admitted permit reply)) :
    after.readThrough = call.nonce ∧ Spent (authority after) after.readThrough call.writer call.nonce := by
  simp only [OrderedReadReplay.decide] at admitted
  split at admitted
  · next checked =>
      cases admitted
      have fresh := checked.2.2.2.2
      refine ⟨rfl, ?_⟩
      change Spent (journalAuthority (JointSource.decide rules.journal lineage before.journal
        (AppliedBarrierReceipt.readCommand call)).1) call.nonce call.writer call.nonce
      rw [a_read_marker_leaves_its_grant rules lineage before call checked.1 fresh.1]
      exact ReadInvocationFloor.after_consumption_the_exact_invocation_is_spent fresh
  · simp at admitted

theorem a_spent_invocation_cannot_admit_again_even_with_an_empty_result_slot
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (call : Invocation) (slot : Fin capacity)
    (proof : Ticket) (spent : Spent (authority before) before.readThrough call.writer call.nonce) :
    decide rules lineage before (.admit call slot proof) = (advance before, .refused) := by
  have refused := ReadInvocationFloor.a_spent_invocation_is_never_fresh (width := width) spent
  simp [OrderedReadReplay.decide, refused]

theorem a_later_nonce_cannot_skip_a_pending_nonce
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (call : Invocation) (slot : Fin capacity)
    (proof : Ticket) (later : before.readThrough + 1 < call.nonce) :
    decide rules lineage before (.admit call slot proof) = (advance before, .refused) := by
  have blocked : ¬ Fresh width (authority before) before.readThrough call.writer call.nonce := by
    intro fresh
    exact (Nat.not_le_of_lt later) (ReadInvocationFloor.a_fresh_invocation_cannot_pass_the_next_nonce fresh)
  simp [OrderedReadReplay.decide, blocked]

theorem an_authenticated_abandon_consumes_only_the_next_nonce_and_keeps_all_holds
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (call : Invocation) (proof : Ticket)
    (same : call.lineage = lineage) (authorized : rules.abandon call proof)
    (fresh : Fresh width (authority before) before.readThrough call.writer call.nonce) :
    let after := {advance before with readThrough := call.nonce}
    decide rules lineage before (.abandon call proof) = (after, .abandoned) ∧
      after.reads = before.reads ∧ Spent (authority after) after.readThrough call.writer call.nonce := by
  refine ⟨by simp [OrderedReadReplay.decide, same, authorized, fresh], rfl, ?_⟩
  exact ReadInvocationFloor.after_consumption_the_exact_invocation_is_spent fresh

theorem replay_preserves_an_already_consumed_invocation
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (frames : List (Frame slots capacity Payload Ticket)) (before after : Image slots capacity Payload)
    (writer : Kernel.Writer) (nonce : Nat) (spent : Spent (authority before) before.readThrough writer nonce)
    (recovered : replay rules lineage before frames = some after) :
    Spent (authority after) after.readThrough writer nonce := by
  induction frames generalizing before with
  | nil =>
      have same : before = after := by simpa [replay] using recovered
      exact same ▸ spent
  | cons frame rest follow =>
      by_cases eligible : OrderedReadReplay.Eligible lineage before frame
      · let next := (decide rules lineage before frame.command).1
        have applied : step rules lineage before frame = some next := by simp [step, eligible, next]
        have carried := ReadInvocationFloor.spent_survives_monotone_scope_and_floor spent
          (every_decision_preserves_the_invocation_fence rules lineage before frame.command)
        have restored : replay rules lineage next rest = some after := by simpa [replay, applied] using recovered
        exact follow next carried restored
      · have blocked : step rules lineage before frame = none := by simp [step, eligible]
        simp [replay, blocked] at recovered

theorem reopening_from_either_base_preserves_the_consumption_in_a_certified_prefix
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity Payload Ticket)}
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity Payload} (cut : Cut ledger) (earlier selected : Base rules lineage origin cut.frames)
    (media : List (Frame slots capacity Payload Ticket)) (after : Image slots capacity Payload)
    (writer : Kernel.Writer) (nonce : Nat) (spent : Spent (authority earlier.image) earlier.image.readThrough writer nonce)
    (opened : reopen rules lineage cut selected media = some after) :
    Spent (authority after) after.readThrough writer nonce := by
  have whole := OrderedReadReplay.any_successful_reopen_is_exact rules lineage cut selected media opened
  have suffix := OrderedReadReplay.replay_after_a_certified_combined_base rules lineage _ (cut.frames.drop earlier.cut) earlier.certified
  rw [List.take_append_drop, whole] at suffix
  exact replay_preserves_an_already_consumed_invocation rules lineage _ _ _ writer nonce spent suffix.symm

theorem an_exhausted_namespace_refuses_instead_of_wrapping
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity Payload) (call : Invocation) (slot : Fin capacity) (proof : Ticket)
    (endOfSpace : EnvelopeCodec.wordLimit width ≤ before.readThrough + 1) :
    decide rules lineage before (.admit call slot proof) = (advance before, .refused) ∧
    decide rules lineage before (.abandon call proof) = (advance before, .refused) := by
  have exhausted := ReadInvocationFloor.at_width_exhaustion_no_nonce_can_be_admitted
    (authority before) call.writer call.nonce endOfSpace
  constructor <;> simp [OrderedReadReplay.decide, exhausted]

open EnvelopeCodec (Bytes Field wordBytes readWord wordLimit)

def decodeFloor (width : Nat) (wire : Bytes) : Option Nat :=
  if wire.length = width then some (readWord wire) else none

private theorem readWord_fits (wire : Bytes) : readWord wire < wordLimit wire.length := by
  induction wire with
  | nil => decide
  | cons byte tail fits =>
      simp only [readWord, List.length_cons, wordLimit, Nat.pow_succ] at *
      have small := byte.toNat_lt
      omega

theorem the_floor_has_one_canonical_bounded_word (width floor : Nat) (fits : floor < wordLimit width) :
    (wordBytes width floor).length = width ∧ decodeFloor width (wordBytes width floor) = some floor ∧
      ∀ wire, decodeFloor width wire = some floor → wordBytes width floor = wire := by
  refine ⟨EnvelopeCodec.wordBytes_length width floor, ?_, ?_⟩
  · simp [decodeFloor, EnvelopeCodec.wordBytes_length, EnvelopeCodec.fixed_width_words_roundtrip fits]
  · intro wire parsed
    by_cases size : wire.length = width
    · have exact := EnvelopeCodec.wordBytes_after_readWord wire
      have decoded : readWord wire = floor := by simpa [decodeFloor, size] using parsed
      simpa [size, decoded] using exact
    · simp [decodeFloor, size] at parsed

structure CheckpointControl (slots capacity : Nat) (Payload : Type) where
  body : JointReadRecovery.Control capacity slots Payload
  floor : Bytes

noncomputable def openCheckpoint (rules : Rules width slots capacity Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (CheckpointControl slots capacity Payload) (FundedAppend.Source slots Payload))
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) : Option (Image slots capacity Payload) := by
  classical
  exact do
    let (contents, reads) ← JointReadRecovery.openNamedReads catalog (fun control => control.body.protectedReads)
      authenticate anchor coreNeeds readNeeds wire
    let journal ← RankedJointReplay.imageOf rules.journal contents.control.body.source contents.data
    let floor ← decodeFloor width contents.control.floor
    if journal.source.source.position = readWord anchor.position.val ∧ OrderedReadReplay.Aligned reads.view journal then
      some ⟨journal, reads, floor⟩
    else none

theorem a_named_checkpoint_opens_its_combined_journal_read_book_and_exact_floor
    (rules : Rules width slots capacity Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (CheckpointControl slots capacity Payload) (FundedAppend.Source slots Payload))
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (header : EnvelopeCodec.Envelope width)
    (contents : EnvelopeRecovery.Contents width (CheckpointControl slots capacity Payload) (FundedAppend.Source slots Payload))
    (image : Image slots capacity Payload) (historical : Barrier → Prop)
    (sound : RecoverableRead.SoundFor width rules.snapshot historical image.reads) (positive : 0 < width)
    (opened : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire = some (header, contents))
    (exactRead : contents.control.body.protectedReads = JointReadRecovery.encodeSection width image.reads)
    (covered : ∀ object, JointReadRecovery.Needs readNeeds image.reads object → object ∈ contents.dependencies)
    (exactJournal : RankedJointReplay.imageOf rules.journal contents.control.body.source contents.data = some image.journal)
    (exactFloor : contents.control.floor = wordBytes width image.readThrough) (fits : image.readThrough < wordLimit width)
    (orderedCut : OrderedReadReplay.position image = readWord anchor.position.val)
    (aligned : OrderedReadReplay.Aligned image.reads.view image.journal) :
    openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds wire = some image := by
  have joint := JointReadRecovery.the_authenticated_named_control_opens_its_exact_read_section
    catalog (fun control => control.body.protectedReads) authenticate anchor coreNeeds readNeeds wire header contents
    image.reads sound positive opened exactRead covered
  have atCut : image.journal.source.source.position = readWord anchor.position.val := orderedCut
  simp [openCheckpoint, joint, exactJournal, atCut, aligned, exactFloor, (the_floor_has_one_canonical_bounded_word width _ fits).2.1]

theorem recovery_cannot_borrow_the_floor_from_another_control_image
    (rules : Rules width slots capacity Payload Ticket)
    (catalog : EnvelopeRecovery.Catalog width (CheckpointControl slots capacity Payload) (FundedAppend.Source slots Payload))
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor width)
    (coreNeeds : Field width → Prop) (readNeeds : SnapshotAdmission.Basis → Field width → Prop)
    (wire : Bytes) (image : Image slots capacity Payload)
    (opened : openCheckpoint rules catalog authenticate anchor coreNeeds readNeeds wire = some image) :
    ∃ header contents,
      EnvelopeRecovery.Opened catalog authenticate anchor coreNeeds wire header contents ∧
      contents.control.floor = wordBytes width image.readThrough ∧ image.readThrough < wordLimit width := by
  cases found : JointReadRecovery.openNamedReads catalog (fun control => control.body.protectedReads)
      authenticate anchor coreNeeds readNeeds wire with
  | none => simp [openCheckpoint, found] at opened
  | some control =>
      rcases control with ⟨contents, reads⟩
      cases journal : RankedJointReplay.imageOf rules.journal contents.control.body.source contents.data with
      | none => simp [openCheckpoint, found, journal] at opened
      | some source =>
          by_cases size : contents.control.floor.length = width
          · have decoded : decodeFloor width contents.control.floor = some (readWord contents.control.floor) := by
              simp [decodeFloor, size]
            by_cases aligned : source.source.source.position = readWord anchor.position.val ∧
                OrderedReadReplay.Aligned reads.view source
            · have same : (⟨source, reads, readWord contents.control.floor⟩ : Image slots capacity Payload) = image := by
                simpa [openCheckpoint, found, journal, decoded, aligned] using opened
              subst image
              obtain ⟨⟨header, verified, _⟩, _⟩ :=
                JointReadRecovery.named_read_recovery_pins_all_original_dependencies catalog
                  (fun control => control.body.protectedReads) authenticate anchor coreNeeds readNeeds wire contents reads found
              exact ⟨header, contents, verified, by simpa [size] using (EnvelopeCodec.wordBytes_after_readWord contents.control.floor).symm,
                by simpa [size] using readWord_fits contents.control.floor⟩
            · simp [openCheckpoint, found, journal, decoded, aligned] at opened
          · simp [openCheckpoint, found, journal, decodeFloor, size] at opened

#print axioms exact_unordered_deduplication_distinguishes_every_spent_subset
#print axioms ordinary_kernel_writer_transitions_allow_the_floor_to_be_carried
#print axioms accepting_the_exact_call_consumes_its_nonce_with_the_read
#print axioms a_spent_invocation_cannot_admit_again_even_with_an_empty_result_slot
#print axioms a_later_nonce_cannot_skip_a_pending_nonce
#print axioms an_authenticated_abandon_consumes_only_the_next_nonce_and_keeps_all_holds
#print axioms reopening_from_either_base_preserves_the_consumption_in_a_certified_prefix
#print axioms an_exhausted_namespace_refuses_instead_of_wrapping
#print axioms the_floor_has_one_canonical_bounded_word
#print axioms a_named_checkpoint_opens_its_combined_journal_read_book_and_exact_floor
#print axioms recovery_cannot_borrow_the_floor_from_another_control_image

end InvocationFloorProof
