import SelectiveCheckpoint

set_option warningAsError true

namespace GrantReadPolicy

open ChosenReplay (Lineage)
open ReadInvocationFloor (grant Advances)
open RetainedDelivery (Reply)

variable {bytes slots capacity limit : Nat} {Payload Ticket Voter : Type}

structure Binding where
  lineage : Lineage
  writer : Option Kernel.Writer
  horizon : Nat
  deriving DecidableEq

def Matches (authenticated expected : Binding) : Prop :=
  authenticated = expected

theorem agreement_binds_the_exact_window_policy (authenticated expected : Binding)
    (checked : Matches authenticated expected) : authenticated = expected := by
  exact checked

structure Proposal (Ticket : Type) where
  horizon : Nat
  evidence : Ticket

structure Rules (bytes slots capacity limit : Nat) (Payload Ticket : Type) where
  ordered : RetainedDelivery.Rules bytes slots capacity limit Payload Ticket
  formatMax : Nat
  authorized : Ticket → Option Binding

structure Image (slots capacity limit : Nat) (Payload : Type) where
  horizon : Nat
  state : SelectiveOrderedRecovery.Image horizon slots capacity limit Payload

def writer (image : Image slots capacity limit Payload) : Option Kernel.Writer :=
  grant (SelectiveOrderedRecovery.authority image.state)

def binding (lineage : Lineage) (image : Image slots capacity limit Payload) : Binding :=
  ⟨lineage, writer image, image.horizon⟩

def Authorized (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (successor : Kernel.Writer) (proposal : Proposal Ticket) : Prop :=
  0 < proposal.horizon ∧ proposal.horizon ≤ rules.formatMax ∧
    ∃ signed, rules.authorized proposal.evidence = some signed ∧
      Matches signed ⟨lineage, some successor, proposal.horizon⟩

structure Command (slots capacity limit : Nat) (Payload Ticket : Type) where
  effect : RetainedDelivery.Command slots capacity limit Payload Ticket
  proposal : Option (Proposal Ticket)

noncomputable def adopt (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (applied : SelectiveOrderedRecovery.Image before.horizon slots capacity limit Payload)
    (proposal : Option (Proposal Ticket)) : Option (Image slots capacity limit Payload) := by
  classical
  let current := grant (SelectiveOrderedRecovery.authority applied)
  exact match proposal with
  | none => some ⟨before.horizon, applied⟩
  | some offered =>
    match current with
    | none => none
    | some successor =>
      if writer before ≠ some successor ∧ Authorized rules lineage successor offered then
        some ⟨offered.horizon, SelectiveOrderedRecovery.attach applied.body (SelectiveReadWindow.initial offered.horizon)⟩
      else none

noncomputable def decide (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    Image slots capacity limit Payload × Reply Payload capacity :=
  let applied := SelectiveOrderedRecovery.decide rules.ordered lineage before.state command.effect
  match adopt rules lineage before applied.1 command.proposal with
  | some next => (next, applied.2)
  | none => (⟨before.horizon, SelectiveOrderedRecovery.advance before.state⟩, .refused)

theorem work_and_writer_recovery_inherit_the_existing_width_without_an_offer
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (effect : RetainedDelivery.Command slots capacity limit Payload Ticket) :
    decide rules lineage before ⟨effect, none⟩ =
      (⟨before.horizon, (SelectiveOrderedRecovery.decide rules.ordered lineage before.state effect).1⟩,
        (SelectiveOrderedRecovery.decide rules.ordered lineage before.state effect).2) := by
  rfl

theorem an_offer_cannot_change_the_policy_inside_the_same_grant
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (effect : RetainedDelivery.Command slots capacity limit Payload Ticket)
    (offered : Proposal Ticket) (same : writer before = grant (SelectiveOrderedRecovery.authority
      (SelectiveOrderedRecovery.decide rules.ordered lineage before.state effect).1)) :
    decide rules lineage before ⟨effect, some offered⟩ =
      (⟨before.horizon, SelectiveOrderedRecovery.advance before.state⟩, .refused) := by
  cases current : grant (SelectiveOrderedRecovery.authority
    (SelectiveOrderedRecovery.decide rules.ordered lineage before.state effect).1) with
  | none => simp [decide, adopt, current]
  | some writer => simp [decide, adopt, current, same]

theorem a_matching_offer_changes_width_only_with_the_real_new_grant
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (effect : RetainedDelivery.Command slots capacity limit Payload Ticket)
    (offered : Proposal Ticket) (successor : Kernel.Writer)
    (installed : grant (SelectiveOrderedRecovery.authority
      (SelectiveOrderedRecovery.decide rules.ordered lineage before.state effect).1) = some successor)
    (new : writer before ≠ some successor) (authorized : Authorized rules lineage successor offered) :
    let applied := SelectiveOrderedRecovery.decide rules.ordered lineage before.state effect
    decide rules lineage before ⟨effect, some offered⟩ =
      (⟨offered.horizon, SelectiveOrderedRecovery.attach applied.1.body (SelectiveReadWindow.initial offered.horizon)⟩,
        applied.2) := by
  simp [decide, adopt, installed, new, authorized]

theorem a_changed_width_requires_its_exact_authenticated_successor
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket)
    (applied : (decide rules lineage before command).1 = after)
    (different : before.horizon ≠ after.horizon) :
    ∃ successor offered signed, writer after = some successor ∧ writer before ≠ some successor ∧
      command.proposal = some offered ∧ rules.authorized offered.evidence = some signed ∧
      signed = binding lineage after ∧ 0 < after.horizon ∧ after.horizon ≤ rules.formatMax := by
  unfold decide at applied
  dsimp only at applied
  split at applied
  · next candidate matched =>
    cases applied
    unfold adopt at matched
    cases offered : command.proposal with
    | none =>
      rw [offered] at matched
      cases matched
      exact False.elim (different rfl)
    | some proposal =>
      simp only [offered] at matched
      cases selected : grant (SelectiveOrderedRecovery.authority
        (SelectiveOrderedRecovery.decide rules.ordered lineage before.state command.effect).1) with
      | none => simp [selected] at matched
      | some chosen =>
        simp only [selected] at matched
        split at matched
        · next allowed =>
          cases matched
          obtain ⟨positive, fits, signed, proof, binds⟩ := allowed.2
          have chosenWriter : writer
              (⟨proposal.horizon, SelectiveOrderedRecovery.attach
                (SelectiveOrderedRecovery.decide rules.ordered lineage before.state command.effect).1.body
                (SelectiveReadWindow.initial proposal.horizon)⟩ : Image slots capacity limit Payload) = some chosen :=
            selected
          refine ⟨chosen, proposal, signed, chosenWriter, allowed.1, rfl, proof, ?_, positive, fits⟩
          exact (agreement_binds_the_exact_window_policy _ _ binds).trans (by
            simp only [binding, chosenWriter])
        · cases matched
  · cases applied
    exact False.elim (different rfl)

theorem bare_packed_bytes_can_alias_distinct_policy_widths :
    SelectiveCheckpoint.encode 1 (SelectiveReadWindow.initial 1) =
      SelectiveCheckpoint.encode 1 (SelectiveReadWindow.initial 2) := by rfl

theorem an_unqualified_checkpoint_can_open_under_both_widths :
    let raw := SelectiveCheckpoint.encode 1 (SelectiveReadWindow.initial 1)
    SelectiveCheckpoint.decode 1 1 raw = some (SelectiveReadWindow.initial 1) ∧
      SelectiveCheckpoint.decode 1 2 raw = some (SelectiveReadWindow.initial 2) := by
  intro raw
  refine ⟨SelectiveCheckpoint.decode_the_exact_packed_window 1 _ (by decide), ?_⟩
  change SelectiveCheckpoint.decode 1 2 (SelectiveCheckpoint.encode 1 (SelectiveReadWindow.initial 1)) =
    some (SelectiveReadWindow.initial 2)
  rw [bare_packed_bytes_can_alias_distinct_policy_widths]
  exact SelectiveCheckpoint.decode_the_exact_packed_window 1 _ (by decide)

def Preserves (before after : Image slots capacity limit Payload) : Prop :=
  (writer before = writer after ∧ before.horizon = after.horizon ∧
    ∀ nonce, SelectiveReadWindow.Spent before.state.window nonce → SelectiveReadWindow.Spent after.state.window nonce) ∨
  Advances (writer before) (writer after)

theorem every_decision_keeps_the_same_policy_or_advances_the_grant
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    Preserves before (decide rules lineage before command).1 := by
  let applied := (SelectiveOrderedRecovery.decide rules.ordered lineage before.state command.effect).1
  have original := SelectiveOrderedRecovery.every_applied_command_preserves_spent_invocations
    rules.ordered lineage before.state command.effect
  have keepOriginal : Preserves before ⟨before.horizon, applied⟩ := by
    rcases original with ⟨same, held⟩ | newer
    · exact .inl ⟨same, rfl, held⟩
    · exact .inr newer
  have refused : Preserves before ⟨before.horizon, SelectiveOrderedRecovery.advance before.state⟩ :=
    .inl ⟨rfl, rfl, fun _ bit => bit⟩
  cases selected : adopt rules lineage before applied command.proposal with
  | none =>
    have complete : (decide rules lineage before command).1 =
        ⟨before.horizon, SelectiveOrderedRecovery.advance before.state⟩ := by
      have adopted : adopt rules lineage before
          (SelectiveOrderedRecovery.decide rules.ordered lineage before.state command.effect).1 command.proposal = none :=
        selected
      simp [decide, adopted]
    exact complete.symm ▸ refused
  | some after =>
    have complete : (decide rules lineage before command).1 = after := by
      have adopted : adopt rules lineage before
          (SelectiveOrderedRecovery.decide rules.ordered lineage before.state command.effect).1 command.proposal = some after :=
        selected
      simp [decide, adopted]
    rw [complete]
    unfold adopt at selected
    cases offered : command.proposal with
    | none =>
      rw [offered] at selected
      cases selected
      exact keepOriginal
    | some proposal =>
      simp only [offered] at selected
      cases current : grant (SelectiveOrderedRecovery.authority applied) with
      | none => simp [current] at selected
      | some successor =>
        simp only [current] at selected
        split at selected
        · next present =>
          cases selected
          rcases original with ⟨equal, _⟩ | newer
          · exact False.elim (present.1 (equal.trans current))
          · exact .inr newer
        · cases selected

theorem every_decision_preserves_spent_exact_invocations
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket)
    (old : Kernel.Writer) (nonce : Nat) (spent : SelectiveOrderedRecovery.Spent before.state old nonce) :
    SelectiveOrderedRecovery.Spent (decide rules lineage before command).1.state old nonce := by
  rcases every_decision_keeps_the_same_policy_or_advances_the_grant rules lineage before command with
    ⟨same, _, marked⟩ | newer
  · rcases spent with ⟨equal, bit⟩ | older
    · exact .inl ⟨same.symm.trans equal, marked nonce bit⟩
    · refine .inr ?_
      change Advances (some old) (writer (decide rules lineage before command).1)
      rw [← same]
      exact older
  · rcases spent with ⟨previous, _⟩ | older
    · exact .inr (previous ▸ newer)
    · exact .inr (ReadInvocationFloor.advances_trans older newer)

structure Frame (slots capacity limit : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots capacity limit Payload Ticket

noncomputable def step (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (frame : Frame slots capacity limit Payload Ticket) :
    Option (Image slots capacity limit Payload) := by
  classical
  exact if frame.lineage = lineage ∧ frame.position = RetainedDelivery.position before.state.body + 1 then
    some (decide rules lineage before frame.command).1 else none

noncomputable def replay (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket)) :
    Option (Image slots capacity limit Payload) :=
  frames.foldlM (step rules lineage) origin

private theorem compose_preservation {first middle after : Image slots capacity limit Payload}
    (early : Preserves first middle) (late : Preserves middle after) : Preserves first after := by
  rcases early with ⟨same, width, held⟩ | newer <;> rcases late with ⟨equal, widthLater, heldLater⟩ | latest
  · exact .inl ⟨same.trans equal, width.trans widthLater, fun n mark => heldLater n (held n mark)⟩
  · exact .inr (same.symm ▸ latest)
  · exact .inr (equal ▸ newer)
  · exact .inr (ReadInvocationFloor.advances_trans newer latest)

theorem no_exact_grant_can_reappear_with_a_different_policy_during_replay
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket))
    (replayed : replay rules lineage before frames = some after) : Preserves before after := by
  induction frames generalizing before with
  | nil =>
    have exactImage : before = after := by simpa [replay] using replayed
    subst after
    exact .inl ⟨rfl, rfl, fun _ bit => bit⟩
  | cons frame tail later =>
    cases applied : step rules lineage before frame with
    | none => simp [replay, applied] at replayed
    | some next =>
      have first : Preserves before next := by
        unfold step at applied
        split at applied
        · cases applied
          exact every_decision_keeps_the_same_policy_or_advances_the_grant rules lineage before frame.command
        · cases applied
      exact compose_preservation first (later next (by simpa [replay, applied] using replayed))

theorem the_same_grant_has_the_same_width_after_any_replay
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket))
    (replayed : replay rules lineage before frames = some after) (same : writer before = writer after) :
    before.horizon = after.horizon := by
  rcases no_exact_grant_can_reappear_with_a_different_policy_during_replay rules lineage before after frames replayed
    with ⟨_, width, _⟩ | newer
  · exact width
  · rw [← same] at newer
    cases known : writer before <;> simp [known, ReadInvocationFloor.Advances, ReadInvocationFloor.Newer] at newer

structure Base (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket)) where
  cut : Nat
  image : Image slots capacity limit Payload
  within : cut ≤ frames.length
  certified : replay rules lineage origin (frames.take cut) = some image

noncomputable def reopen (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity limit Payload} {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket)}
    (_chosen : PrefixAgreement.Chosen ledger ballot frames) (base : Base rules lineage origin frames)
    (supplied : Binding) (media : List (Frame slots capacity limit Payload Ticket)) :
    Option (Image slots capacity limit Payload) := by
  classical
  exact if Matches supplied (binding lineage base.image) ∧ frames.drop base.cut <+: media then
    replay rules lineage base.image (frames.drop base.cut)
  else none

theorem a_certified_old_selector_applies_the_new_grant_policy_from_its_suffix
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity limit Payload} {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket)}
    (chosen : PrefixAgreement.Chosen ledger ballot frames) (base : Base rules lineage origin frames)
    (read : Binding) (media : List (Frame slots capacity limit Payload Ticket))
    (after : Image slots capacity limit Payload) (opened : reopen rules lineage chosen base read media = some after) :
    read = binding lineage base.image ∧ replay rules lineage origin frames = some after := by
  unfold reopen at opened
  split at opened
  · next valid =>
    refine ⟨agreement_binds_the_exact_window_policy _ _ valid.1, ?_⟩
    rw [← List.take_append_drop base.cut frames]
    have exactPrefix := base.certified
    simp only [replay] at exactPrefix opened ⊢
    rw [List.foldlM_append, exactPrefix]
    exact opened
  · cases opened

open EnvelopeCodec (Bytes Field readWord)

structure Control (bytes slots capacity limit : Nat) (Payload : Type) where
  body : SelectiveCheckpoint.Control bytes slots capacity limit Payload
  policy : Binding

abbrev Catalog (bytes slots capacity limit : Nat) (Payload : Type) :=
  EnvelopeRecovery.Catalog bytes (Control bytes slots capacity limit Payload) (FundedAppend.Source slots Payload)

def project (catalog : Catalog bytes slots capacity limit Payload) :
    SelectiveCheckpoint.Catalog bytes slots capacity limit Payload :=
  ⟨fun name => (catalog.control name).map Control.body, catalog.data, catalog.manifests, catalog.retained⟩

def CertifiedAnchor (lineage : Lineage) (base : Image slots capacity limit Payload)
    (anchor : EnvelopeRecovery.Anchor bytes) (declared : Binding) : Prop :=
  Matches declared (binding lineage base) ∧
    readWord anchor.position.val = RetainedDelivery.position base.state.body

noncomputable def openHistorical (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity limit Payload} {frames : List (Frame slots capacity limit Payload Ticket)}
    (base : Base rules lineage origin frames) (catalog : Catalog bytes slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor bytes) (coreNeeds : Field bytes → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field bytes → Prop)
    (deliveryNeeds : DeliveryBook.Entry capacity → Field bytes → Prop) (wire : Bytes) :
    Option (SelectiveOrderedRecovery.Image base.image.horizon slots capacity limit Payload) := by
  classical
  exact do
    let (_, contents) ← EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire
    if CertifiedAnchor lineage base.image anchor contents.control.policy ∧
        0 < base.image.horizon ∧ base.image.horizon ≤ rules.formatMax then
      let restored ← SelectiveCheckpoint.openCheckpoint rules.ordered (project catalog) authenticate anchor
        coreNeeds readNeeds deliveryNeeds wire
      if grant (SelectiveOrderedRecovery.authority restored) = writer base.image then some restored else none
    else none

theorem a_historical_open_authenticates_the_exact_grant_and_width_at_its_cut
    (rules : Rules bytes slots capacity limit Payload Ticket) (lineage : Lineage)
    {origin : Image slots capacity limit Payload} {frames : List (Frame slots capacity limit Payload Ticket)}
    (base : Base rules lineage origin frames) (catalog : Catalog bytes slots capacity limit Payload)
    (authenticate : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor bytes) (coreNeeds : Field bytes → Prop)
    (readNeeds : SnapshotAdmission.Basis → Field bytes → Prop)
    (deliveryNeeds : DeliveryBook.Entry capacity → Field bytes → Prop) (wire : Bytes)
    (restored : SelectiveOrderedRecovery.Image base.image.horizon slots capacity limit Payload)
    (opened : openHistorical rules lineage base catalog authenticate anchor coreNeeds readNeeds deliveryNeeds wire =
        some restored) :
    ∃ header contents,
      EnvelopeRecovery.Opened catalog authenticate anchor coreNeeds wire header contents ∧
      contents.control.policy = binding lineage base.image ∧
      readWord anchor.position.val = RetainedDelivery.position base.image.state.body ∧
      grant (SelectiveOrderedRecovery.authority restored) = writer base.image ∧
      0 < base.image.horizon ∧ base.image.horizon ≤ rules.formatMax := by
  cases named : EnvelopeRecovery.openChecked catalog authenticate anchor coreNeeds wire with
  | none => simp [openHistorical, named] at opened
  | some result =>
    obtain ⟨header, contents⟩ := result
    by_cases ready : CertifiedAnchor lineage base.image anchor contents.control.policy ∧
        0 < base.image.horizon ∧ base.image.horizon ≤ rules.formatMax
    · cases decoded : SelectiveCheckpoint.openCheckpoint (horizon := base.image.horizon) rules.ordered
          (project catalog) authenticate anchor coreNeeds readNeeds deliveryNeeds wire with
      | none => simp [openHistorical, named, decoded] at opened
      | some image =>
        by_cases same : grant (SelectiveOrderedRecovery.authority image) = writer base.image
        · have aligned : image = restored := by
            simpa [openHistorical, named, ready, decoded, same] using opened
          exact ⟨header, contents, EnvelopeRecovery.a_successful_open_has_all_authentication_and_custody_checks named,
            agreement_binds_the_exact_window_policy _ _ ready.1.1, ready.1.2, aligned ▸ same, ready.2.1, ready.2.2⟩
        · simp [openHistorical, named, ready, decoded, same] at opened
    · simp [openHistorical, named, ready] at opened

#print axioms agreement_binds_the_exact_window_policy
#print axioms work_and_writer_recovery_inherit_the_existing_width_without_an_offer
#print axioms an_offer_cannot_change_the_policy_inside_the_same_grant
#print axioms a_matching_offer_changes_width_only_with_the_real_new_grant
#print axioms a_changed_width_requires_its_exact_authenticated_successor
#print axioms bare_packed_bytes_can_alias_distinct_policy_widths
#print axioms an_unqualified_checkpoint_can_open_under_both_widths
#print axioms every_decision_keeps_the_same_policy_or_advances_the_grant
#print axioms every_decision_preserves_spent_exact_invocations
#print axioms no_exact_grant_can_reappear_with_a_different_policy_during_replay
#print axioms the_same_grant_has_the_same_width_after_any_replay
#print axioms a_certified_old_selector_applies_the_new_grant_policy_from_its_suffix
#print axioms a_historical_open_authenticates_the_exact_grant_and_width_at_its_cut

end GrantReadPolicy
