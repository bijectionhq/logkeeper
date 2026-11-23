import ActivationComposition
import ConfigurationClosure
import CopyFence

set_option warningAsError true

namespace CertifiedActivationReplay

open ActivationComposition (TargetCut State capture)
open IntentRetirement (CopyKey Store Evidence)
open PrefixAgreement (Chosen)

variable {Image Replica Voter : Type}

inductive Operation (Image : Type) where
  | acknowledge (id : Nat) (image : Image)
  | settle (key : CopyKey) (image : Image)

inductive Attachment (Image : Type) where
  | source (id : Nat) (image : Image)
  | fencedCopy (key : CopyKey) (image : Image) (receipt : CopyFence.Receipt)

structure Command (Image : Type) where
  operation : Operation Image
  attachment : Option (Attachment Image)

inductive Outcome where
  | applied
  | refused

abbrev OriginalReceipts (Image : Type) := CopyKey → Image → CopyFence.Receipt

def Required (original : OriginalReceipts Image) (operation : Operation Image) : Attachment Image :=
  match operation with
  | .acknowledge id image => .source id image
  | .settle key image => .fencedCopy key image (original key image)

def ExactAttachment (original : OriginalReceipts Image) (command : Command Image) : Prop :=
  command.attachment = some (Required original command.operation)

def CheckedAtIntake (original : OriginalReceipts Image) (state : State Image)
    (attachment : Option (Attachment Image)) : Prop :=
  match attachment with
  | none => True
  | some (.source id image) => state.store.recorded id = some image
  | some (.fencedCopy key image receipt) => receipt = original key image ∧ state.fences key image

noncomputable def apply (original : OriginalReceipts Image) (state : TargetCut Image)
    (command : Command Image) : TargetCut Image × Outcome := by
  classical
  exact if ExactAttachment original command then
    match command.operation with
    | .acknowledge id image =>
        if state.outcomes id = some image
        then ({state with outcomes := IntentRetirement.update state.outcomes id none}, .applied)
        else (state, .refused)
    | .settle key image =>
        if state.jobs key = some image
        then ({state with jobs := IntentRetirement.update state.jobs key none}, .applied)
        else (state, .refused)
  else (state, .refused)

theorem no_eligible_ordered_attachment_means_refusal
    (original : OriginalReceipts Image) (state : TargetCut Image) (command : Command Image)
    (missing : ¬ ExactAttachment original command) :
    apply original state command = (state, .refused) := by
  simp [apply, missing]

theorem a_foreign_custodian_receipt_cannot_discharge_the_copy
    (original : OriginalReceipts Image) (state : TargetCut Image) (key : CopyKey) (image : Image)
    (receipt : CopyFence.Receipt) (foreign : receipt ≠ original key image) :
    apply original state ⟨.settle key image, some (.fencedCopy key image receipt)⟩ = (state, .refused) := by
  apply no_eligible_ordered_attachment_means_refusal
  simp [ExactAttachment, Required, foreign]

def AuthenticFences (evidence : Evidence Image) (state : State Image) : Prop :=
  ∀ key image, state.fences key image → evidence.settledCopy key image

theorem activation_traces_preserve_authentic_fence_facts
    {evidence : Evidence Image} {first last : State Image}
    (authentic : AuthenticFences evidence first) (trace : ActivationComposition.Trace evidence first last) :
    AuthenticFences evidence last := by
  induction trace with
  | same => exact authentic
  | next _ step prior =>
      cases step with
      | providerFence key image _ proof =>
          intro observed expected found
          rcases found with ⟨sameKey, sameImage⟩ | earlier
          · exact sameKey.symm ▸ sameImage.symm ▸ proof
          · exact prior observed expected earlier
      | _ => exact prior

private theorem unchanged_copy_plans_need_no_receipt (state : State Image) (after : Store Image)
    (same : after.jobs = state.store.jobs) : ActivationComposition.CopyRemovalsCertified state after := by
  intro key image pending changed
  exact False.elim (changed (same.symm ▸ pending))

private theorem removing_just_the_certified_copy
    (state : State Image) (key : CopyKey) (image : Image)
    (planned : state.store.jobs key = some image) (fenced : state.fences key image) :
    ActivationComposition.CopyRemovalsCertified state
      {state.store with jobs := IntentRetirement.update state.store.jobs key none} := by
  intro observed binding pending changed
  by_cases matchesKey : observed = key
  · subst observed
    have same := Option.some.inj (planned.symm.trans pending)
    subst binding
    exact fenced
  · exact False.elim (changed (by simpa [IntentRetirement.update, matchesKey] using pending))

theorem an_ordered_evidence_command_refines_the_composed_reducer
    {evidence : Evidence Image} (original : OriginalReceipts Image) (state : State Image)
    (command : Command Image) (owner : Nat) (current : ActivationComposition.CanWrite state owner)
    (verified : CheckedAtIntake original state command.attachment) (fences : AuthenticFences evidence state) :
    ∃ after, ActivationComposition.Step evidence state after ∧
      capture after.store = (apply original (capture state.store) command).1 := by
  classical
  have refuses (decision : (apply original (capture state.store) command).1 = capture state.store) :
      ∃ after, ActivationComposition.Step evidence state after ∧
        capture after.store = (apply original (capture state.store) command).1 := by
    exact ⟨state, .target owner state.store current .restart rfl
      (unchanged_copy_plans_need_no_receipt state state.store rfl), decision.symm⟩
  by_cases matched : ExactAttachment original command
  · rcases command with ⟨operation, attachment⟩
    have exactAttachment : attachment = some (Required original operation) := matched
    subst attachment
    cases operation with
    | acknowledge id image =>
        by_cases retained : state.store.outcomes id = some image
        · let after := {state.store with outcomes := IntentRetirement.update state.store.outcomes id none}
          have recorded : state.store.recorded id = some image := verified
          have ordered : IntentRetirement.Step evidence state.store after := .acknowledge id image retained recorded
          exact ⟨{state with store := after},
            .target owner after current ordered rfl (unchanged_copy_plans_need_no_receipt state after rfl),
            by simp [apply, ExactAttachment, capture, retained, after]⟩
        · exact refuses (by simp [apply, ExactAttachment, capture, retained])
    | settle key image =>
        by_cases planned : state.store.jobs key = some image
        · let after := {state.store with jobs := IntentRetirement.update state.store.jobs key none}
          have checked : original key image = original key image ∧ state.fences key image := verified
          have validFence : state.fences key image := checked.2
          have ordered : IntentRetirement.Step evidence state.store after :=
            .settle key image planned (fences key image validFence)
          exact ⟨{state with store := after},
            .target owner after current ordered rfl (removing_just_the_certified_copy state key image planned validFence),
            by simp [apply, ExactAttachment, capture, planned, after]⟩
        · exact refuses (by simp [apply, ExactAttachment, capture, planned])
  · exact refuses (congrArg Prod.fst (no_eligible_ordered_attachment_means_refusal original _ command matched))

noncomputable def replay (original : OriginalReceipts Image) (state : TargetCut Image) :
    List (Command Image) → TargetCut Image × List Outcome
  | [] => (state, [])
  | command :: commands =>
      let first := apply original state command
      let more := replay original first.1 commands
      (more.1, first.2 :: more.2)

theorem replay_append (original : OriginalReceipts Image) (state : TargetCut Image)
    (first later : List (Command Image)) :
    replay original state (first ++ later) =
      let earlier := replay original state first
      let remaining := replay original earlier.1 later
      (remaining.1, earlier.2 ++ remaining.2) := by
  induction first generalizing state with
  | nil => simp [replay]
  | cons command commands prior =>
      simp only [List.cons_append, replay]
      rw [prior]

theorem a_historical_refusal_remains_at_its_position
    (original : OriginalReceipts Image) (state : TargetCut Image) (command : Command Image)
    (suffix : List (Command Image)) (missing : ¬ ExactAttachment original command) :
    (replay original state (command :: suffix)).2 =
      .refused :: (replay original state suffix).2 := by
  simp [replay, no_eligible_ordered_attachment_means_refusal original state command missing]

theorem chosen_outcomes_follow_any_exact_journal_extension
    (original : OriginalReceipts Image) (state : TargetCut Image) {first later : List (Command Image)}
    (inherited : first <+: later) : (replay original state first).2 <+: (replay original state later).2 := by
  rcases inherited with ⟨suffix, rfl⟩
  rw [replay_append]
  exact List.prefix_append _ _

private theorem an_ordered_command_cannot_recreate_a_discharged_copy
    (original : OriginalReceipts Image) (state : TargetCut Image) (command : Command Image)
    (key : CopyKey) (cleared : state.jobs key = none) : (apply original state command).1.jobs key = none := by
  classical
  by_cases matched : ExactAttachment original command
  · cases operation : command.operation with
    | acknowledge id image =>
        by_cases retained : state.outcomes id = some image <;>
          simpa [apply, matched, operation, retained] using cleared
    | settle other image =>
        by_cases retained : state.jobs other = some image
        · by_cases same : key = other
          · simp [apply, matched, operation, retained, IntentRetirement.update, same]
          · simpa [apply, matched, operation, retained, IntentRetirement.update, same] using cleared
        · simpa [apply, matched, operation, retained] using cleared
  · simpa [apply, matched] using cleared

theorem a_replayed_suffix_cannot_recreate_a_discharged_copy
    (original : OriginalReceipts Image) (initial : TargetCut Image) (journal : List (Command Image))
    (key : CopyKey) (cleared : initial.jobs key = none) :
    (replay original initial journal).1.jobs key = none := by
  induction journal generalizing initial with
  | nil => exact cleared
  | cons command _ prior =>
      exact prior (apply original initial command).1
        (an_ordered_command_cannot_recreate_a_discharged_copy original initial command key cleared)

theorem extending_a_recovered_prefix_keeps_every_discharged_copy_cleared
    (original : OriginalReceipts Image) (initial : TargetCut Image) {first later : List (Command Image)}
    (inherited : first <+: later) (key : CopyKey)
    (cleared : (replay original initial first).1.jobs key = none) :
    (replay original initial later).1.jobs key = none := by
  rcases inherited with ⟨suffix, rfl⟩
  rw [replay_append]
  exact a_replayed_suffix_cannot_recreate_a_discharged_copy original _ suffix key cleared

theorem each_current_recovery_majority_recovers_prior_chosen_outcomes
    {before next current : ConfigurationClosure.Generation Voter (Command Image)}
    (firstChange : ConfigurationClosure.Handoff before next)
    (subsequent : ConfigurationClosure.Changes next current)
    (installed : ConfigurationClosure.InstalledOnQuorum current)
    (available : Voter → Bool) (majority : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {history : List (Command Image)} (choice : Chosen before.ledger ballot history)
    (original : OriginalReceipts Image) (initial : TargetCut Image) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧
      current.installed voter current.basis ∧
      (replay original initial history).2 <+: (replay original initial current.basis).2 ∧
      ∀ key, (replay original initial history).1.jobs key = none →
        (replay original initial current.basis).1.jobs key = none := by
  obtain ⟨voter, member, online, exactCut, inherited⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority
      firstChange subsequent installed available majority choice
  exact ⟨voter, member, online, exactCut, chosen_outcomes_follow_any_exact_journal_extension original initial inherited,
    extending_a_recovered_prefix_keeps_every_discharged_copy_cleared original initial inherited⟩

structure Disposition where
  absent : CopyFence.Receipt → Prop
  durablyCharged : CopyFence.Receipt → Prop

structure CertifiedOriginal (original : OriginalReceipts Image) (authority : Nat → ChannelLifecycle.Authority)
    (authenticated : Nat → JournalRefinement.Journal Replica CustodianRecovery.Image → Prop)
    (disposition : Disposition)
    (key : CopyKey) (image : Image) : Prop where
  committed : ∃ journal, authenticated key.custodian journal ∧
      key.custodian = (original key image).key.handle.custodian ∧
      JournalRefinement.CompleteCut journal ∧
      CopyFence.CommittedRelease journal (authority key.custodian) (original key image)
  physical : disposition.absent (original key image) ∨ disposition.durablyCharged (original key image)

def settleFromCustodian (base : Evidence Image) (original : OriginalReceipts Image)
    (authority : Nat → ChannelLifecycle.Authority)
    (authenticated : Nat → JournalRefinement.Journal Replica CustodianRecovery.Image → Prop)
    (disposition : Disposition) : Evidence Image :=
  {base with settledCopy := CertifiedOriginal original authority authenticated disposition}

theorem a_settlement_certificate_accounts_for_the_exact_physical_copy
    {original : OriginalReceipts Image} {authority : Nat → ChannelLifecycle.Authority}
    {authenticated : Nat → JournalRefinement.Journal Replica CustodianRecovery.Image → Prop}
    {disposition : Disposition} {key : CopyKey} {image : Image}
    (certificate : CertifiedOriginal original authority authenticated disposition key image) :
    disposition.absent (original key image) ∨ disposition.durablyCharged (original key image) := by
  exact certificate.physical

theorem a_committed_original_release_supplies_the_composed_fence
    {base : Evidence Image} {original : OriginalReceipts Image}
    {authority : Nat → ChannelLifecycle.Authority}
    {authenticated : Nat → JournalRefinement.Journal Replica CustodianRecovery.Image → Prop}
    {disposition : Disposition} {state : State Image} {key : CopyKey} {image : Image}
    (planned : state.store.jobs key = some image)
    (proof : CertifiedOriginal original authority authenticated disposition key image) :
    ∃ after, ActivationComposition.Step (settleFromCustodian base original authority authenticated disposition) state after ∧
      after.fences key image ∧ after.store = state.store ∧ after.routing = state.routing := by
  exact ⟨_, .providerFence key image planned proof, Or.inl ⟨rfl, rfl⟩, rfl, rfl⟩

theorem a_current_owner_can_order_the_certified_custodian_receipt
    {base : Evidence Image} {original : OriginalReceipts Image}
    {authority : Nat → ChannelLifecycle.Authority}
    {authenticated : Nat → JournalRefinement.Journal Replica CustodianRecovery.Image → Prop}
    {disposition : Disposition} {state : State Image} {key : CopyKey} {image : Image} {owner : Nat}
    (current : ActivationComposition.CanWrite state owner)
    (planned : state.store.jobs key = some image)
    (sound : AuthenticFences (settleFromCustodian base original authority authenticated disposition) state)
    (proof : CertifiedOriginal original authority authenticated disposition key image) :
    let evidence := settleFromCustodian base original authority authenticated disposition
    ∃ after, ActivationComposition.Trace evidence state after ∧ after.store.jobs key = none := by
  let evidence := settleFromCustodian base original authority authenticated disposition
  obtain ⟨informed, notification, known, unchanged, sameRoute⟩ :=
    a_committed_original_release_supplies_the_composed_fence (base := base) planned proof
  have notifications : ActivationComposition.Trace evidence state informed := .next (.same _) notification
  have originalReceipt : informed.fences key image := known
  let command : Command Image := ⟨.settle key image, some (.fencedCopy key image (original key image))⟩
  have atIntake : CheckedAtIntake original informed command.attachment := ⟨rfl, originalReceipt⟩
  have stillCurrent : ActivationComposition.CanWrite informed owner := by
    simpa [ActivationComposition.CanWrite, sameRoute] using current
  obtain ⟨after, step, projected⟩ := an_ordered_evidence_command_refines_the_composed_reducer
    original informed command owner stillCurrent atIntake
    (activation_traces_preserve_authentic_fence_facts sound notifications)
  have selected := congrArg (fun cut : TargetCut Image => cut.jobs key) projected
  refine ⟨after, .next notifications step, ?_⟩
  have remains : informed.store.jobs key = some image := unchanged ▸ planned
  simpa [capture, apply, command, ExactAttachment, Required, remains, IntentRetirement.update] using selected

#print axioms no_eligible_ordered_attachment_means_refusal
#print axioms a_foreign_custodian_receipt_cannot_discharge_the_copy
#print axioms activation_traces_preserve_authentic_fence_facts
#print axioms an_ordered_evidence_command_refines_the_composed_reducer
#print axioms replay_append
#print axioms a_historical_refusal_remains_at_its_position
#print axioms chosen_outcomes_follow_any_exact_journal_extension
#print axioms a_replayed_suffix_cannot_recreate_a_discharged_copy
#print axioms extending_a_recovered_prefix_keeps_every_discharged_copy_cleared
#print axioms each_current_recovery_majority_recovers_prior_chosen_outcomes
#print axioms a_settlement_certificate_accounts_for_the_exact_physical_copy
#print axioms a_committed_original_release_supplies_the_composed_fence
#print axioms a_current_owner_can_order_the_certified_custodian_receipt

end CertifiedActivationReplay
