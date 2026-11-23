import GrantPolicyWire

set_option warningAsError true

namespace OrderedPolicyVerifiers

open ChosenReplay (Lineage)
open EnvelopeCodec (Bytes Field wordLimit)
open GrantPolicyWire (Packet Verifier)

variable {bytes slots capacity limit : Nat} {Payload Ticket Key Signature Voter : Type}

structure Rules (bytes slots capacity limit : Nat) (Payload Ticket Key Signature : Type) where
  ordered : RetainedDelivery.Rules bytes slots capacity limit Payload Ticket
  formatMax : Nat
  verify : Key → Bytes → Signature → Prop
  mayRotate : Lineage → Verifier Key → Verifier Key → Ticket → Prop

structure Image (slots capacity limit : Nat) (Payload Key : Type) where
  policy : GrantReadPolicy.Image slots capacity limit Payload
  verifier : Verifier Key

structure SignedProposal (Ticket Signature : Type) where
  request : GrantReadPolicy.Proposal Ticket
  proof : Packet Signature

noncomputable def atVerifier (rules : Rules bytes slots capacity limit Payload Ticket Key Signature)
    (current : Verifier Key) (offered : Option (SignedProposal Ticket Signature)) :
    GrantReadPolicy.Rules bytes slots capacity limit Payload Ticket := by
  classical
  exact ⟨rules.ordered, rules.formatMax, fun ticket => do
    let attachment ← offered
    if attachment.request.evidence = ticket then
      GrantPolicyWire.authenticate bytes current rules.verify attachment.proof
    else none⟩

inductive Command (slots capacity limit : Nat) (Payload Ticket Key Signature : Type) where
  | effect (request : RetainedDelivery.Command slots capacity limit Payload Ticket)
      (offer : Option (SignedProposal Ticket Signature))
  | rotate (candidate : Verifier Key) (evidence : Ticket)

inductive Reply (Payload : Type) (capacity : Nat) where
  | effect (result : RetainedDelivery.Reply Payload capacity)
  | rotated
  | refused

def advance (before : GrantReadPolicy.Image slots capacity limit Payload) :
    GrantReadPolicy.Image slots capacity limit Payload :=
  ⟨before.horizon, SelectiveOrderedRecovery.advance before.state⟩

def AllowsRotation (rules : Rules bytes slots capacity limit Payload Ticket Key Signature)
    (lineage : Lineage) (before candidate : Verifier Key) (evidence : Ticket) : Prop :=
  before.version < candidate.version ∧ candidate.version < wordLimit bytes ∧
    rules.mayRotate lineage before candidate evidence

noncomputable def decide (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (before : Image slots capacity limit Payload Key) (command : Command slots capacity limit Payload Ticket Key Signature) :
    Image slots capacity limit Payload Key × Reply Payload capacity := by
  classical
  exact match command with
  | .effect request offer =>
    let applied := GrantReadPolicy.decide (atVerifier rules before.verifier offer) lineage before.policy
      ⟨request, offer.map SignedProposal.request⟩
    (⟨applied.1, before.verifier⟩, .effect applied.2)
  | .rotate candidate evidence =>
    if AllowsRotation rules lineage before.verifier candidate evidence then
      (⟨advance before.policy, candidate⟩, .rotated)
    else (⟨advance before.policy, before.verifier⟩, .refused)

theorem rotation_is_an_ordered_administrative_decision_without_a_policy_packet
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (before : Image slots capacity limit Payload Key) (candidate : Verifier Key) (evidence : Ticket)
    (allowed : AllowsRotation rules lineage before.verifier candidate evidence) :
    decide rules lineage before (.rotate candidate evidence) = (⟨advance before.policy, candidate⟩, .rotated) ∧
      candidate.version > before.verifier.version := by
  exact ⟨by simp [decide, allowed], allowed.1⟩

theorem every_decision_keeps_or_advances_the_verifier_version
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (before : Image slots capacity limit Payload Key) (command : Command slots capacity limit Payload Ticket Key Signature) :
    let after := (decide rules lineage before command).1
    after.verifier = before.verifier ∨ before.verifier.version < after.verifier.version := by
  cases command with
  | effect request offer => exact .inl rfl
  | rotate candidate evidence =>
    simp only [decide]
    split
    · next allowed =>
      exact .inr allowed.1
    · exact .inl rfl

theorem a_fresh_changed_policy_must_use_its_current_exact_signed_message
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (before : Image slots capacity limit Payload Key)
    (request : RetainedDelivery.Command slots capacity limit Payload Ticket)
    (offered : Option (SignedProposal Ticket Signature))
    (changed : before.policy.horizon ≠ (decide rules lineage before (.effect request offered)).1.policy.horizon) :
    let applied := (decide rules lineage before (.effect request offered)).1.policy
    ∃ attachment message, offered = some attachment ∧
      GrantPolicyWire.decode bytes attachment.proof.body = some message ∧
      message.version = before.verifier.version ∧
      rules.verify before.verifier.key attachment.proof.body attachment.proof.signature ∧
      GrantPolicyWire.binding message = GrantReadPolicy.binding lineage applied := by
  intro applied
  obtain ⟨_, proposed, signed, _, _, record, authorization, exactPolicy, _, _⟩ :=
    GrantReadPolicy.a_changed_width_requires_its_exact_authenticated_successor
      (atVerifier rules before.verifier offered) lineage before.policy applied
      ⟨request, offered.map SignedProposal.request⟩ rfl changed
  cases offered with
  | none => simp at record
  | some attachment =>
    have exactRequest : attachment.request = proposed := by simpa using record
    subst proposed
    have verified : GrantPolicyWire.authenticate bytes before.verifier rules.verify attachment.proof = some signed := by
      simpa [atVerifier] using authorization
    obtain ⟨message, decoded, version, cryptographic, binds⟩ :=
      GrantPolicyWire.a_verified_offer_returns_only_its_exact_signed_scope bytes before.verifier rules.verify
        attachment.proof signed verified
    refine ⟨attachment, message, rfl, decoded, version, ?_, binds.symm.trans exactPolicy⟩
    rw [← GrantPolicyWire.decoded_policy_bytes_have_one_canonical_encoding decoded]
    exact cryptographic

theorem an_inline_offer_with_a_retired_version_cannot_change_the_current_width
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (before : Image slots capacity limit Payload Key)
    (request : RetainedDelivery.Command slots capacity limit Payload Ticket)
    (attachment : SignedProposal Ticket Signature) (old : GrantPolicyWire.Message)
    (decoded : GrantPolicyWire.decode bytes attachment.proof.body = some old)
    (retired : old.version ≠ before.verifier.version) :
    before.policy.horizon = (decide rules lineage before (.effect request (some attachment))).1.policy.horizon := by
  by_cases sameWidth : before.policy.horizon =
      (decide rules lineage before (.effect request (some attachment))).1.policy.horizon
  · exact sameWidth
  · obtain ⟨actual, message, offered, same, version, _, _⟩ :=
      a_fresh_changed_policy_must_use_its_current_exact_signed_message rules lineage before request (some attachment) sameWidth
    cases offered
    have exactBody : old = message := Option.some.inj (decoded.symm.trans same)
    exact False.elim (retired ((congrArg GrantPolicyWire.Message.version exactBody).trans version))

structure Frame (slots capacity limit : Nat) (Payload Ticket Key Signature : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots capacity limit Payload Ticket Key Signature

noncomputable def step (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (before : Image slots capacity limit Payload Key) (frame : Frame slots capacity limit Payload Ticket Key Signature) :
    Option (Image slots capacity limit Payload Key) := by
  classical
  exact if frame.lineage = lineage ∧ frame.position = RetainedDelivery.position before.policy.state.body + 1 then
    some (decide rules lineage before frame.command).1 else none

noncomputable def replay (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (origin : Image slots capacity limit Payload Key) (frames : List (Frame slots capacity limit Payload Ticket Key Signature)) :
    Option (Image slots capacity limit Payload Key) :=
  frames.foldlM (step rules lineage) origin

private theorem replay_after_prefix
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (origin base : Image slots capacity limit Payload Key)
    (prefixFrames suffix : List (Frame slots capacity limit Payload Ticket Key Signature))
    (certified : replay rules lineage origin prefixFrames = some base) :
    replay rules lineage origin (prefixFrames ++ suffix) = replay rules lineage base suffix := by
  simp only [replay] at certified ⊢
  rw [List.foldlM_append, certified]
  rfl

structure Base (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (origin : Image slots capacity limit Payload Key) (frames : List (Frame slots capacity limit Payload Ticket Key Signature)) where
  cut : Nat
  image : Image slots capacity limit Payload Key
  within : cut ≤ frames.length
  certified : replay rules lineage origin (frames.take cut) = some image

noncomputable def reopen (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    {origin : Image slots capacity limit Payload Key}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket Key Signature)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket Key Signature)}
    (_chosen : PrefixAgreement.Chosen ledger ballot frames) (base : Base rules lineage origin frames)
    (supplied : Verifier Key) (media : List (Frame slots capacity limit Payload Ticket Key Signature)) :
    Option (Image slots capacity limit Payload Key) := by
  classical
  exact if supplied = base.image.verifier ∧ frames.drop base.cut <+: media then
    replay rules lineage base.image (frames.drop base.cut)
  else none

theorem any_reopened_choice_uses_its_own_historical_verifier
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    {origin : Image slots capacity limit Payload Key}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket Key Signature)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket Key Signature)}
    (chosen : PrefixAgreement.Chosen ledger ballot frames) (base : Base rules lineage origin frames)
    (supplied : Verifier Key) (media : List (Frame slots capacity limit Payload Ticket Key Signature))
    (after : Image slots capacity limit Payload Key) (opened : reopen rules lineage chosen base supplied media = some after) :
    supplied = base.image.verifier ∧ replay rules lineage origin frames = some after := by
  unfold reopen at opened
  split at opened
  · next checked =>
    refine ⟨checked.1, ?_⟩
    rw [← List.take_append_drop base.cut frames,
      replay_after_prefix rules lineage origin base.image _ _ base.certified]
    exact opened
  · cases opened

theorem rotated_policy_recovers_identically_from_either_certified_base
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    {origin : Image slots capacity limit Payload Key}
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket Key Signature)}
    {ballot : Nat} {frames : List (Frame slots capacity limit Payload Ticket Key Signature)}
    (chosen : PrefixAgreement.Chosen ledger ballot frames) (old new : Base rules lineage origin frames)
    (oldVerifier newVerifier : Verifier Key) (oldMedia newMedia : List (Frame slots capacity limit Payload Ticket Key Signature))
    (first second : Image slots capacity limit Payload Key)
    (one : reopen rules lineage chosen old oldVerifier oldMedia = some first)
    (two : reopen rules lineage chosen new newVerifier newMedia = some second) : first = second := by
  have left := (any_reopened_choice_uses_its_own_historical_verifier rules lineage chosen old oldVerifier oldMedia first one).2
  have right := (any_reopened_choice_uses_its_own_historical_verifier rules lineage chosen new newVerifier newMedia second two).2
  exact Option.some.inj (left.symm.trans right)

theorem an_actual_crash_choice_replays_the_exact_inline_verifier_history
    (rules : Rules bytes slots capacity limit Payload Ticket Key Signature) (lineage : Lineage)
    (origin after : Image slots capacity limit Payload Key)
    (first current : JournalRotation.State (Frame slots capacity limit Payload Ticket Key Signature))
    (safe : JournalRotation.Safe first) (tracked : JournalRotation.TracksNamespace first)
    (media : JournalRotation.Trace first current) (view : JournalRotation.View)
    (selected : current.namespaceChoices view)
    (replayed : replay rules lineage origin current.history = some after) :
    ∃ prefixFrames suffix atCut,
      current.media (.base view.generation) = some prefixFrames ∧
      (∀ offset frame, suffix[offset]? = some frame →
        current.media (.tail (view.cut + offset)) = some [frame]) ∧
      replay rules lineage origin prefixFrames = some atCut ∧
      replay rules lineage atCut suffix = some after := by
  obtain ⟨remainsSafe, covers⟩ := JournalRotation.every_trace_preserves_safety safe tracked media
  obtain ⟨prefixFrames, suffix, opened, whole, exactBytes⟩ :=
    JournalRotation.recovery_paths_cover_the_same_history remainsSafe covers selected
  rw [← whole] at replayed
  cases loaded : replay rules lineage origin prefixFrames with
  | none =>
    simp only [replay, List.foldlM_append] at replayed
    simp only [replay] at loaded
    rw [loaded] at replayed
    cases replayed
  | some atCut =>
    exact ⟨prefixFrames, suffix, atCut, opened, exactBytes, loaded,
      (replay_after_prefix rules lineage origin atCut prefixFrames suffix loaded).symm.trans replayed⟩

structure Control (bytes slots capacity limit : Nat) (Payload Key : Type) where
  body : GrantReadPolicy.Control bytes slots capacity limit Payload
  verifier : Verifier Key

abbrev Catalog (bytes slots capacity limit : Nat) (Payload Key : Type) :=
  EnvelopeRecovery.Catalog bytes (Control bytes slots capacity limit Payload Key) (FundedAppend.Source slots Payload)

noncomputable def openVerifier (catalog : Catalog bytes slots capacity limit Payload Key)
    (authenticated : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor bytes) (needs : Field bytes → Prop)
    (wire : Bytes) (expected : Verifier Key) : Option (Verifier Key) := by
  classical
  exact do
    let (_, contents) ← EnvelopeRecovery.openChecked catalog authenticated anchor needs wire
    if contents.control.verifier = expected then some contents.control.verifier else none

theorem a_historical_verifier_is_named_in_the_authentic_checkpoint
    (catalog : Catalog bytes slots capacity limit Payload Key)
    (authenticated : Bytes → Prop) (anchor : EnvelopeRecovery.Anchor bytes) (needs : Field bytes → Prop)
    (wire : Bytes) (expected found : Verifier Key) (opened : openVerifier catalog authenticated anchor needs wire expected = some found) :
    ∃ header contents, EnvelopeRecovery.Opened catalog authenticated anchor needs wire header contents ∧
      contents.control.verifier = found ∧ found = expected := by
  cases named : EnvelopeRecovery.openChecked catalog authenticated anchor needs wire with
  | none => simp [openVerifier, named] at opened
  | some pair =>
    obtain ⟨header, contents⟩ := pair
    by_cases same : contents.control.verifier = expected
    · have exactKey : contents.control.verifier = found := by simpa [openVerifier, named, same] using opened
      exact ⟨header, contents, EnvelopeRecovery.a_successful_open_has_all_authentication_and_custody_checks named,
        exactKey, exactKey.symm.trans same⟩
    · simp [openVerifier, named, same] at opened

#print axioms rotation_is_an_ordered_administrative_decision_without_a_policy_packet
#print axioms every_decision_keeps_or_advances_the_verifier_version
#print axioms a_fresh_changed_policy_must_use_its_current_exact_signed_message
#print axioms an_inline_offer_with_a_retired_version_cannot_change_the_current_width
#print axioms any_reopened_choice_uses_its_own_historical_verifier
#print axioms rotated_policy_recovers_identically_from_either_certified_base
#print axioms an_actual_crash_choice_replays_the_exact_inline_verifier_history
#print axioms a_historical_verifier_is_named_in_the_authentic_checkpoint

end OrderedPolicyVerifiers
