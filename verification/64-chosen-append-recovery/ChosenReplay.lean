import FundedAppend
import StagedVotes
import EnvelopeRecovery

set_option warningAsError true

namespace ChosenReplay

open SnapshotAdmission (setSlot)
open PrefixAgreement (Chosen)

variable {slots width : Nat} {Payload Ticket : Type}

structure Lineage where
  stream : Nat
  incarnation : Nat
  deriving DecidableEq

structure Grant (Ticket : Type) where
  version : Nat
  writer : Kernel.Writer
  proof : Ticket

structure Activation (slots : Nat) (Payload Ticket : Type) where
  installation : UnifiedSource.Installation slots Nat Payload Ticket
  grant : Grant Ticket

inductive Command (slots : Nat) (Payload Ticket : Type) where
  | append (request : FundedAppend.Request Payload Ticket)
  | install (grant : Grant Ticket)
  | activate (installation : Activation slots Payload Ticket)
  | prune (version : Nat)
  | source (command : UnifiedSource.Command slots Nat Payload Ticket)

structure Frame (slots : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots Payload Ticket

structure Applied (slots : Nat) (Payload Ticket : Type) where
  frame : Frame slots Payload Ticket
  reply : UnifiedSource.Reply Payload

structure Image (slots : Nat) (Payload : Type) where
  source : FundedAppend.Source slots Payload
  book : FundedAppend.Book

structure Rules (slots : Nat) (Payload Ticket : Type) where
  append : FundedAppend.Rules slots Payload Ticket
  grant : Lineage → Grant Ticket → Prop
  activation : Lineage → Activation slots Payload Ticket → Prop

def eligibleFrame (lineage : Lineage) (image : Image slots Payload) (frame : Frame slots Payload Ticket) : Prop :=
  frame.lineage = lineage ∧ frame.position = image.source.position + 1

def frameRules (rules : Rules slots Payload Ticket) (frame : Frame slots Payload Ticket) :
    FundedAppend.Rules slots Payload Ticket :=
  {rules.append with durable := fun stream request =>
    frame.lineage.stream = stream ∧ frame.command = .append request}

def InstallAllowed (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (grant : Grant Ticket) : Prop :=
  rules.grant lineage grant ∧ rules.append.owner grant.version = lineage.stream ∧
  image.book.latest lineage.stream < grant.version ∧ image.book.windows grant.version = none ∧
  image.source.core.stream.authority = .active grant.writer

def PruneAllowed (lineage : Lineage) (image : Image slots Payload) (version : Nat) : Prop :=
  ∃ window, image.book.windows version = some window ∧ window.stream = lineage.stream ∧
    (window.nextLsn ≤ image.source.core.stream.firstRetained ∨ image.source.core.stream.authority = .retired)

def advancePosition (image : Image slots Payload) : Image slots Payload :=
  {image with source := {image.source with position := image.source.position + 1}}

def installWindow (lineage : Lineage) (image : Image slots Payload) (grant : Grant Ticket) :
    Image slots Payload :=
  let window : FundedAppend.Window :=
    ⟨lineage.stream, grant.writer.placement, image.source.core.stream.history.length, 0⟩
  let book : FundedAppend.Book :=
    ⟨setSlot image.book.windows grant.version (some window), setSlot image.book.latest lineage.stream grant.version⟩
  {advancePosition image with book}

noncomputable def applyActivation (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (activation : Activation slots Payload Ticket) :
    Image slots Payload × UnifiedSource.Reply Payload :=
  let result := UnifiedSource.decide (rules.append.regional.limits lineage.stream)
    (rules.append.regional.source lineage.stream) image.source.core (image.source.position + 1)
    (.activate activation.installation)
  ({image with source := {image.source with core := result.1}}, result.2)

def AcceptsActivation (rules : Rules slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (activation : Activation slots Payload Ticket) : Prop :=
  let result := applyActivation rules lineage image activation
  result.2 = .accepted ∧ rules.activation lineage activation ∧
    InstallAllowed rules lineage result.1 activation.grant

noncomputable def decide (rules : Rules slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (frame : Frame slots Payload Ticket) : Image slots Payload × UnifiedSource.Reply Payload := by
  classical
  let refused := (advancePosition image, (UnifiedSource.Reply.refused : UnifiedSource.Reply Payload))
  exact match frame.command with
  | .append request =>
      let next := FundedAppend.decide (frameRules rules frame) lineage.stream image.source image.book request
      (⟨next.1, next.2.1⟩, next.2.2)
  | .install grant =>
      if InstallAllowed rules lineage image grant then (installWindow lineage image grant, .accepted) else refused
  | .activate activation =>
      if AcceptsActivation rules lineage image activation then
        (installWindow lineage (applyActivation rules lineage image activation).1 activation.grant, .accepted)
      else refused
  | .prune version =>
      if PruneAllowed lineage image version then
        ({advancePosition image with book := {image.book with windows := setSlot image.book.windows version none}},
          .accepted)
      else refused
  | .source (.activate _) => refused
  | .source command =>
      let outcome := UnifiedSource.decide (rules.append.regional.limits lineage.stream)
        (rules.append.regional.source lineage.stream) image.source.core (image.source.position + 1) command
      if outcome.1.stream.history = image.source.core.stream.history then
        ({image with source := ⟨outcome.1, image.source.position + 1⟩}, outcome.2)
      else refused

noncomputable def replay (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (frames : List (Frame slots Payload Ticket)) :
    Option (Image slots Payload × List (Applied slots Payload Ticket)) := by
  classical
  exact match frames with
  | [] => some (image, [])
  | frame :: rest =>
      if eligibleFrame lineage image frame then
        let outcome := decide rules lineage image frame
        (replay rules lineage outcome.1 rest).map fun tail => (tail.1, ⟨frame, outcome.2⟩ :: tail.2)
      else none

abbrev Outcomes (slots : Nat) (Payload Ticket : Type) :=
  Image slots Payload × List (Applied slots Payload Ticket)

def CheckpointFor (rules : Rules slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : List (Frame slots Payload Ticket)) (cut : Nat) (base : Image slots Payload) : Prop :=
  ∃ decisions, replay rules lineage origin (chosen.take cut) = some (base, decisions)

noncomputable def selectSuffix (chosen physical : List (Frame slots Payload Ticket)) :
    Option (List (Frame slots Payload Ticket)) := by
  classical
  exact if chosen <+: physical then some (physical.take chosen.length) else none

private noncomputable def recover (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (base : Image slots Payload) (cut : Nat)
    (chosen physical : List (Frame slots Payload Ticket)) : Option (Outcomes slots Payload Ticket) :=
  (selectSuffix (chosen.drop cut) physical).bind (replay rules lineage base)

structure CertifiedCut {Voter : Type} (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)) where
  ballot : Nat
  frames : List (Frame slots Payload Ticket)
  chosen : Chosen ledger ballot frames

structure SelectedBase (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (origin : Image slots Payload) (chosen : List (Frame slots Payload Ticket)) where
  cut : Nat
  image : Image slots Payload
  within : cut ≤ chosen.length
  certified : CheckpointFor rules lineage origin chosen cut image

noncomputable def reopen {Voter : Type} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : CertifiedCut ledger) (selected : SelectedBase rules lineage origin chosen.frames)
    (physical : List (Frame slots Payload Ticket)) : Option (Outcomes slots Payload Ticket) :=
  recover rules lineage selected.image selected.cut chosen.frames physical

structure Observed {Voter : Type} (ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket))
    (media : StagedVotes.Rules slots (Frame slots Payload Ticket) Ticket) where
  replicas : Voter → StagedVotes.State (Frame slots Payload Ticket) Ticket
  sound : ∀ voter ∈ ledger.members, StagedVotes.Sound media (replicas voter)
  ballots : PrefixAgreement.BallotRules ledger
  votes : ∀ voter ∈ ledger.members, ∀ vote, ledger.voted voter vote → (replicas voter).voter.votes vote
  reports : ∀ voter ∈ ledger.members, ∀ ballot, ledger.prepared ballot voter = true →
    (replicas voter).voter.replies ballot = some (ledger.report ballot voter)

theorem votes_with_durable_scope_agree_on_exact_frames
    {Voter : Type} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    {media : StagedVotes.Rules slots (Frame slots Payload Ticket) Ticket}
    (observed : Observed ledger media) {first second : Nat}
    {left right : List (Frame slots Payload Ticket)} (leftChoice : Chosen ledger first left)
    (rightChoice : Chosen ledger second right) {atIndex : Nat} {a b : Frame slots Payload Ticket}
    (inLeft : left[atIndex]? = some a) (inRight : right[atIndex]? = some b) : a = b := by
  have coverage := DurableAcceptor.durable_acceptor_traces_supply_quorum_reply_coverage (ledger := ledger)
    (fun voter => (observed.replicas voter).voter)
    (fun voter member => (observed.sound voter member).voter) observed.votes observed.reports
  exact PrefixAgreement.any_two_certificates_agree_at_position ⟨observed.ballots, coverage⟩
    leftChoice rightChoice inLeft inRight

theorem certified_append_accepts_only_the_frame_request
    {rules : Rules slots Payload Ticket} {frame : Frame slots Payload Ticket} {stream : Nat}
    {request : FundedAppend.Request Payload Ticket} (checked : (frameRules rules frame).durable stream request) :
    frame.lineage.stream = stream ∧ frame.command = .append request := by
  exact checked

theorem the_applied_chosen_append_uses_the_actual_charged_window
    {rules : Rules slots Payload Ticket} {lineage : Lineage} {state : FundedAppend.State slots Payload Ticket}
    {frame : Frame slots Payload Ticket} {request : FundedAppend.Request Payload Ticket}
    (command : frame.command = .append request)
    (funded : FundedAppend.Funded rules.append state)
    (accepted : (decide rules lineage ⟨state.regional.streams lineage.stream, state.book⟩ frame).2 =
      .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩)) :
    ∃ window, state.book.windows request.version = some window ∧
      FundedAppend.Backed state.regional request.version ∧
      rules.append.owner request.version = lineage.stream ∧
      request.offset = window.spent ∧
      window.spent < request.offset + rules.append.cost request.payload ∧
      request.offset + rules.append.cost request.payload ≤ FundedAppend.debitBytes rules.append request.version := by
  simp only [decide, command] at accepted
  exact FundedAppend.a_successful_append_spends_only_its_own_prepaid_range
    (rules := frameRules rules frame) funded accepted

theorem a_cross_lineage_or_out_of_order_frame_cannot_enter_replay
    {rules : Rules slots Payload Ticket} {lineage : Lineage} {image : Image slots Payload}
    {frame : Frame slots Payload Ticket} (wrong : frame.lineage ≠ lineage ∨
      frame.position ≠ image.source.position + 1) (rest : List (Frame slots Payload Ticket)) :
    replay rules lineage image (frame :: rest) = none := by
  have denied : ¬ eligibleFrame lineage image frame := fun admissible =>
    wrong.elim (fun apart => apart admissible.1) (fun apart => apart admissible.2)
  simp [replay, denied]

theorem a_window_install_changes_the_replay_basis_without_advancing_data
    {rules : Rules slots Payload Ticket} {lineage : Lineage} {image : Image slots Payload}
    {grant : Grant Ticket} (admitted : InstallAllowed rules lineage image grant) :
    let frame : Frame slots Payload Ticket := ⟨lineage, image.source.position + 1, .install grant⟩
    let applied := (decide rules lineage image frame).1
    applied.source.core.stream.history = image.source.core.stream.history ∧
      applied.source.position = image.source.position + 1 ∧
      image.book.latest lineage.stream < applied.book.latest lineage.stream := by
  simp [decide, admitted, installWindow, advancePosition, setSlot, admitted.2.2.1]

theorem checked_suffix_is_exact
    {chosen physical result : List (Frame slots Payload Ticket)}
    (selected : selectSuffix chosen physical = some result) :
    result = chosen ∧ chosen <+: physical := by
  simp only [selectSuffix] at selected
  split at selected
  · rename_i prefixOf
    have clipped : physical.take chosen.length = result := Option.some.inj selected
    refine ⟨clipped.symm.trans ?_, prefixOf⟩
    obtain ⟨surplus, rfl⟩ := prefixOf
    exact List.take_append_length
  · cases selected

theorem checked_suffix_excludes_an_intact_unchosen_continuation
    (chosen surplus : List (Frame slots Payload Ticket)) :
    selectSuffix chosen (chosen ++ surplus) = some chosen := by
  have alignment : chosen <+: chosen ++ surplus := List.prefix_append _ _
  have existsSuffix : ∃ result, selectSuffix chosen (chosen ++ surplus) = some result := by
    rw [selectSuffix, ite_eq_left alignment]
    exact ⟨_, rfl⟩
  obtain ⟨selected, readable⟩ := existsSuffix
  exact (checked_suffix_is_exact readable).1 ▸ readable

theorem never_substitute_a_rival_or_missing_suffix
    {chosen physical : List (Frame slots Payload Ticket)} (incompatible : ¬ chosen <+: physical) :
    selectSuffix chosen physical = none := by
  simp [selectSuffix, incompatible]

theorem replay_returns_only_original_command_records
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (frames : List (Frame slots Payload Ticket))
    {final : Image slots Payload} {outcomes : List (Applied slots Payload Ticket)}
    (replayed : replay rules lineage image frames = some (final, outcomes)) :
    outcomes.map Applied.frame = frames := by
  induction frames generalizing image outcomes with
  | nil => simp [replay] at replayed; simp [replayed.2.symm]
  | cons frame tail prior =>
    simp only [replay] at replayed
    split at replayed
    · cases tailReplay : replay rules lineage (decide rules lineage image frame).1 tail with
      | none => simp [tailReplay] at replayed
      | some result =>
        simp [tailReplay] at replayed
        rw [← replayed.2]
        simp only [List.map_cons, List.cons.injEq, true_and]
        have exactTail : replay rules lineage (decide rules lineage image frame).1 tail =
            some (final, result.2) := by
          rw [← replayed.1]
          cases result
          exact tailReplay
        exact prior _ exactTail
    · cases replayed

theorem replay_after_a_certified_prefix
    (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (initial base : Image slots Payload) (earlier suffix : List (Frame slots Payload Ticket))
    {before : List (Applied slots Payload Ticket)}
    (replayed : replay rules lineage initial earlier = some (base, before)) :
    replay rules lineage initial (earlier ++ suffix) =
      (replay rules lineage base suffix).map (fun rest => (rest.1, before ++ rest.2)) := by
  induction earlier generalizing initial before with
  | nil =>
    simp [replay] at replayed
    obtain ⟨rfl, rfl⟩ := replayed
    simp only [List.nil_append]
    cases replay rules lineage initial suffix with
    | none => rfl
    | some pair => cases pair; rfl
  | cons frame tail prior =>
    simp only [List.cons_append, replay] at replayed ⊢
    split at replayed
    · rename_i permitted
      simp only [ite_eq_left permitted]
      cases tailReplay : replay rules lineage (decide rules lineage initial frame).1 tail with
      | none => simp [tailReplay] at replayed
      | some result =>
        simp [tailReplay] at replayed
        obtain ⟨rfl, rfl⟩ := replayed
        rw [prior _ tailReplay]
        cases replay rules lineage result.1 suffix <;> rfl
    · cases replayed

theorem successful_recovery_matches_the_exact_chosen_history
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (initial base final : Image slots Payload)
    (chosen physical : List (Frame slots Payload Ticket)) (cut : Nat)
    (baseCertified : CheckpointFor rules lineage initial chosen cut base)
    {suffix : List (Applied slots Payload Ticket)}
    (opened : recover rules lineage base cut chosen physical = some (final, suffix)) :
    ∃ earlier, replay rules lineage initial chosen = some (final, earlier ++ suffix) ∧
      suffix.map Applied.frame = chosen.drop cut := by
  unfold recover at opened
  cases readSuffix : selectSuffix (chosen.drop cut) physical with
  | none => simp [readSuffix] at opened
  | some entries =>
    have exactTail := (checked_suffix_is_exact readSuffix).1
    subst entries
    rw [readSuffix] at opened
    change replay rules lineage base (chosen.drop cut) = some (final, suffix) at opened
    obtain ⟨earlier, exactBase⟩ := baseCertified
    refine ⟨earlier, ?_, replay_returns_only_original_command_records _ _ _ _ opened⟩
    calc
      replay rules lineage initial chosen =
        replay rules lineage initial (chosen.take cut ++ chosen.drop cut) := by rw [List.take_append_drop]
      _ = some (final, earlier ++ suffix) := by
        rw [replay_after_a_certified_prefix _ _ _ _ _ _ exactBase, opened]
        rfl

theorem two_selectable_bases_restore_one_exact_state_and_suffix
    {Voter : Type} {ledger : PrefixAgreement.Ledger Voter (Frame slots Payload Ticket)}
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : CertifiedCut ledger) (old new : SelectedBase rules lineage origin chosen.frames)
    (oldPhysical newPhysical : List (Frame slots Payload Ticket))
    {left right : Image slots Payload} {oldTail newTail : List (Applied slots Payload Ticket)}
    (reopenedOld : reopen rules lineage origin chosen old oldPhysical = some (left, oldTail))
    (reopenedNew : reopen rules lineage origin chosen new newPhysical = some (right, newTail)) :
    left = right ∧ oldTail.map Applied.frame = chosen.frames.drop old.cut ∧
      newTail.map Applied.frame = chosen.frames.drop new.cut := by
  obtain ⟨_, exactOld, recordsOld⟩ :=
    successful_recovery_matches_the_exact_chosen_history rules lineage origin old.image left chosen.frames
      oldPhysical old.cut old.certified reopenedOld
  obtain ⟨_, exactNew, recordsNew⟩ :=
    successful_recovery_matches_the_exact_chosen_history rules lineage origin new.image right chosen.frames
      newPhysical new.cut new.certified reopenedNew
  exact ⟨congrArg Prod.fst (Option.some.inj (exactOld.symm.trans exactNew)), recordsOld, recordsNew⟩

theorem a_canonical_checkpoint_restores_the_same_source_and_window_book
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (initial final : Image slots Payload)
    (catalog : EnvelopeRecovery.Catalog width FundedAppend.Book (FundedAppend.Source slots Payload))
    (authenticated : EnvelopeCodec.Bytes → Prop) (needed : EnvelopeCodec.Field width → Prop)
    (anchor : EnvelopeRecovery.Anchor width)
    {wire : EnvelopeCodec.Bytes} {header : EnvelopeCodec.Envelope width}
    {contents : EnvelopeRecovery.Contents width FundedAppend.Book (FundedAppend.Source slots Payload)}
    (opened : EnvelopeRecovery.Opened catalog authenticated anchor needed wire header contents)
    {cut : Nat} {chosen physical : List (Frame slots Payload Ticket)}
    (atCut : CheckpointFor rules lineage initial chosen cut ⟨contents.data, contents.control⟩)
    {suffix : List (Applied slots Payload Ticket)}
    (recovered : recover rules lineage ⟨contents.data, contents.control⟩ cut chosen physical =
      some (final, suffix)) :
    (∀ object, needed object → catalog.retained object) ∧
      ∃ before, replay rules lineage initial chosen = some (final, before ++ suffix) ∧
        suffix.map Applied.frame = chosen.drop cut := by
  exact ⟨fun object neededHere => EnvelopeRecovery.opened_checkpoint_covers_every_required_object opened object neededHere,
    successful_recovery_matches_the_exact_chosen_history rules lineage initial _ final
      chosen physical cut atCut recovered⟩

#print axioms votes_with_durable_scope_agree_on_exact_frames
#print axioms certified_append_accepts_only_the_frame_request
#print axioms the_applied_chosen_append_uses_the_actual_charged_window
#print axioms a_cross_lineage_or_out_of_order_frame_cannot_enter_replay
#print axioms a_window_install_changes_the_replay_basis_without_advancing_data
#print axioms checked_suffix_is_exact
#print axioms checked_suffix_excludes_an_intact_unchosen_continuation
#print axioms never_substitute_a_rival_or_missing_suffix
#print axioms replay_returns_only_original_command_records
#print axioms replay_after_a_certified_prefix
#print axioms successful_recovery_matches_the_exact_chosen_history
#print axioms two_selectable_bases_restore_one_exact_state_and_suffix
#print axioms a_canonical_checkpoint_restores_the_same_source_and_window_book

end ChosenReplay
