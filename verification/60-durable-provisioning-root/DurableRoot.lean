import NamespaceClosure
import MediaCrash
import JournalRotation

set_option warningAsError true

namespace DurableRoot

open NamespaceClosure (Bank Scope Phase Terminal)

variable {Address Payload ChildCommand : Type} {width : Nat}

inductive Command (Address ChildCommand : Type) (width : Nat) where
  | reserve (scope : Scope Address)
  | seed (scope : Scope Address) (index : Fin width)
  | finish (scope : Scope Address)
  | child (command : ChildCommand)

inductive Reply (Address : Type) (width : Nat) where
  | reserved (scope : Scope Address)
  | seeded (scope : Scope Address) (index : Fin width)
  | terminal (scope : Scope Address)
  | updated
  | refused

abbrev Records (Address ChildCommand : Type) (width : Nat) := List (Command Address ChildCommand width)

structure Rules (Address Payload ChildCommand : Type) (width : Nat) [DecidableEq Address] where
  provider : NamespaceClosure.Rules Address width
  child : Bank Address Payload width → ChildCommand → Option (Bank Address Payload width)
  childSound : ∀ bank command next, child bank command = some next → NamespaceClosure.Step provider bank next

variable [DecidableEq Address]

noncomputable def decide (rules : Rules Address Payload ChildCommand width) (bank : Bank Address Payload width) :
    Command Address ChildCommand width → Bank Address Payload width × Reply Address width := by
  classical
  exact fun command => match command with
  | .reserve scope =>
      if scope = ⟨bank.address, bank.issued + 1⟩ ∧ bank.phase = .vacant ∧ rules.provider.bankFunded scope then
        ({bank with issued := bank.issued + 1, phase := .provisioning}, .reserved scope)
      else (bank, .refused)
  | .seed scope index =>
      match NamespaceClosure.seedIfLive bank scope index with
      | some next => (next, .seeded scope index)
      | none => (bank, .refused)
  | .finish scope =>
      if scope = NamespaceClosure.current bank ∧ 0 < scope.serial ∧ bank.phase ≠ .vacant ∧
          rules.provider.closing scope ∧ NamespaceClosure.AllMissing bank ∧ rules.provider.auxiliaryClosed scope then
        ({bank with phase := .vacant}, .terminal scope)
      else (bank, .refused)
  | .child command =>
      match rules.child bank command with
      | some next => (next, .updated)
      | none => (bank, .refused)

noncomputable def apply (rules : Rules Address Payload ChildCommand width) (bank : Bank Address Payload width)
    (command : Command Address ChildCommand width) : Bank Address Payload width :=
  (decide rules bank command).1

theorem every_root_record_stutters_or_uses_the_namespace_reducer
    (rules : Rules Address Payload ChildCommand width) (bank : Bank Address Payload width)
    (command : Command Address ChildCommand width) :
    apply rules bank command = bank ∨ NamespaceClosure.Step rules.provider bank (apply rules bank command) := by
  cases command with
  | reserve scope =>
      simp only [apply, decide]
      split
      next admitted =>
        exact .inr (.reserve admitted.2.1 (admitted.1 ▸ admitted.2.2))
      next => exact .inl rfl
  | seed scope index =>
      cases result : NamespaceClosure.seedIfLive bank scope index with
      | none => exact .inl (by simp [apply, decide, result])
      | some next =>
          exact .inr (by simpa [apply, decide, result] using
            (NamespaceClosure.Step.seed (rules := rules.provider) scope index result))
  | finish scope =>
      simp only [apply, decide]
      split
      next admitted =>
        exact .inr (.finish admitted.2.2.1
          (admitted.1 ▸ admitted.2.2.2.1) admitted.2.2.2.2.1 (admitted.1 ▸ admitted.2.2.2.2.2))
      next => exact .inl rfl
  | child command =>
      cases result : rules.child bank command with
      | none => exact .inl (by simp [apply, decide, result])
      | some next => exact .inr (by simpa [apply, decide, result] using rules.childSound bank command next result)

theorem every_positive_terminal_decision_closes_its_exact_scope
    (rules : Rules Address Payload ChildCommand width)
    {bank : Bank Address Payload width} {scope : Scope Address}
    (terminal : (decide rules bank (.finish scope)).2 = .terminal scope) :
    Terminal rules.provider (apply rules bank (.finish scope)) scope := by
  simp only [apply, decide] at terminal ⊢
  split at terminal
  next admitted =>
    simp only [ite_eq_left admitted]
    exact ⟨⟨congrArg Scope.address admitted.1, admitted.2.1,
      .inr ⟨congrArg Scope.serial admitted.1, rfl⟩⟩, admitted.2.2.2.2.2⟩
  next => contradiction

private theorem prepend_root_step {rules : NamespaceClosure.Rules Address width}
    {first next last : Bank Address Payload width} (step : NamespaceClosure.Step rules first next)
    (rest : NamespaceClosure.Trace rules next last) : NamespaceClosure.Trace rules first last := by
  induction rest with
  | same => exact .next (.same _) step
  | next _ transition earlier => exact .next earlier transition

theorem root_replay_is_a_namespace_trace (rules : Rules Address Payload ChildCommand width)
    (initial : Bank Address Payload width) (history : Records Address ChildCommand width) :
    NamespaceClosure.Trace rules.provider initial (history.foldl (apply rules) initial) := by
  induction history generalizing initial with
  | nil => exact .same _
  | cons command rest prior =>
      simp only [List.foldl_cons]
      rcases every_root_record_stutters_or_uses_the_namespace_reducer rules initial command with unchanged | step
      · rw [unchanged]
        exact prior initial
      · exact prepend_root_step step (prior _)

noncomputable def publishTerminal (rules : Rules Address Payload ChildCommand width) (initial : Bank Address Payload width)
    (vote : MediaCrash.AckEvidence (Command Address ChildCommand width)) (applied : Nat)
    (before : Records Address ChildCommand width) (scope : Scope Address) : Option (Scope Address) := by
  classical
  exact if vote.bytesStable = true ∧ vote.nameStable = true ∧
      before ++ [.finish scope] <+: vote.records ∧ before.length < applied ∧ applied ≤ vote.records.length ∧
      (decide rules (before.foldl (apply rules) initial) (.finish scope)).2 = .terminal scope then some scope
      else none

theorem published_retirement_requires_exact_ordered_application_and_both_barriers
    (rules : Rules Address Payload ChildCommand width) (initial : Bank Address Payload width)
    {vote : MediaCrash.AckEvidence (Command Address ChildCommand width)} {applied : Nat}
    {before : Records Address ChildCommand width} {scope accepted : Scope Address}
    (sent : publishTerminal rules initial vote applied before scope = some accepted) :
    MediaCrash.Admissible vote ∧ before ++ [.finish scope] <+: vote.records ∧
      before.length < applied ∧ applied ≤ vote.records.length ∧ accepted = scope ∧
      Terminal rules.provider ((before ++ [Command.finish scope]).foldl (apply rules) initial) scope := by
  simp only [publishTerminal] at sent
  split at sent
  next permitted =>
    cases sent
    refine ⟨⟨permitted.1, permitted.2.1⟩, permitted.2.2.1, permitted.2.2.2.1,
      permitted.2.2.2.2.1, rfl, ?_⟩
    rw [List.foldl_append]
    exact every_positive_terminal_decision_closes_its_exact_scope rules permitted.2.2.2.2.2
  next => simp at sent

noncomputable def exactChosen {Record : Type} (chosen physical : List Record) : Option (List Record) := by
  classical
  exact if chosen <+: physical then some (physical.take chosen.length) else none

theorem intact_frames_beyond_the_authorized_cut_cannot_apply {Record : Type}
    {chosen physical result : List Record}
    (opened : exactChosen chosen physical = some result) :
    result = chosen ∧ chosen <+: physical := by
  simp only [exactChosen] at opened
  split at opened
  next aligned =>
    cases opened
    refine ⟨?_, aligned⟩
    obtain ⟨rest, rfl⟩ := aligned
    exact List.take_append_length
  next => simp at opened

theorem an_intact_later_suffix_still_allows_opening_the_chosen_cut {Record : Type}
    (chosen residue : List Record) :
    exactChosen chosen (chosen ++ residue) = some chosen := by
  have marker : chosen <+: chosen ++ residue := List.prefix_append _ _
  have opened : ∃ result, exactChosen chosen (chosen ++ residue) = some result := by
    rw [exactChosen, ite_eq_left marker]
    exact ⟨_, rfl⟩
  obtain ⟨result, recovered⟩ := opened
  exact (intact_frames_beyond_the_authorized_cut_cannot_apply recovered).1 ▸ recovered

theorem every_legal_media_selector_preserves_the_published_root_frames
    (rules : Rules Address Payload ChildCommand width) (initial : Bank Address Payload width)
    {vote : MediaCrash.AckEvidence (Command Address ChildCommand width)} {applied : Nat}
    {before : Records Address ChildCommand width} {scope accepted : Scope Address}
    (sent : publishTerminal rules initial vote applied before scope = some accepted)
    {rotation : MediaCrash.Rotation} {selector : MediaCrash.Selector}
    (reachable : MediaCrash.Reachable rotation) (allowed : MediaCrash.SelectorAllows rotation selector)
    (captured later : Records Address ChildCommand width) (exactSync : vote.records = captured ++ later)
    (cut : Nat) (inCapture : cut ≤ captured.length) (nameSurvives : Bool)
    (frames residue : List (Option (Command Address ChildCommand width)))
    (persistedBytes : vote.bytesStable = true → frames = vote.records.map some ++ residue)
    (persistedName : vote.nameStable = true → nameSurvives = true) :
    MediaCrash.recover rotation selector captured cut nameSurvives frames =
      some (vote.records ++ MediaCrash.decodePrefix residue) := by
  have durable := (published_retirement_requires_exact_ordered_application_and_both_barriers rules initial sent).1
  exact MediaCrash.acknowledged_records_survive_every_legal_selector vote durable reachable allowed captured later
    exactSync cut inCapture nameSurvives frames residue persistedBytes persistedName

theorem root_recovery_from_any_selected_base_restores_the_current_decisions
    (rules : Rules Address Payload ChildCommand width) (initial checkpoint : Bank Address Payload width)
    {media : JournalRotation.State (Command Address ChildCommand width)} {selected : JournalRotation.View}
    (safe : JournalRotation.Safe media) (tracked : JournalRotation.TracksNamespace media)
    (selectedByCrash : media.namespaceChoices selected)
    (baseState : checkpoint = (media.history.take selected.cut).foldl (apply rules) initial) :
    ∃ tail : Records Address ChildCommand width, tail = media.history.drop selected.cut ∧
      (∀ offset command, tail[offset]? = some command →
        media.media (.tail (selected.cut + offset)) = some [command]) ∧
      tail.foldl (apply rules) checkpoint = media.history.foldl (apply rules) initial := by
  obtain ⟨_, _, frames⟩ := JournalRotation.selectable_has_exact_cut safe ((tracked selected).mp selectedByCrash)
  refine ⟨media.history.drop selected.cut, rfl, ?_, ?_⟩
  · intro offset command saved
    rw [List.getElem?_drop] at saved
    exact frames _ _ (Nat.le_add_right _ _) saved
  · rw [baseState, ← List.foldl_append, List.take_append_drop]

theorem a_published_fence_blocks_old_creation_after_any_recovery_selector
    (rules : Rules Address Payload ChildCommand width) (initial checkpoint : Bank Address Payload width)
    {vote : MediaCrash.AckEvidence (Command Address ChildCommand width)} {applied : Nat}
    {before : Records Address ChildCommand width} {scope accepted : Scope Address}
    (sent : publishTerminal rules initial vote applied before scope = some accepted)
    {mediaAtReply mediaAfter : JournalRotation.State (Command Address ChildCommand width)}
    (lived : JournalRotation.Trace mediaAtReply mediaAfter)
    (exactAtReply : mediaAtReply.history = vote.records)
    (safe : JournalRotation.Safe mediaAtReply) (tracked : JournalRotation.TracksNamespace mediaAtReply)
    {selected : JournalRotation.View} (selectedByCrash : mediaAfter.namespaceChoices selected)
    (baseState : checkpoint = (mediaAfter.history.take selected.cut).foldl (apply rules) initial)
    (index : Fin width) :
    let recovered := (mediaAfter.history.drop selected.cut).foldl (apply rules) checkpoint
    Terminal rules.provider recovered accepted ∧ NamespaceClosure.seedIfLive recovered accepted index = none := by
  obtain ⟨_, ordered, _, _, sameScope, closed⟩ :=
    published_retirement_requires_exact_ordered_application_and_both_barriers rules initial sent
  subst accepted
  obtain ⟨mediaSound, names⟩ := JournalRotation.every_trace_preserves_safety safe tracked lived
  obtain ⟨tail, fromSelected, _, replayed⟩ :=
    root_recovery_from_any_selected_base_restores_the_current_decisions rules initial checkpoint mediaSound names
      selectedByCrash baseState
  obtain ⟨extension, fullHead⟩ := JournalRotation.trace_extends_history lived
  have covers : before ++ [Command.finish scope] <+: mediaAfter.history := by
    rw [fullHead, exactAtReply]
    exact ordered.trans (List.prefix_append _ _)
  obtain ⟨later, splitHead⟩ := covers
  have full := root_replay_is_a_namespace_trace rules
    ((before ++ [Command.finish scope]).foldl (apply rules) initial) later
  have terminal := NamespaceClosure.terminal_evidence_keeps_the_original_scope_after_replacement closed full
  have refusal := (NamespaceClosure.a_terminal_namespace_rejects_late_creates_across_restart_and_reuse
    closed.1 full index).2
  change Terminal rules.provider ((mediaAfter.history.drop selected.cut).foldl (apply rules) checkpoint) scope ∧ _
  rw [← fromSelected, replayed, ← splitHead, List.foldl_append]
  exact ⟨terminal, refusal⟩

#print axioms every_root_record_stutters_or_uses_the_namespace_reducer
#print axioms every_positive_terminal_decision_closes_its_exact_scope
#print axioms root_replay_is_a_namespace_trace
#print axioms published_retirement_requires_exact_ordered_application_and_both_barriers
#print axioms intact_frames_beyond_the_authorized_cut_cannot_apply
#print axioms an_intact_later_suffix_still_allows_opening_the_chosen_cut
#print axioms every_legal_media_selector_preserves_the_published_root_frames
#print axioms root_recovery_from_any_selected_base_restores_the_current_decisions
#print axioms a_published_fence_blocks_old_creation_after_any_recovery_selector

end DurableRoot
