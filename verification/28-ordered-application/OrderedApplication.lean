import PrefixAgreement

set_option warningAsError true

namespace OrderedApplication

open Kernel

inductive Command (Payload : Type) where
  | append (writer : Writer) (expectedLsn : Nat) (payload : Payload)
  | fence (expectedWriter successor : Writer)
  | withdraw (writer : Writer)
  | freeze (writer : Writer) (target : Placement)
  | activate (target : Placement) (priorWriter : Writer) (installed : List (Entry Payload))
  | retire (writer : Writer)
  | checkpoint (writer : Writer) (cut : Nat)
  | trim (writer : Writer) (cut : Nat)
  | prepareReplay (writer : Writer) (firstLsn : Nat)
  | admitReplay (writer : Writer) (id firstLsn : Nat)
  | releaseReplay (id : Nat)
  | read (writer : Writer) (nonce : Nat)

inductive Outcome (Payload : Type) where
  | refused
  | appended (lsn : Nat) (entry : Entry Payload)
  | installed (cut : Nat)
  | replayPrepared (id : Nat)
  | replayChanged
  | readCut (nonce cut : Nat)

def AppendAllowed (limits : Limits) (state : State Payload) (writer : Writer) (lsn : Nat) : Prop :=
  state.authority = .active writer ∧
  lsn = state.history.length ∧
  state.history.length + 1 - state.checkpointEnd ≤ limits.recovery ∧
  state.history.length + 1 - state.firstRetained ≤ limits.retained

theorem append_guard_is_kernel_admission {limits : Limits} {state : State Payload}
    {writer : Writer} {lsn : Nat} (allowed : AppendAllowed limits state writer lsn) :
    AppendAdmissible limits state writer lsn := by
  have writerMatches : state.authority = .active writer := by
    exact allowed.1
  have lsnMatches : lsn = state.history.length := by
    exact allowed.2.1
  exact ⟨writerMatches, lsnMatches, allowed.2.2.1, allowed.2.2.2⟩

noncomputable def decideCommand (limits : Limits) (state : State Payload) :
    Command Payload → State Payload × Outcome Payload := by
  classical
  exact fun command =>
    match command with
    | .append writer lsn payload =>
        if AppendAllowed limits state writer lsn then
          let entry : Entry Payload := ⟨writer.epoch, payload⟩
          ({state with history := state.history ++ [entry]}, .appended lsn entry)
        else (state, .refused)
    | .fence expected successor =>
        if AtWriter state.authority expected ∧ successor.placement = expected.placement ∧
            expected.epoch < successor.epoch then
          ({state with authority := .active successor}, .installed state.history.length)
        else (state, .refused)
    | .withdraw writer =>
        if state.authority = .active writer then
          ({state with authority := .vacant writer}, .installed state.history.length)
        else (state, .refused)
    | .freeze writer target =>
        if state.authority = .active writer ∧ writer.placement.generation < target.generation ∧
            writer.placement.group ≠ target.group then
          ({state with authority := .sealed target writer}, .installed state.history.length)
        else (state, .refused)
    | .activate target prior installed =>
        if state.authority = .sealed target prior ∧ installed = state.history then
          ({state with history := installed, authority := .active {prior with placement := target}},
            .installed installed.length)
        else (state, .refused)
    | .retire writer =>
        if AtWriter state.authority writer then
          ({state with authority := .retired}, .installed state.history.length)
        else (state, .refused)
    | .checkpoint writer cut =>
        if state.authority = .active writer ∧ state.checkpointEnd ≤ cut ∧ cut ≤ state.history.length then
          ({state with checkpointEnd := cut}, .installed cut)
        else (state, .refused)
    | .trim writer cut =>
        if state.authority = .active writer ∧ state.firstRetained ≤ cut ∧ cut ≤ state.checkpointEnd ∧
            (∀ id lsn, state.replays id = .holding lsn → cut ≤ lsn) then
          ({state with firstRetained := cut}, .installed cut)
        else (state, .refused)
    | .prepareReplay writer firstLsn =>
        if state.authority = .active writer then
          let id := state.replayIssued + 1
          ({state with replayIssued := id, replays := replaceReplay state.replays id (.prepared firstLsn)},
            .replayPrepared id)
        else (state, .refused)
    | .admitReplay writer id firstLsn =>
        if state.authority = .active writer ∧ state.replays id = .prepared firstLsn ∧
            state.firstRetained ≤ firstLsn ∧ firstLsn < state.history.length then
          ({state with replays := replaceReplay state.replays id (.holding firstLsn)}, .replayChanged)
        else (state, .refused)
    | .releaseReplay id =>
        if id ≤ state.replayIssued then
          ({state with replays := replaceReplay state.replays id .unused}, .replayChanged)
        else (state, .refused)
    | .read writer nonce =>
        (state, match barrier state writer with
          | some cut => .readCut nonce cut
          | none => .refused)

theorem decision_projects_to_kernel {limits : Limits} {state : State Payload}
    (command : Command Payload) :
    let after := (decideCommand limits state command).1
    state = after ∨ Step limits state after := by
  cases command with
  | append writer lsn payload =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.append lsn payload (append_guard_is_kernel_admission allowed))
      next => exact Or.inl rfl
  | fence expected successor =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.fenceWriter successor allowed.1 allowed.2.1 allowed.2.2)
      next => exact Or.inl rfl
  | withdraw writer =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.withdrawWriter allowed)
      next => exact Or.inl rfl
  | freeze writer target =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.freeze target allowed.1 allowed.2.1 allowed.2.2)
      next => exact Or.inl rfl
  | activate target prior installed =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.activate installed allowed.1 allowed.2)
      next => exact Or.inl rfl
  | retire writer =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.retire allowed)
      next => exact Or.inl rfl
  | checkpoint writer cut =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.publish cut allowed.1 allowed.2.1 allowed.2.2)
      next => exact Or.inl rfl
  | trim writer cut =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.trim cut allowed.1 allowed.2.1 allowed.2.2.1 allowed.2.2.2)
      next => exact Or.inl rfl
  | prepareReplay writer lsn =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.prepareReplay lsn allowed)
      next => exact Or.inl rfl
  | admitReplay writer id lsn =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.admitReplay id lsn allowed.1 allowed.2.1 allowed.2.2.1 allowed.2.2.2)
      next => exact Or.inl rfl
  | releaseReplay id =>
      simp only [decideCommand]
      split
      next allowed => exact Or.inr (.releaseReplay id allowed)
      next => exact Or.inl rfl
  | read => exact Or.inl rfl

theorem refused_command_preserves_state {limits : Limits} {state : State Payload}
    {command : Command Payload} (refused : (decideCommand limits state command).2 = .refused) :
    (decideCommand limits state command).1 = state := by
  cases command <;> simp only [decideCommand] at refused ⊢ <;>
    first
    | rfl
    | (split
       next allowed => simp only [ite_eq_left allowed] at refused; cases refused
       next => rfl)

theorem every_kernel_step_has_an_ordered_command {limits : Limits} {before after : State Payload}
    (step : Step limits before after) :
    ∃ command, (decideCommand limits before command).1 = after ∧
      (decideCommand limits before command).2 ≠ .refused := by
  cases step with
  | append lsn bytes admitted =>
      rename_i writer
      have allowed : AppendAllowed limits before writer lsn :=
        ⟨admitted.authorized, admitted.ordered, admitted.recoveryRoom, admitted.retainedRoom⟩
      exact ⟨.append writer lsn bytes, by simp [decideCommand, allowed]⟩
  | withdrawWriter authorized =>
      rename_i writer
      exact ⟨.withdraw writer, by simp [decideCommand, authorized]⟩
  | fenceWriter successor authorized samePlacement higher =>
      rename_i writer
      exact ⟨.fence writer successor, by simp [decideCommand, authorized, samePlacement, higher]⟩
  | freeze target authorized advances relocates =>
      rename_i writer
      exact ⟨.freeze writer target, by simp [decideCommand, authorized, advances, relocates]⟩
  | activate installed sealed exactCut =>
      rename_i target writer
      exact ⟨.activate target writer installed, by simp [decideCommand, sealed, exactCut]⟩
  | retire authorized =>
      rename_i writer
      exact ⟨.retire writer, by simp [decideCommand, authorized]⟩
  | publish cut authorized advances committed =>
      rename_i writer
      exact ⟨.checkpoint writer cut, by simp [decideCommand, authorized, advances, committed]⟩
  | trim cut authorized advances published protects =>
      rename_i writer
      have allowed : before.authority = .active writer ∧ before.firstRetained ≤ cut ∧
          cut ≤ before.checkpointEnd ∧ (∀ id lsn, before.replays id = .holding lsn → cut ≤ lsn) :=
        ⟨authorized, advances, published, protects⟩
      exact ⟨.trim writer cut, by rw [decideCommand, ite_eq_left allowed]; simp⟩
  | prepareReplay firstLsn authorized =>
      rename_i writer
      exact ⟨.prepareReplay writer firstLsn, by simp [decideCommand, authorized]⟩
  | admitReplay id firstLsn authorized reserved available contains =>
      rename_i writer
      exact ⟨.admitReplay writer id firstLsn,
        by simp [decideCommand, authorized, reserved, available, contains]⟩
  | releaseReplay id issued =>
      exact ⟨.releaseReplay id, by simp [decideCommand, issued]⟩

noncomputable def replay (limits : Limits) (state : State Payload) :
    List (Command Payload) → State Payload × List (Outcome Payload)
  | [] => (state, [])
  | command :: rest =>
      let decision := decideCommand limits state command
      let continued := replay limits decision.1 rest
      (continued.1, decision.2 :: continued.2)

theorem replay_append (limits : Limits) (state : State Payload)
    (before after : List (Command Payload)) :
    replay limits state (before ++ after) =
      let prefixRun := replay limits state before
      let suffixRun := replay limits prefixRun.1 after
      (suffixRun.1, prefixRun.2 ++ suffixRun.2) := by
  induction before generalizing state with
  | nil => simp [replay]
  | cons command rest prior =>
      simp only [List.cons_append, replay]
      rw [prior]

theorem exactly_one_outcome_per_command (limits : Limits) (state : State Payload)
    (commands : List (Command Payload)) : (replay limits state commands).2.length = commands.length := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest prior => simp [replay, prior]

private theorem trace_trans {limits : Limits} {first middle last : State Payload}
    (earlier : Trace limits first middle) (later : Trace limits middle last) :
    Trace limits first last := by
  induction later with
  | same => exact earlier
  | next _ final prior => exact .next prior final

theorem replay_projects_to_kernel (limits : Limits) (state : State Payload)
    (commands : List (Command Payload)) : Trace limits state (replay limits state commands).1 := by
  induction commands generalizing state with
  | nil => exact .same _
  | cons command rest prior =>
      have projected : Trace limits state (decideCommand limits state command).1 := by
        rcases decision_projects_to_kernel (limits := limits) (state := state) command with same | one
        · rw [← same]
          exact .same _
        · exact .next (.same _) one
      exact trace_trans projected (prior (decideCommand limits state command).1)

theorem replay_preserves_kernel_bounds {limits : Limits} {state : State Payload}
    (valid : Valid limits state) (commands : List (Command Payload)) :
    Valid limits (replay limits state commands).1 :=
  every_trace_preserves_bounds valid (replay_projects_to_kernel limits state commands)

theorem outcomes_extend_with_commands (limits : Limits) (state : State Payload)
    {earlier later : List (Command Payload)} (extendsHistory : earlier <+: later) :
    (replay limits state earlier).2 <+: (replay limits state later).2 := by
  obtain ⟨suffix, rfl⟩ := extendsHistory
  rw [replay_append]
  exact List.prefix_append _ _

theorem certified_replicas_agree_on_application {ledger : PrefixAgreement.Ledger Voter (Command Payload)}
    (rules : PrefixAgreement.Rules ledger) (limits : Limits) (initial : State Payload)
    {first second : Nat} {earlier later : List (Command Payload)}
    (left : PrefixAgreement.Chosen ledger first earlier)
    (right : PrefixAgreement.Chosen ledger second later) :
    (replay limits initial earlier).2 <+: (replay limits initial later).2 ∨
    (replay limits initial later).2 <+: (replay limits initial earlier).2 := by
  rcases PrefixAgreement.every_chosen_prefix_agrees rules left right with same | same
  · exact Or.inl (outcomes_extend_with_commands limits initial same)
  · exact Or.inr (outcomes_extend_with_commands limits initial same)

private theorem lookup_extends {earlier later : List Value} {position : Nat} {value : Value}
    (prefixProof : earlier <+: later) (found : earlier[position]? = some value) :
    later[position]? = some value := by
  obtain ⟨suffix, rfl⟩ := prefixProof
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem certified_slots_bind_exact_command_and_outcome
    {ledger : PrefixAgreement.Ledger Voter (Command Payload)} (rules : PrefixAgreement.Rules ledger)
    (limits : Limits) (initial : State Payload) {first second position : Nat}
    {earlier later : List (Command Payload)} {leftRequest rightRequest : Command Payload}
    {leftResult rightResult : Outcome Payload}
    (left : PrefixAgreement.Chosen ledger first earlier)
    (right : PrefixAgreement.Chosen ledger second later)
    (leftAt : earlier[position]? = some leftRequest) (rightAt : later[position]? = some rightRequest)
    (leftApplied : (replay limits initial earlier).2[position]? = some leftResult)
    (rightApplied : (replay limits initial later).2[position]? = some rightResult) :
    leftRequest = rightRequest ∧ leftResult = rightResult := by
  refine ⟨PrefixAgreement.any_two_certificates_agree_at_position rules left right leftAt rightAt, ?_⟩
  rcases certified_replicas_agree_on_application rules limits initial left right with inside | reverse
  · exact Option.some.inj ((lookup_extends inside leftApplied).symm.trans rightApplied)
  · exact Option.some.inj (leftApplied.symm.trans (lookup_extends reverse rightApplied))

theorem successful_append_binds_exact_request {limits : Limits} {state : State Payload}
    {writer : Writer} {expected lsn : Nat} {payload : Payload} {entry : Entry Payload}
    (valid : Valid limits state)
    (outcome : (decideCommand limits state (.append writer expected payload)).2 = .appended lsn entry) :
    state.authority = .active writer ∧ lsn = expected ∧ entry = ⟨writer.epoch, payload⟩ ∧
    MatchesReceipt (decideCommand limits state (.append writer expected payload)).1 lsn entry := by
  simp only [decideCommand] at outcome ⊢
  split at outcome
  next allowed =>
    have admitted := append_guard_is_kernel_admission allowed
    have exactFields := Outcome.appended.inj outcome
    obtain ⟨rfl, rfl⟩ := exactFields
    rw [ite_eq_left allowed]
    refine ⟨admitted.authorized, rfl, rfl, ?_⟩
    rw [admitted.ordered]
    refine ⟨Nat.le_trans valid.trimCertified valid.checkpointCommitted, ?_⟩
    simp
  next => cases outcome

theorem superseded_writer_command_is_refused {limits : Limits} {state : State Payload}
    {writer : Writer} (unauthorized : state.authority ≠ .active writer) (lsn : Nat) (payload : Payload) :
    decideCommand limits state (.append writer lsn payload) = (state, .refused) := by
  have denied : ¬ AppendAllowed limits state writer lsn := fun allowed =>
    unauthorized (append_guard_is_kernel_admission allowed).authorized
  simp only [decideCommand, ite_eq_right denied]

theorem applied_read_reports_exact_cut {limits : Limits} {state : State Payload}
    {writer : Writer} {nonce responseNonce cut : Nat}
    (outcome : (decideCommand limits state (.read writer nonce)).2 = .readCut responseNonce cut) :
    responseNonce = nonce ∧ state.authority = .active writer ∧ cut = state.history.length := by
  simp only [decideCommand] at outcome
  split at outcome
  next exactCut known =>
    have fields := Outcome.readCut.inj outcome
    obtain ⟨rfl, rfl⟩ := fields
    exact ⟨rfl, barrier_reports_committed_end known⟩
  next => cases outcome

theorem ordered_read_survives_later_certificates
    {ledger : PrefixAgreement.Ledger Voter (Command Payload)} (rules : PrefixAgreement.Rules ledger)
    (limits : Limits) (initial : State Payload) (preceding observed : List (Command Payload))
    (writer : Writer) (nonce cut invokedAt markerBallot observedBallot : Nat)
    (ordered : PrefixAgreement.Chosen ledger markerBallot (preceding ++ [.read writer nonce]))
    (delivered : PrefixAgreement.Chosen ledger observedBallot observed)
    (outcome : (decideCommand limits (replay limits initial preceding).1 (.read writer nonce)).2 =
      .readCut nonce cut)
    (afterInvoke : invokedAt ≤ preceding.length) (beforeReply : preceding.length < observed.length) :
    invokedAt < preceding.length + 1 ∧ preceding.length + 1 ≤ observed.length ∧
      (replay limits initial observed).2[preceding.length]? = some (.readCut nonce cut) ∧
      (replay limits initial preceding).1.authority = .active writer ∧
      cut = (replay limits initial preceding).1.history.length := by
  have markerFound :
      (replay limits initial (preceding ++ [.read writer nonce])).2[preceding.length]? =
        some (.readCut nonce cut) := by
    rw [replay_append]
    simp [exactly_one_outcome_per_command, replay, outcome]
  have longEnough : (preceding ++ [Command.read writer nonce]).length ≤ observed.length := by
    simpa using Nat.succ_le_of_lt beforeReply
  have orderedPart : preceding ++ [.read writer nonce] <+: observed := by
    rcases PrefixAgreement.every_chosen_prefix_agrees rules ordered delivered with contains | reverse
    · exact contains
    · rw [reverse.eq_of_length_le longEnough]
      exact List.prefix_rfl
  have originalOutcome :
      (replay limits initial observed).2[preceding.length]? = some (.readCut nonce cut) :=
    lookup_extends (outcomes_extend_with_commands limits initial orderedPart) markerFound
  exact ⟨by omega, Nat.succ_le_of_lt beforeReply, originalOutcome,
    (applied_read_reports_exact_cut outcome).2⟩

#print axioms append_guard_is_kernel_admission
#print axioms decision_projects_to_kernel
#print axioms refused_command_preserves_state
#print axioms every_kernel_step_has_an_ordered_command
#print axioms replay_append
#print axioms exactly_one_outcome_per_command
#print axioms replay_projects_to_kernel
#print axioms replay_preserves_kernel_bounds
#print axioms outcomes_extend_with_commands
#print axioms certified_replicas_agree_on_application
#print axioms certified_slots_bind_exact_command_and_outcome
#print axioms successful_append_binds_exact_request
#print axioms superseded_writer_command_is_refused
#print axioms applied_read_reports_exact_cut
#print axioms ordered_read_survives_later_certificates

end OrderedApplication
