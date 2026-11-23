import FundedSeal
import SourceOutcomes
import OrderedApplication
import SettlementComposition

set_option warningAsError true

namespace UnifiedSource

variable {width : Nat} {Pool Payload Ticket : Type}

abbrev MoveBook (width : Nat) (Pool : Type) :=
  SourceOutcomes.Book width (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool)

abbrev Receipt (width : Nat) (Pool : Type) := SettlementComposition.Receipt width Pool

abbrev Participants (Pool : Type) := List (SettlementComposition.Participant Pool)

structure Anchor (width : Nat) (Pool : Type) where
  decision : SourceOutcomes.Decision width (FundedSeal.Intent Pool)
  position : Nat

structure Installation (width : Nat) (Pool Payload Ticket : Type) where
  anchor : Anchor width Pool
  writer : Kernel.Writer
  history : List (Kernel.Entry Payload)
  evidence : Ticket

structure Core (width : Nat) (Pool Payload : Type) where
  stream : Kernel.State Payload
  book : MoveBook width Pool
  pending : Option (SourceOutcomes.Key width)
  handoff : Option (Anchor width Pool)

structure State (width : Nat) (Pool Payload : Type) where
  core : Core width Pool Payload
  position : Nat

structure Rules (width : Nat) (Pool Payload Ticket : Type) where
  plan : SourceOutcomes.Key width → FundedSeal.Intent Pool → Participants Pool → Prop
  preparedReceipt : FundedSeal.Receipt Pool → Prop
  settledReceipt : Receipt width Pool → Ticket → Prop
  installed : Installation width Pool Payload Ticket → Prop

inductive Command (width : Nat) (Pool Payload Ticket : Type) where
  | stream (command : OrderedApplication.Command Payload)
  | reserve (key : SourceOutcomes.Key width) (intent : FundedSeal.Intent Pool)
      (participants : Participants Pool)
  | cancel (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
  | fundedSeal (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
      (receipts : List (FundedSeal.Receipt Pool))
  | retire (writer : Kernel.Writer)
  | activate (installation : Installation width Pool Payload Ticket)
  | acknowledge (receipt : Receipt width Pool) (evidence : Option Ticket)
  | compact (key : SourceOutcomes.Key width)

inductive Reply (Payload : Type) where
  | refused
  | accepted
  | stream (response : OrderedApplication.Outcome Payload)

def Routine : OrderedApplication.Command Payload → Prop
  | .freeze .. | .activate .. | .retire .. => False
  | .append .. | .fence .. | .withdraw .. | .checkpoint .. | .trim .. | .prepareReplay .. |
    .admitReplay .. | .releaseReplay .. | .read .. => True

def Ready (core : Core width Pool Payload) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool)) : Prop :=
  core.pending = some key ∧ SourceOutcomes.lookup core.book key = some row ∧ row.result = none

def terminal (core : Core width Pool Payload) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (result : SourceOutcomes.Resolution) :
    Core width Pool Payload :=
  {core with
    pending := none
    book := SourceOutcomes.setRow core.book key.slot (some {row with result := some result})}

def full (rules : Rules width Pool Payload Ticket) (receipts : List (FundedSeal.Receipt Pool))
    (intent : FundedSeal.Intent Pool) : Prop :=
  FundedSeal.FullVector (fun receipt => receipt ∈ receipts ∧ rules.preparedReceipt receipt) intent

def SameInstallation (proof : Installation width Pool Payload Ticket) (handoff : Anchor width Pool) : Prop :=
  proof.anchor.decision = handoff.decision ∧ proof.anchor.position = handoff.position

def AcceptsReceipt (rules : Rules width Pool Payload Ticket)
    (receipt : Receipt width Pool) (attachment : Option Ticket) : Prop :=
  ∃ token, attachment = some token ∧ rules.settledReceipt receipt token

private theorem accepted_receipt_has_an_ordered_attachment
    {rules : Rules width Pool Payload Ticket} {receipt : Receipt width Pool} {attachment : Option Ticket}
    (eligible : AcceptsReceipt rules receipt attachment) : ∃ token, attachment = some token := by
  obtain ⟨token, attached, _⟩ := eligible
  exact ⟨token, attached⟩

private theorem installation_checks_ordered_position {proof : Installation width Pool Payload Ticket}
    {handoff : Anchor width Pool} (matched : SameInstallation proof handoff) :
    proof.anchor.position = handoff.position := by
  exact matched.2

private noncomputable def changeLifecycle (core : Core width Pool Payload)
    (key : SourceOutcomes.Key width)
    (action : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool) →
      Core width Pool Payload × Reply Payload) : Core width Pool Payload × Reply Payload := by
  classical
  exact match SourceOutcomes.lookup core.book key with
  | none => (core, .refused)
  | some row => if Ready core key row then action row else (core, .refused)

noncomputable def decide (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat) :
    Command width Pool Payload Ticket → Core width Pool Payload × Reply Payload := by
  classical
  exact fun command => match command with
  | .stream command =>
      if Routine command then
        let next := OrderedApplication.decideCommand limits core.stream command
        ({core with stream := next.1}, .stream next.2)
      else (core, .refused)
  | .reserve key intent participants =>
      if FundedSeal.Serving core.stream ∧ core.pending = none ∧ core.book.rows key.slot = none ∧
          key.serial = core.book.issued + 1 ∧ intent.serial = key.serial ∧ rules.plan key intent participants then
        let book := SourceOutcomes.setRow core.book key.slot (some ⟨key.serial, intent, none, participants⟩)
        ({core with pending := some key, book := {book with issued := key.serial}}, .accepted)
      else (core, .refused)
  | .cancel writer key =>
      if core.stream.authority = .active writer then
        changeLifecycle core key fun row => (terminal core key row .canceled, .accepted)
      else (core, .refused)
  | .fundedSeal writer key receipts =>
      changeLifecycle core key fun row =>
        if core.stream.authority = .active writer ∧
            writer.placement.generation < row.binding.target.generation ∧
            writer.placement.group ≠ row.binding.target.group ∧ full rules receipts row.binding then
          ({terminal core key row .committed with
            stream := {core.stream with authority := .sealed row.binding.target writer}
            handoff := some ⟨⟨key, row.binding, .committed⟩, position⟩}, .accepted)
        else (core, .refused)
  | .retire writer =>
      if Kernel.AtWriter core.stream.authority writer then
        let closed := {core.stream with authority := .retired}
        match core.pending with
        | none => ({core with stream := closed}, .accepted)
        | some key =>
            changeLifecycle core key fun row => ({terminal core key row .canceled with stream := closed}, .accepted)
      else (core, .refused)
  | .activate proof =>
      match core.handoff with
      | none => (core, .refused)
      | some handoff =>
          let placement := handoff.decision.binding.target
          if SameInstallation proof handoff ∧ rules.installed proof ∧
              core.stream.authority = .sealed placement proof.writer ∧ proof.history = core.stream.history then
            ({core with
              handoff := none
              stream := {core.stream with
                history := proof.history
                authority := .active {proof.writer with placement := placement}}}, .accepted)
          else (core, .refused)
  | .acknowledge receipt attachment =>
      match SourceOutcomes.lookup core.book receipt.decision.key with
      | none => (core, .refused)
      | some row =>
          if row.binding = receipt.decision.binding ∧ row.result = some receipt.decision.result ∧
              AcceptsReceipt rules receipt attachment then
            let remaining := row.waiting.filter (fun participant => if participant = receipt.participant then false else true)
            let book := SourceOutcomes.setRow core.book receipt.decision.key.slot (some {row with waiting := remaining})
            ({core with book := book}, .accepted)
          else (core, .refused)
  | .compact key =>
      match SourceOutcomes.lookup core.book key with
      | none => (core, .refused)
      | some row =>
          if SourceOutcomes.MayCompact row then
            ({core with book := SourceOutcomes.setRow core.book key.slot none}, .accepted)
          else (core, .refused)

private theorem lifecycle_projects (limits : Kernel.Limits)
    (core : Core width Pool Payload) (key : SourceOutcomes.Key width)
    (action : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool) →
      Core width Pool Payload × Reply Payload)
    (projects : ∀ row, core.stream = (action row).1.stream ∨ Kernel.Step limits core.stream (action row).1.stream) :
    core.stream = (changeLifecycle core key action).1.stream ∨
      Kernel.Step limits core.stream (changeLifecycle core key action).1.stream := by
  unfold changeLifecycle
  split
  · exact .inl rfl
  · split
    · exact projects _
    · exact .inl rfl

theorem a_joint_command_projects_to_the_stream
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat) (command : Command width Pool Payload Ticket) :
    let after := (decide limits rules core position command).1.stream
    core.stream = after ∨ Kernel.Step limits core.stream after := by
  dsimp only
  cases command with
  | stream command =>
      simp only [decide]
      split
      · exact OrderedApplication.decision_projects_to_kernel command
      · exact .inl rfl
  | reserve =>
      simp only [decide]
      split <;> exact .inl rfl
  | cancel =>
      simp only [decide]
      split
      · exact lifecycle_projects limits core _ _ (fun _ => .inl rfl)
      · exact .inl rfl
  | fundedSeal writer key receipts =>
      simp only [decide]
      apply lifecycle_projects limits core key
      intro row
      split
      next eligible => exact .inr (.freeze row.binding.target eligible.1 eligible.2.1 eligible.2.2.1)
      next => exact .inl rfl
  | retire writer =>
      simp only [decide]
      split
      next allowed =>
        split
        · exact .inr (.retire allowed)
        · exact lifecycle_projects limits core _ _ (fun _ => .inr (.retire allowed))
      next => exact .inl rfl
  | activate install =>
      simp only [decide]
      split
      · exact .inl rfl
      · split
        next eligible => exact .inr (.activate install.history eligible.2.2.1 eligible.2.2.2)
        next => exact .inl rfl
  | acknowledge =>
      simp only [decide]
      split
      · exact .inl rfl
      · split <;> exact .inl rfl
  | compact =>
      simp only [decide]
      split
      · exact .inl rfl
      · split <;> exact .inl rfl

theorem missing_ordered_evidence_is_a_refusal
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat) (receipt : Receipt width Pool) :
    decide limits rules core position (.acknowledge receipt none) = (core, .refused) := by
  have absent : ¬ AcceptsReceipt rules receipt none := by
    intro eligible
    obtain ⟨_, impossible⟩ := accepted_receipt_has_an_ordered_attachment eligible
    cases impossible
  cases found : SourceOutcomes.lookup core.book receipt.decision.key <;>
    simp [decide, found, absent]

def withSettlements {ProviderTicket Voter : Type} (rules : Rules width Pool Payload Ticket)
    (openCertificate : Ticket → SettlementComposition.Evidence width Pool ProviderTicket Payload Voter) :
    Rules width Pool Payload Ticket :=
  {rules with settledReceipt := fun receipt certificate =>
    SettlementComposition.Settled (openCertificate certificate) receipt}

theorem a_certified_physical_settlement_is_applied_from_its_ordered_attachment
    {ProviderTicket Voter : Type} (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (openCertificate : Ticket → SettlementComposition.Evidence width Pool ProviderTicket Payload Voter)
    (core : Core width Pool Payload) (position : Nat) (receipt : Receipt width Pool) (certificate : Ticket)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (found : SourceOutcomes.lookup core.book receipt.decision.key = some row)
    (binding : row.binding = receipt.decision.binding) (resolved : row.result = some receipt.decision.result)
    (physical : SettlementComposition.Settled (openCertificate certificate) receipt) :
    (decide limits (withSettlements rules openCertificate) core position
      (.acknowledge receipt (some certificate))).2 = .accepted := by
  have attached : AcceptsReceipt (withSettlements rules openCertificate) receipt (some certificate) :=
    ⟨certificate, by trivial, physical⟩
  simp [decide, found, binding, resolved, attached]

theorem ordinary_commands_cannot_freeze_the_source
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat) (writer : Kernel.Writer) (target : Kernel.Placement) :
    decide limits rules core position (.stream (.freeze writer target)) = (core, .refused) := by
  simp [decide, Routine]

theorem decide_funded_seal_accepts_the_exact_pending_row
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (receipts : List (FundedSeal.Receipt Pool)) (ready : Ready core key row)
    (authorized : core.stream.authority = .active writer)
    (advances : writer.placement.generation < row.binding.target.generation)
    (relocates : writer.placement.group ≠ row.binding.target.group) (funded : full rules receipts row.binding) :
    decide limits rules core position (.fundedSeal writer key receipts) =
      ({terminal core key row .committed with
        stream := {core.stream with authority := .sealed row.binding.target writer}
        handoff := some ⟨⟨key, row.binding, .committed⟩, position⟩}, .accepted) := by
  have eligible : core.stream.authority = .active writer ∧
      writer.placement.generation < row.binding.target.generation ∧
      writer.placement.group ≠ row.binding.target.group ∧ full rules receipts row.binding :=
    ⟨authorized, advances, relocates, funded⟩
  simp only [decide, changeLifecycle, ready.2.1, ite_eq_left ready, ite_eq_left eligible]

theorem a_successful_funded_seal_records_both_effects_at_one_position
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (receipts : List (FundedSeal.Receipt Pool)) (ready : Ready core key row)
    (authorized : core.stream.authority = .active writer)
    (advances : writer.placement.generation < row.binding.target.generation)
    (relocates : writer.placement.group ≠ row.binding.target.group) (funded : full rules receipts row.binding) :
    let after := (decide limits rules core position (.fundedSeal writer key receipts)).1
    after.stream.authority = .sealed row.binding.target writer ∧
      SourceOutcomes.lookup after.book key = some {row with result := some .committed} ∧
      after.handoff = some ⟨⟨key, row.binding, .committed⟩, position⟩ := by
  have serial := (Option.filter_eq_some_iff.mp ready.2.1).2
  rw [decide_funded_seal_accepts_the_exact_pending_row limits rules core position writer key row receipts
    ready authorized advances relocates funded]
  simp [terminal, SourceOutcomes.lookup, SourceOutcomes.setRow, serial]

theorem a_prepared_retirement_records_its_abort_at_the_same_position
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (ready : Ready core key row)
    (authorized : Kernel.AtWriter core.stream.authority writer) :
    let after := (decide limits rules core position (.retire writer)).1
    after.stream.authority = .retired ∧
      SourceOutcomes.lookup after.book key = some {row with result := some .canceled} := by
  have serial := (Option.filter_eq_some_iff.mp ready.2.1).2
  simp only [decide, ite_eq_left authorized,
    ready.1, changeLifecycle, ready.2.1, ite_eq_left ready]
  simp [terminal, SourceOutcomes.lookup, SourceOutcomes.setRow, serial]

theorem a_prepared_cancellation_records_its_exact_abort
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (ready : Ready core key row)
    (authorized : core.stream.authority = .active writer) :
    SourceOutcomes.lookup (decide limits rules core position (.cancel writer key)).1.book key =
      some {row with result := some .canceled} := by
  have serial := (Option.filter_eq_some_iff.mp ready.2.1).2
  simp only [decide, ite_eq_left authorized, changeLifecycle, ready.2.1, ite_eq_left ready]
  simp [terminal, SourceOutcomes.lookup, SourceOutcomes.setRow, serial]

theorem a_decided_move_refuses_a_delivered_seal
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat) (writer : Kernel.Writer)
    (key : SourceOutcomes.Key width) (receipts : List (FundedSeal.Receipt Pool))
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (found : SourceOutcomes.lookup core.book key = some row)
    (decided : row.result ≠ none) :
    decide limits rules core position (.fundedSeal writer key receipts) = (core, .refused) := by
  have notReady : ¬ Ready core key row := fun eligible => decided eligible.2.2
  simp [decide, changeLifecycle, found, notReady]

theorem installation_rejects_a_different_ordered_seal_position
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (core : Core width Pool Payload) (position : Nat)
    (installation : Installation width Pool Payload Ticket) (handoff : Anchor width Pool)
    (present : core.handoff = some handoff) (different : installation.anchor.position ≠ handoff.position) :
    decide limits rules core position (.activate installation) = (core, .refused) := by
  have mismatched : ¬ SameInstallation installation handoff :=
    fun matched => different (installation_checks_ordered_position matched)
  simp [decide, present, mismatched]

noncomputable def replay (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (initial : State width Pool Payload) :
    List (Command width Pool Payload Ticket) → State width Pool Payload × List (Reply Payload)
  | [] => (initial, [])
  | command :: rest =>
      let next := decide limits rules initial.core (initial.position + 1) command
      let remaining := replay limits rules ⟨next.1, initial.position + 1⟩ rest
      (remaining.1, next.2 :: remaining.2)

private theorem prepend_step {limits : Kernel.Limits} {first second last : Kernel.State Payload}
    (step : Kernel.Step limits first second) (trace : Kernel.Trace limits second last) :
    Kernel.Trace limits first last := by
  induction trace with
  | same => exact .next (.same _) step
  | next _ transition prior => exact .next prior transition

theorem a_joint_history_projects_to_the_stream_trace
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (initial : State width Pool Payload) (commands : List (Command width Pool Payload Ticket)) :
    Kernel.Trace limits initial.core.stream (replay limits rules initial commands).1.core.stream := by
  induction commands generalizing initial with
  | nil => exact .same _
  | cons command remaining prior =>
      let next := (decide limits rules initial.core (initial.position + 1) command).1
      have tail := prior ⟨next, initial.position + 1⟩
      rcases a_joint_command_projects_to_the_stream limits rules initial.core (initial.position + 1) command with
        equal | transition
      · exact equal.symm ▸ tail
      · exact prepend_step transition tail

theorem replay_append (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (initial : State width Pool Payload) (earlier suffix : List (Command width Pool Payload Ticket)) :
    replay limits rules initial (earlier ++ suffix) =
      let applied := replay limits rules initial earlier
      let later := replay limits rules applied.1 suffix
      (later.1, applied.2 ++ later.2) := by
  induction earlier generalizing initial with
  | nil => simp [replay]
  | cons command remaining prior =>
      simp only [List.cons_append, replay]
      rw [prior]

theorem a_certified_joint_checkpoint_replays_the_same_tail
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (initial checkpoint : State width Pool Payload)
    (earlier suffix : List (Command width Pool Payload Ticket))
    (certified : checkpoint = (replay limits rules initial earlier).1) :
    replay limits rules checkpoint suffix =
      ((replay limits rules initial (earlier ++ suffix)).1,
        (replay limits rules initial (earlier ++ suffix)).2.drop (replay limits rules initial earlier).2.length) := by
  rw [replay_append, certified]
  simp

theorem ranked_recovery_preserves_the_old_ordered_replies
    {Voter : Type}
    {old next current : ConfigurationClosure.Generation Voter (Command width Pool Payload Ticket)}
    (changed : ConfigurationClosure.Handoff old next) (later : ConfigurationClosure.Changes next current)
    (installed : ConfigurationClosure.InstalledOnQuorum current) (available : Voter → Bool)
    (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {earlier : List (Command width Pool Payload Ticket)}
    (chosen : PrefixAgreement.Chosen old.ledger ballot earlier)
    (limits : Kernel.Limits) (rules : Rules width Pool Payload Ticket)
    (initial : State width Pool Payload) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧ current.installed voter current.basis ∧
      (replay limits rules initial earlier).2 <+: (replay limits rules initial current.basis).2 := by
  obtain ⟨voter, member, online, covered, inherited⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority changed later installed available quorum chosen
  obtain ⟨suffix, exactPrefix⟩ := inherited
  refine ⟨voter, member, online, covered, ?_⟩
  rw [← exactPrefix, replay_append]
  exact List.prefix_append _ _

#print axioms missing_ordered_evidence_is_a_refusal
#print axioms a_certified_physical_settlement_is_applied_from_its_ordered_attachment
#print axioms a_joint_command_projects_to_the_stream
#print axioms ordinary_commands_cannot_freeze_the_source
#print axioms a_successful_funded_seal_records_both_effects_at_one_position
#print axioms a_prepared_retirement_records_its_abort_at_the_same_position
#print axioms installation_rejects_a_different_ordered_seal_position
#print axioms replay_append
#print axioms a_joint_history_projects_to_the_stream_trace
#print axioms a_certified_joint_checkpoint_replays_the_same_tail
#print axioms ranked_recovery_preserves_the_old_ordered_replies

end UnifiedSource
