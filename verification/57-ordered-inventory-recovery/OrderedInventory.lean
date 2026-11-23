import InventoryCodec
import ConfigurationClosure
import JournalRotation

set_option warningAsError true

namespace OrderedInventory

open PoolIncarnations (State Validation Event)

variable {Ticket Book LedgerCommand Voter : Type}

inductive Command (Book LedgerCommand : Type) where
  | register (scope : Nat)
  | fault (scope epoch : Nat)
  | reconnect (scope epoch : Nat)
  | validate (scope : Nat) (evidence : Validation Book)
  | settle (scope : Nat) (evidence : Book)
  | account (command : LedgerCommand)

inductive Reply where
  | registered (scope : Nat)
  | completed
  | refused

def event : Command Book LedgerCommand → Event
  | .register _ => .register
  | .fault .. => .fault
  | .reconnect .. => .reconnect
  | .validate .. => .validate
  | .settle .. => .settle
  | .account _ => .account

structure Rules (Ticket Book LedgerCommand : Type) [DecidableEq Ticket] where
  slots : Nat
  serialMax : Nat
  epochMax : Nat
  layout : SharedExtentAccounting.Layout Nat
  needs : SharedCustody.Dependencies
  closeAllowed : Nat → Prop
  reserve : ProviderIOClosure.Custody Ticket → Prop
  expected : SharedExtentAccounting.State Nat Ticket → Nat → Book
  authenticated : Validation Book → Prop
  terminalEvidence : Nat → Book → Prop
  applyAccount : State Ticket → LedgerCommand → Option (State Ticket)
  accountSound : ∀ state command next, applyAccount state command = some next →
    PoolIncarnations.Step slots layout needs closeAllowed reserve expected authenticated
      (fun scope => ∃ evidence, terminalEvidence scope evidence) state .account next

abbrev Transition [DecidableEq Ticket] (rules : Rules Ticket Book LedgerCommand) :=
  FiniteCounters.Step rules.slots rules.serialMax rules.epochMax rules.layout rules.needs
    rules.closeAllowed rules.reserve rules.expected rules.authenticated
    (fun scope => ∃ evidence, rules.terminalEvidence scope evidence)

variable [DecidableEq Ticket]

noncomputable def attempt (rules : Rules Ticket Book LedgerCommand) (state : State Ticket) :
    Command Book LedgerCommand → Option (State Ticket × Reply) := by
  classical
  exact fun command => match command with
  | .register scope =>
      if scope = state.issued + 1 ∧ state.registry.length < rules.slots ∧ state.issued < rules.serialMax then
        some (PoolIncarnations.register state, .registered scope)
      else none
  | .fault scope epoch =>
      if scope ∈ state.registry ∧ epoch = (state.access scope).epoch ∧ epoch ≤ rules.epochMax then
        some (PoolIncarnations.fault state scope, .completed)
      else none
  | .reconnect scope epoch =>
      if scope ∈ state.registry ∧ (state.access scope).phase = .offline ∧
          epoch = (state.access scope).epoch ∧ epoch ≤ rules.epochMax then
        some (PoolIncarnations.changePhase state scope .quarantine, .completed)
      else none
  | .validate scope evidence =>
      if PoolIncarnations.CanOpen rules.expected rules.authenticated state scope evidence ∧
          (state.access scope).epoch ≤ rules.epochMax then
        some (PoolIncarnations.changePhase state scope .eligible, .completed)
      else none
  | .settle scope evidence =>
      if scope ∈ state.registry ∧ (state.access scope).phase = .offline ∧
          rules.terminalEvidence scope evidence ∧ PoolIncarnations.Uncharged rules.layout state scope then
        some (PoolIncarnations.forget state scope, .completed)
      else none
  | .account command =>
      (rules.applyAccount state command).map (fun next => (next, .completed))

noncomputable def decide (rules : Rules Ticket Book LedgerCommand) (state : State Ticket)
    (command : Command Book LedgerCommand) : State Ticket × Reply :=
  (attempt rules state command).getD (state, .refused)

theorem each_successful_command_uses_the_finite_custody_rule
    (rules : Rules Ticket Book LedgerCommand)
    {state next : State Ticket} {command : Command Book LedgerCommand} {reply : Reply}
    (accepted : attempt rules state command = some (next, reply)) :
    Transition rules state (event command) next := by
  cases command with
  | register scope =>
      simp only [attempt] at accepted
      split at accepted
      next ready =>
        cases accepted
        exact .register ready.2.1 ready.2.2
      next => simp at accepted
  | fault scope epoch =>
      simp only [attempt] at accepted
      split at accepted
      next ready =>
        cases accepted
        exact .fault scope ready.1 (ready.2.1 ▸ ready.2.2)
      next => simp at accepted
  | reconnect scope epoch =>
      simp only [attempt] at accepted
      split at accepted
      next ready =>
        cases accepted
        exact .reconnect scope ready.1 ready.2.1 (ready.2.2.1 ▸ ready.2.2.2)
      next => simp at accepted
  | validate scope evidence =>
      simp only [attempt] at accepted
      split at accepted
      next verified =>
        cases accepted
        exact .validate scope evidence verified.1 verified.2
      next => simp at accepted
  | settle scope evidence =>
      simp only [attempt] at accepted
      split at accepted
      next verified =>
        cases accepted
        exact .settle (.settle scope verified.1 verified.2.1
          ⟨evidence, verified.2.2.1⟩ verified.2.2.2)
      next => simp at accepted
  | account command =>
      cases applied : rules.applyAccount state command with
      | none => simp [attempt, applied] at accepted
      | some result =>
          simp [attempt, applied] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact .account (rules.accountSound state command result applied)

theorem issuance_is_bound_to_the_exact_next_scope
    (rules : Rules Ticket Book LedgerCommand) {state next : State Ticket} {request returned : Nat}
    (accepted : attempt rules state (.register request) = some (next, .registered returned)) :
    returned = request ∧ returned = state.issued + 1 ∧ next = PoolIncarnations.register state := by
  simp only [attempt] at accepted
  split at accepted
  next authorized =>
    cases accepted
    exact ⟨rfl, authorized.1, rfl⟩
  next => simp at accepted

theorem a_registered_scope_cannot_be_allocated_again_by_the_same_request
    (rules : Rules Ticket Book LedgerCommand) {state next : State Ticket} {scope : Nat}
    (accepted : attempt rules state (.register scope) = some (next, .registered scope)) :
    decide rules next (.register scope) = (next, .refused) := by
  obtain ⟨_, fresh, rfl⟩ := issuance_is_bound_to_the_exact_next_scope rules accepted
  have spent : scope ≠ (PoolIncarnations.register state).issued + 1 := by simp [PoolIncarnations.register, fresh]
  simp [decide, attempt, spent]

theorem replay_uses_the_original_attached_proof
    (rules : Rules Ticket Book LedgerCommand) (state : State Ticket) (scope : Nat)
    (evidence : Validation Book) (inadmissible : ¬ rules.authenticated evidence) :
    decide rules state (.validate scope evidence) = (state, .refused) := by
  have refused : ¬ (PoolIncarnations.CanOpen rules.expected rules.authenticated state scope evidence ∧
      (state.access scope).epoch ≤ rules.epochMax) := fun accepted => inadmissible accepted.1.2.2.2.2.2
  simp [decide, attempt, refused]

noncomputable def apply (rules : Rules Ticket Book LedgerCommand) (state : State Ticket)
    (command : Command Book LedgerCommand) : State Ticket :=
  (decide rules state command).1

noncomputable def receiptAt (rules : Rules Ticket Book LedgerCommand) (initial : State Ticket)
    (history : List (Command Book LedgerCommand)) (position : Nat) : Option Reply :=
  history[position]?.map (fun command => (decide rules ((history.take position).foldl (apply rules) initial) command).2)

noncomputable def replyIfReady (rules : Rules Ticket Book LedgerCommand) (initial : State Ticket)
    (ledger : PrefixAgreement.Ledger Voter (Command Book LedgerCommand)) (ballot : Nat)
    (history : List (Command Book LedgerCommand)) (position appliedCut : Nat) (request : Command Book LedgerCommand) :
    Option Reply := by
  classical
  exact if PrefixAgreement.Chosen ledger ballot history ∧
      position < appliedCut ∧ appliedCut ≤ history.length ∧
      history[position]? = some request then receiptAt rules initial history position else none

theorem a_reply_requires_the_exact_applied_chosen_command
    (rules : Rules Ticket Book LedgerCommand) (initial : State Ticket)
    {ledger : PrefixAgreement.Ledger Voter (Command Book LedgerCommand)} {ballot : Nat}
    {history : List (Command Book LedgerCommand)} {position appliedCut : Nat}
    {request : Command Book LedgerCommand} {reply : Reply}
    (sent : replyIfReady rules initial ledger ballot history position appliedCut request = some reply) :
    (PrefixAgreement.Chosen ledger ballot history ∧ position < appliedCut ∧ appliedCut ≤ history.length ∧
      history[position]? = some request) ∧ receiptAt rules initial history position = some reply := by
  simp only [replyIfReady] at sent
  split at sent
  next authorized => exact ⟨authorized, sent⟩
  next => simp at sent

theorem replay_preserves_inventory_and_original_physical_obligations
    (rules : Rules Ticket Book LedgerCommand) (initial : State Ticket)
    (history : List (Command Book LedgerCommand))
    (safe : PoolIncarnations.Sound rules.slots rules.layout rules.needs initial)
    (fits : FiniteCounters.Fits rules.serialMax rules.epochMax initial)
    (ordered : FiniteCounters.Ordered initial) :
    let final := history.foldl (apply rules) initial
    PoolIncarnations.Sound rules.slots rules.layout rules.needs final ∧
      FiniteCounters.Fits rules.serialMax rules.epochMax final ∧ FiniteCounters.Ordered final := by
  induction history generalizing initial with
  | nil => exact ⟨safe, fits, ordered⟩
  | cons command tail prior =>
      cases observed : attempt rules initial command with
      | none => simpa [apply, decide, observed] using prior initial safe fits ordered
      | some result =>
          obtain ⟨next, reply⟩ := result
          have step := each_successful_command_uses_the_finite_custody_rule rules observed
          obtain ⟨valid, bounds⟩ := FiniteCounters.finite_steps_preserve_custody_and_representability safe fits step
          have shape := FiniteCounters.finite_steps_keep_a_canonical_registry_order safe ordered step
          simpa [apply, decide, observed] using prior next valid bounds shape

structure Opened (rules : Rules Ticket Book LedgerCommand) (initial checkpoint : State Ticket)
    (media : JournalRotation.State (Command Book LedgerCommand)) (selector : JournalRotation.View)
    (width : Nat) (wire : EnvelopeCodec.Bytes) : Prop where
  imageAtCut : checkpoint = (media.history.take selector.cut).foldl (apply rules) initial
  body : InventoryCodec.decode width rules.slots wire = some (InventoryCodec.fromState width checkpoint)

theorem media_recovery_reconstructs_the_exact_inventory_and_its_frames
    (rules : Rules Ticket Book LedgerCommand)
    {initial checkpoint : State Ticket} {media : JournalRotation.State (Command Book LedgerCommand)}
    {selector : JournalRotation.View} {width : Nat} {wire : EnvelopeCodec.Bytes}
    (opened : Opened rules initial checkpoint media selector width wire)
    (safe : JournalRotation.Safe media) (tracked : JournalRotation.TracksNamespace media)
    (selected : media.namespaceChoices selector) :
    InventoryCodec.encode width (InventoryCodec.fromState width checkpoint) = wire ∧
      ∃ tail, tail = media.history.drop selector.cut ∧
        tail.foldl (apply rules) checkpoint = media.history.foldl (apply rules) initial ∧
        ∀ offset command, tail[offset]? = some command →
          media.media (.tail (selector.cut + offset)) = some [command] := by
  obtain ⟨_, _, frames⟩ := JournalRotation.selectable_has_exact_cut safe ((tracked selector).mp selected)
  refine ⟨(InventoryCodec.accepted_inventory_bytes_are_canonical opened.body).2,
    media.history.drop selector.cut, rfl, ?_, ?_⟩
  · exact FiniteCounters.recovering_the_exact_selected_base_and_suffix_restores_the_inventory
      (apply rules) initial checkpoint _ _ _ opened.imageAtCut.symm (List.take_append_drop _ _)
  · intro offset command atPosition
    rw [List.getElem?_drop] at atPosition
    exact frames _ _ (Nat.le_add_right _ _) atPosition

theorem earlier_receipts_keep_their_exact_ordered_basis
    (rules : Rules Ticket Book LedgerCommand) (initial : State Ticket)
    {earlier later : List (Command Book LedgerCommand)} (inherited : earlier <+: later)
    (position : Nat) (existing : position < earlier.length) :
    receiptAt rules initial earlier position = receiptAt rules initial later position := by
  obtain ⟨tail, rfl⟩ := inherited
  have samePrefix : (earlier ++ tail).take position = earlier.take position := by
    rw [List.take_append_of_le_length (Nat.le_of_lt existing)]
  simp [receiptAt, samePrefix, List.getElem?_append_left existing]

theorem ranked_media_recovery_preserves_receipts_from_unlearned_choices
    (rules : Rules Ticket Book LedgerCommand)
    {old first current : ConfigurationClosure.Generation Voter (Command Book LedgerCommand)}
    (handoff : ConfigurationClosure.Handoff old first) (later : ConfigurationClosure.Changes first current)
    (installed : ConfigurationClosure.InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {earlier : List (Command Book LedgerCommand)} (chosen : PrefixAgreement.Chosen old.ledger ballot earlier)
    (initial : State Ticket)
    (media : Voter → JournalRotation.State (Command Book LedgerCommand))
    (selector : Voter → JournalRotation.View) (checkpoint : Voter → State Ticket)
    (width : Nat) (wire : Voter → EnvelopeCodec.Bytes)
    (donor : ∀ voter ∈ current.ledger.members, available voter = true → current.installed voter current.basis →
      (media voter).history = current.basis ∧ JournalRotation.Safe (media voter) ∧
      JournalRotation.TracksNamespace (media voter) ∧ (media voter).namespaceChoices (selector voter) ∧
      Opened rules initial (checkpoint voter) (media voter) (selector voter) width (wire voter)) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧
      ((media voter).history.drop (selector voter).cut).foldl (apply rules) (checkpoint voter) =
        current.basis.foldl (apply rules) initial ∧
      ∀ position, position < earlier.length →
        receiptAt rules initial earlier position = receiptAt rules initial (media voter).history position := by
  obtain ⟨voter, member, reachable, bound, inherited⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority handoff later installed available quorum chosen
  obtain ⟨exact, safe, tracked, selected, opened⟩ := donor voter member reachable bound
  obtain ⟨_, tail, suffix, recovered, _⟩ :=
    media_recovery_reconstructs_the_exact_inventory_and_its_frames rules opened safe tracked selected
  refine ⟨voter, member, reachable, ?_, ?_⟩
  · rwa [← exact, ← suffix]
  · intro position existing
    rw [exact]
    exact earlier_receipts_keep_their_exact_ordered_basis rules initial inherited position existing

#print axioms each_successful_command_uses_the_finite_custody_rule
#print axioms issuance_is_bound_to_the_exact_next_scope
#print axioms a_registered_scope_cannot_be_allocated_again_by_the_same_request
#print axioms replay_uses_the_original_attached_proof
#print axioms a_reply_requires_the_exact_applied_chosen_command
#print axioms replay_preserves_inventory_and_original_physical_obligations
#print axioms media_recovery_reconstructs_the_exact_inventory_and_its_frames
#print axioms earlier_receipts_keep_their_exact_ordered_basis
#print axioms ranked_media_recovery_preserves_receipts_from_unlearned_choices

end OrderedInventory
