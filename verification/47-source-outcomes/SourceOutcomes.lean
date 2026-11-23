import ConfigurationClosure

set_option warningAsError true

namespace SourceOutcomes

variable {Scope Participant : Type} {width : Nat}

inductive Resolution where
  | canceled
  | committed
  deriving DecidableEq

structure Key (width : Nat) where
  slot : Fin width
  serial : Nat
  deriving DecidableEq

structure Row (Scope Participant : Type) where
  serial : Nat
  binding : Scope
  result : Option Resolution
  waiting : List Participant

structure Book (width : Nat) (Scope Participant : Type) where
  issued : Nat
  rows : Fin width → Option (Row Scope Participant)

def lookup (book : Book width Scope Participant) (key : Key width) : Option (Row Scope Participant) :=
  (book.rows key.slot).filter (fun row => row.serial == key.serial)

def setRow (book : Book width Scope Participant) (slot : Fin width) (row : Option (Row Scope Participant)) :
    Book width Scope Participant :=
  {book with rows := fun query => if query = slot then row else book.rows query}

structure Decision (width : Nat) (Scope : Type) where
  key : Key width
  binding : Scope
  result : Resolution

structure Receipt (width : Nat) (Scope Participant : Type) where
  decision : Decision width Scope
  participant : Participant

structure Authority (width : Nat) (Scope Participant : Type) where
  planned : Key width → Scope → List Participant → Prop
  chosen : Decision width Scope → Prop
  settled : Receipt width Scope Participant → Prop
  authenticIssue : Key width → Scope → Prop

inductive Command (width : Nat) (Scope Participant : Type) where
  | reserve (key : Key width) (binding : Scope) (participants : List Participant)
  | resolve (decision : Decision width Scope)
  | acknowledge (receipt : Receipt width Scope Participant)
  | compact (key : Key width)

def MayAccept (auth : Authority width Scope Participant) (row : Row Scope Participant)
    (receipt : Receipt width Scope Participant) : Prop :=
  receipt.decision.binding = row.binding ∧
  row.result = some receipt.decision.result ∧ auth.settled receipt

def MayCompact (row : Row Scope Participant) : Prop :=
  row.result.isSome ∧ row.waiting = []

noncomputable def apply [DecidableEq Scope] [DecidableEq Participant]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant) :
    Command width Scope Participant → Book width Scope Participant
  | .reserve key binding participants => by
      classical
      exact if key.serial = book.issued + 1 ∧ book.rows key.slot = none ∧ auth.planned key binding participants
        then {setRow book key.slot (some ⟨key.serial, binding, none, participants⟩) with issued := key.serial}
        else book
  | .resolve decision => by
      classical
      exact match lookup book decision.key with
      | none => book
      | some row =>
          if row.binding = decision.binding ∧ row.result = none ∧ auth.chosen decision
          then setRow book decision.key.slot (some {row with result := some decision.result})
          else book
  | .acknowledge receipt => by
      classical
      exact match lookup book receipt.decision.key with
      | none => book
      | some row =>
          if MayAccept auth row receipt
          then setRow book receipt.decision.key.slot
            (some {row with waiting := row.waiting.filter (· != receipt.participant)})
          else book
  | .compact key => by
      classical
      exact match lookup book key with
      | none => book
      | some row => if MayCompact row then setRow book key.slot none else book

inductive View where
  | unknown
  | pending
  | exactResult (result : Resolution)
  | closed
  deriving DecidableEq

noncomputable def query [DecidableEq Scope] (auth : Authority width Scope Participant)
    (book : Book width Scope Participant) (key : Key width) (binding : Scope) : View := by
  classical
  exact if ¬ auth.authenticIssue key binding ∨ book.issued < key.serial then .unknown else
    match lookup book key with
    | none => .closed
    | some row =>
        if row.binding = binding then row.result.elim .pending .exactResult else .unknown

theorem receipt_must_match_the_original_binding (auth : Authority width Scope Participant)
    (row : Row Scope Participant) (receipt : Receipt width Scope Participant)
    (eligible : MayAccept auth row receipt) :
    receipt.decision.binding = row.binding := by
  exact eligible.1

theorem compaction_requires_durable_settlement (row : Row Scope Participant) (eligible : MayCompact row) :
    row.waiting = [] := by
  exact eligible.2

theorem uncertain_ownership_receipt_cannot_discharge_a_debt [DecidableEq Scope] [DecidableEq Participant]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant)
    (receipt : Receipt width Scope Participant) (unverified : ¬ auth.settled receipt) :
    apply auth book (.acknowledge receipt) = book := by
  cases found : lookup book receipt.decision.key <;> simp [apply, found, MayAccept, unverified]

theorem a_waiting_participant_retains_its_exact_row [DecidableEq Scope] [DecidableEq Participant]
    {auth : Authority width Scope Participant} {book : Book width Scope Participant}
    {key : Key width} {row : Row Scope Participant} (found : lookup book key = some row)
    (unsettled : row.waiting ≠ []) : apply auth book (.compact key) = book := by
  have blocked : ¬ MayCompact row := fun allowed => unsettled (compaction_requires_durable_settlement row allowed)
  simp [apply, found, blocked]

theorem a_later_settled_slot_can_be_returned_independently [DecidableEq Scope] [DecidableEq Participant]
    {auth : Authority width Scope Participant} {book : Book width Scope Participant}
    {key old : Key width} {row : Row Scope Participant} (found : lookup book key = some row)
    (settled : MayCompact row) (independent : old.slot ≠ key.slot) :
    let next := apply auth book (.compact key)
    next.issued = book.issued ∧ next.rows key.slot = none ∧ lookup next old = lookup book old := by
  dsimp only
  rw [show apply auth book (.compact key) = setRow book key.slot none from by simp [apply, found, settled]]
  simp [lookup, setRow, independent]

theorem deciding_a_reserved_row_needs_no_result_slot [DecidableEq Scope] [DecidableEq Participant]
    {auth : Authority width Scope Participant} {book : Book width Scope Participant}
    {decision : Decision width Scope} {row : Row Scope Participant}
    (found : lookup book decision.key = some row) (binding : row.binding = decision.binding)
    (unresolved : row.result = none) (chosen : auth.chosen decision) :
    apply auth book (.resolve decision) =
      setRow book decision.key.slot (some {row with result := some decision.result}) := by
  simp [apply, found, binding, unresolved, chosen]

theorem retired_issued_identity_reports_only_closure [DecidableEq Scope]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant)
    (key : Key width) (binding : Scope) (authentic : auth.authenticIssue key binding)
    (old : key.serial ≤ book.issued) (missing : lookup book key = none) :
    query auth book key binding = .closed := by
  simp [query, authentic, Nat.not_lt_of_ge old, missing]

theorem unissued_identity_has_no_terminal_result [DecidableEq Scope]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant)
    (key : Key width) (binding : Scope) (future : book.issued < key.serial) :
    query auth book key binding = .unknown := by
  simp [query, future]

theorem a_retained_row_returns_its_exact_outcome [DecidableEq Scope]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant)
    (key : Key width) (row : Row Scope Participant) (result : Resolution)
    (authentic : auth.authenticIssue key row.binding) (issued : key.serial ≤ book.issued)
    (found : lookup book key = some row) (resolved : row.result = some result) :
    query auth book key row.binding = .exactResult result := by
  simp [query, authentic, Nat.not_lt_of_ge issued, found, resolved]

noncomputable def replay [DecidableEq Scope] [DecidableEq Participant]
    (auth : Authority width Scope Participant) (base : Book width Scope Participant)
    (journal : List (Command width Scope Participant)) : Book width Scope Participant :=
  journal.foldl (apply auth) base

theorem replay_append [DecidableEq Scope] [DecidableEq Participant]
    (auth : Authority width Scope Participant) (base : Book width Scope Participant)
    (first rest : List (Command width Scope Participant)) :
    replay auth base (first ++ rest) = replay auth (replay auth base first) rest := by
  simp [replay, List.foldl_append]

theorem a_recovery_majority_replays_every_chosen_source_decision
    {Voter : Type} [DecidableEq Scope] [DecidableEq Participant]
    {old next current : ConfigurationClosure.Generation Voter (Command width Scope Participant)}
    (change : ConfigurationClosure.Handoff old next)
    (later : ConfigurationClosure.Changes next current)
    (installed : ConfigurationClosure.InstalledOnQuorum current)
    (available : Voter → Bool) (quorum : JournalRefinement.Majority current.ledger.members available)
    {ballot : Nat} {history : List (Command width Scope Participant)}
    (chosen : PrefixAgreement.Chosen old.ledger ballot history)
    (auth : Authority width Scope Participant) (base : Book width Scope Participant) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧ current.installed voter current.basis ∧
      ∃ suffix, current.basis = history ++ suffix ∧
        replay auth base current.basis = replay auth (replay auth base history) suffix := by
  obtain ⟨voter, member, online, covered, earlier⟩ :=
    ConfigurationClosure.earlier_choice_reaches_any_later_recovery_majority
      change later installed available quorum chosen
  obtain ⟨suffix, exactPrefix⟩ := earlier
  exact ⟨voter, member, online, covered, suffix, exactPrefix.symm, by rw [← exactPrefix, replay_append]⟩

theorem compaction_can_make_distinct_outcomes_identical [DecidableEq Scope] [DecidableEq Participant]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant)
    (key : Key width) (binding : Scope) (result : Resolution) :
    let settled : Row Scope Participant := ⟨key.serial, binding, some result, []⟩
    apply auth (setRow book key.slot (some settled)) (.compact key) = setRow book key.slot none := by
  have found : lookup (setRow book key.slot (some ⟨key.serial, binding, some result, []⟩)) key =
      some ⟨key.serial, binding, some result, []⟩ := by simp [lookup, setRow]
  dsimp only
  rw [show apply auth (setRow book key.slot (some ⟨key.serial, binding, some result, []⟩)) (.compact key) =
      setRow (setRow book key.slot (some ⟨key.serial, binding, some result, []⟩)) key.slot none from
    by simp [apply, found, MayCompact]]
  simp [setRow]
  funext slot
  by_cases same : slot = key.slot <;> simp [same]

theorem a_compacted_book_cannot_reconstruct_both_exact_outcomes [DecidableEq Scope] [DecidableEq Participant]
    (auth : Authority width Scope Participant) (book : Book width Scope Participant)
    (key : Key width) (binding : Scope) :
    ¬ ∃ decode : Book width Scope Participant → Resolution, ∀ result,
      decode (apply auth (setRow book key.slot (some ⟨key.serial, binding, some result, []⟩)) (.compact key)) =
        result := by
  rintro ⟨decode, exactResult⟩
  have left := exactResult .canceled
  have right := exactResult .committed
  rw [compaction_can_make_distinct_outcomes_identical] at left right
  have different : Resolution.canceled ≠ .committed := by decide
  exact different (left.symm.trans right)

#print axioms receipt_must_match_the_original_binding
#print axioms compaction_requires_durable_settlement
#print axioms uncertain_ownership_receipt_cannot_discharge_a_debt
#print axioms a_waiting_participant_retains_its_exact_row
#print axioms a_later_settled_slot_can_be_returned_independently
#print axioms deciding_a_reserved_row_needs_no_result_slot
#print axioms retired_issued_identity_reports_only_closure
#print axioms unissued_identity_has_no_terminal_result
#print axioms a_retained_row_returns_its_exact_outcome
#print axioms replay_append
#print axioms a_recovery_majority_replays_every_chosen_source_decision
#print axioms compaction_can_make_distinct_outcomes_identical
#print axioms a_compacted_book_cannot_reconstruct_both_exact_outcomes

end SourceOutcomes
