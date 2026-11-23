import PendingActivation

set_option warningAsError true

namespace AttemptCompaction

open PendingActivation

variable {Image : Type}

structure Book (Image : Type) where
  raw : State Image
  cutoff : Nat
  cleanup : Nat → Prop

def Effective (cutoff : Nat) (table : Nat → Holding Image) (id : Nat) : Holding Image :=
  match table id with
  | .absent => if id ≤ cutoff then .spent else .absent
  | holding => holding

def Trimmed (cutoff : Nat) (table : Nat → Holding Image) (id : Nat) : Holding Image :=
  if id ≤ cutoff then
    match table id with
    | .spent => .absent
    | holding => holding
  else table id

def Resolved (table : Nat → Holding Image) (id : Nat) : Prop :=
  table id ≠ .absent

def CanAdvance (book : Book Image) (cutoff : Nat) : Prop :=
  book.cutoff ≤ cutoff ∧ ∀ id, book.cutoff < id → id ≤ cutoff → Resolved book.raw.attempts id

def View (book : Book Image) : State Image :=
  {book.raw with attempts := Effective book.cutoff book.raw.attempts}

def compact (book : Book Image) (cutoff : Nat) : Book Image :=
  {book with cutoff, raw := {book.raw with attempts := Trimmed cutoff book.raw.attempts}}

theorem trimmed_retains_exact_ready_row {table : Nat → Holding Image} {id cutoff : Nat}
    {ticket : Ticket Image} (live : table id = .ready ticket) :
    Trimmed cutoff table id = .ready ticket := by
  by_cases under : id ≤ cutoff
  · have exactWhenCovered : Trimmed cutoff table id = table id := by
      simp [Trimmed, under, live]
    exact exactWhenCovered.trans live
  · simp [Trimmed, under, live]

theorem advancing_cutoff_preserves_the_interpreted_book
    {book : Book Image} {cutoff : Nat} (safe : CanAdvance book cutoff) :
    View (compact book cutoff) = View book := by
  have table : Effective cutoff (Trimmed cutoff book.raw.attempts) =
      Effective book.cutoff book.raw.attempts := by
    funext id
    cases current : book.raw.attempts id with
    | absent =>
        have noGap : id ≤ cutoff → id ≤ book.cutoff := by
          intro reached
          apply Classical.byContradiction
          intro skipped
          have accounted : book.raw.attempts id ≠ .absent := by
            exact safe.2 id (Nat.lt_of_not_ge skipped) reached
          exact accounted current
        have includes : id ≤ book.cutoff → id ≤ cutoff := fun old => Nat.le_trans old safe.1
        by_cases reached : id ≤ cutoff
        · simp [Effective, Trimmed, current, reached, noGap reached]
        · have newer : ¬ id ≤ book.cutoff := fun old => reached (includes old)
          simp [Effective, Trimmed, current, reached, newer]
    | ready ticket =>
        unfold Effective
        rw [trimmed_retains_exact_ready_row (cutoff := cutoff) current, current]
    | spent =>
        by_cases reached : id ≤ cutoff <;> simp [Effective, Trimmed, current, reached]
  exact congrArg (fun attempts => {book.raw with attempts}) table

theorem compaction_keeps_physical_cleanup (book : Book Image) (cutoff : Nat) :
    (compact book cutoff).cleanup = book.cleanup := by
  exact Eq.refl book.cleanup

theorem compaction_preserves_all_later_ordered_results
    {book : Book Image} {cutoff : Nat} (safe : CanAdvance book cutoff)
    (commands : List (Command Image)) :
    replay (View (compact book cutoff)) commands = replay (View book) commands := by
  rw [advancing_cutoff_preserves_the_interpreted_book safe]

theorem a_ready_ticket_can_activate_after_crossing_the_cutoff
    {book : Book Image} {cutoff : Nat} {ticket : Ticket Image}
    (safe : CanAdvance book cutoff) (room : MayActivate (View book) ticket) :
    (apply (View (compact book cutoff)) (.activate ticket)).2 = .activated ticket := by
  rw [advancing_cutoff_preserves_the_interpreted_book safe]
  exact (an_exact_live_candidate_can_be_installed room).2

theorem an_absent_compacted_ticket_cannot_register_through_any_replay
    {book : Book Image} {ticket : Ticket Image}
    (removed : book.raw.attempts ticket.attempt = .absent) (under : ticket.attempt ≤ book.cutoff)
    (commands : List (Command Image)) :
    let state := (replay (View book) commands).1
    apply state (.register ticket) = (state, .refused) := by
  classical
  have interpreted : (View book).attempts ticket.attempt = .spent := by
    simp [View, Effective, removed, under]
  let state := (replay (View book) commands).1
  have stillSpent : state.attempts ticket.attempt = .spent :=
    replay_cannot_resurrect_a_spent_attempt interpreted commands
  have denied : ¬ (InOrderedScope state ticket ∧ state.installed = none ∧
      state.attempts ticket.attempt = .absent) := by
    intro accepts
    have absent := accepts.2.2
    rw [stillSpent] at absent
    cases absent
  change apply state (.register ticket) = (state, .refused)
  simp only [apply, ite_eq_right denied]

theorem remaining_terminal_markers_fit_the_issued_window
    {table : Nat → Holding Image} {floor issued width id : Nat}
    (issuedBound : ∀ handle, table handle = .spent → handle ≤ issued)
    (window : issued - floor ≤ width) (remaining : Trimmed floor table id = .spent) :
    ∃ credit : Fin width, id = floor + credit.val + 1 := by
  have above : floor < id := by
    by_cases behind : id ≤ floor
    · cases row : table id <;> simp [Trimmed, row, behind] at remaining
    · exact Nat.lt_of_not_ge behind
  have original : table id = .spent := by simpa [Trimmed, Nat.not_le_of_gt above] using remaining
  have endBound := issuedBound id original
  refine ⟨⟨id - (floor + 1), by omega⟩, ?_⟩
  change id = floor + (id - (floor + 1)) + 1
  omega

#print axioms trimmed_retains_exact_ready_row
#print axioms advancing_cutoff_preserves_the_interpreted_book
#print axioms compaction_keeps_physical_cleanup
#print axioms compaction_preserves_all_later_ordered_results
#print axioms a_ready_ticket_can_activate_after_crossing_the_cutoff
#print axioms an_absent_compacted_ticket_cannot_register_through_any_replay
#print axioms remaining_terminal_markers_fit_the_issued_window

end AttemptCompaction
