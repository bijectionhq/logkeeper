import Logkeeper.StreamRpc

namespace Logkeeper.StreamRead

open PrefixAgreement StreamJournal StreamIO StreamHead StreamRpc StreamWriter

set_option autoImplicit false
set_option warningAsError true

variable {Payload : Type}

def committedHistory (k : Keeper Payload) : History Payload := k.history.take k.head

theorem local_head_step {w : Writer Payload} {k next : Keeper Payload}
    (step : Step w k next) : k.head ≤ next.head := by
  cases step <;> simp_all [deleteKeeper, sealKeeper] <;>
    first | exact Nat.le_max_left .. | (split <;> simp_all)

theorem local_head_grows (trace : Timeline Payload) {first last : Nat} (ordered : first ≤ last)
    (keeper : KeeperId) : ((trace.state first).keeper keeper).head ≤
      ((trace.state last).keeper keeper).head := by
  induction ordered with
  | refl => exact Nat.le_refl _
  | @step time _ prior =>
      obtain ⟨_, next⟩ := trace.next time
      rcases (every_action_refines (trace.reachable time) next).2 keeper with step | unchanged
      · exact Nat.le_trans prior (local_head_step step)
      · rwa [unchanged]

theorem writer_grows (trace : Timeline Payload) {first last : Nat} (ordered : first ≤ last) :
    Grows (trace.state first).writer (trace.state last).writer := by
  induction ordered with
  | refl => exact Grows.refl _
  | @step time _ prior =>
      obtain ⟨_, next⟩ := trace.next time
      exact prior.trans (next_inv (reachable_inv (trace.reachable time)) next).2.2

theorem committed_history_length (trace : Timeline Payload) (event : Nat) (keeper : KeeperId) :
    (committedHistory ((trace.state event).keeper keeper)).length =
      ((trace.state event).keeper keeper).head := by
  rw [committedHistory, List.length_take, Nat.min_eq_left]
  exact (keeper_bounds ((reachable_inv (trace.reachable event)).reached keeper)).1

theorem committed_history_grows (trace : Timeline Payload) {first last : Nat}
    (ordered : first ≤ last) (keeper : KeeperId) :
    committedHistory ((trace.state first).keeper keeper) <+:
      committedHistory ((trace.state last).keeper keeper) := by
  have advertised (event : Nat) :=
    let inv := reachable_inv (trace.reachable event)
    keeper_head_was_advertised inv.emptyAdvertised (inv.reached keeper)
  rcases certified_cuts_agree (trace.reachable last)
      ((writer_grows trace ordered).advertised _ (advertised first)) (advertised last)
    with forward | reverse
  · exact forward
  · have lengths := local_head_grows trace ordered keeper
    rw [← committed_history_length trace first keeper, ← committed_history_length trace last keeper]
      at lengths
    rw [show committedHistory ((trace.state last).keeper keeper) =
      committedHistory ((trace.state first).keeper keeper) from reverse.eq_of_length_le lengths]
    exact List.prefix_rfl

variable {trace : Timeline Payload} {keeper : KeeperId}

/-- A frame-limited Read samples one immutable slice at the keeper. The request
    is a keeper observation in StreamIO; its page fields come start that sample. -/
structure Chunk (trace : Timeline Payload) (keeper : KeeperId) where
  caller : Nat
  rpc : Exchange trace keeper caller (.observe : Request Payload)
  start : Nat
  count : Nat
  retained : ((trace.state rpc.sample).keeper keeper).floor ≤ start

def Chunk.history (chunk : Chunk trace keeper) : History Payload :=
  committedHistory ((trace.state chunk.rpc.sample).keeper keeper)

def Chunk.records (chunk : Chunk trace keeper) : History Payload :=
  (chunk.history.drop (chunk.start - 1)).take chunk.count

def Chunk.floor (chunk : Chunk trace keeper) : Nat :=
  ((trace.state chunk.rpc.sample).keeper keeper).floor

def Chunk.head (chunk : Chunk trace keeper) : Nat :=
  ((trace.state chunk.rpc.sample).keeper keeper).head

/-- Each later chunk starts where the accumulated page ends. Its requested
    length is bounded by the first sampled head, even if the keeper advanced. -/
theorem read_continuation (first next : Chunk trace keeper) {copied : Nat}
    (after : first.rpc.sample ≤ next.rpc.sample)
    (contiguous : next.start - 1 = first.start - 1 + copied)
    (bounded : first.start - 1 + copied + next.count ≤ first.head) :
    (first.history.drop (first.start - 1)).take copied ++ next.records =
      (first.history.drop (first.start - 1)).take (copied + next.count) := by
  unfold Chunk.records
  rw [contiguous]
  exact assemble_read_chunk (committed_history_grows trace after keeper)
    (by
      change _ ≤ (committedHistory _).length
      rwa [committed_history_length trace first.rpc.sample keeper])

/-- An empty page returned for a positive count sampled a head below the start. -/
theorem empty_page_origin (chunk : Chunk trace keeper) (nonzero : 0 < chunk.start)
    (requested : 0 < chunk.count) (empty : chunk.records = []) :
    chunk.head < chunk.start := by
  have length := congrArg List.length empty
  simp only [Chunk.records, List.length_take, List.length_drop, List.length_nil] at length
  have head := committed_history_length trace chunk.rpc.sample keeper
  change chunk.history.length = chunk.head at head
  rw [head] at length
  omega

/-- Keep only observations from completed attempts and valid BelowFloor
    replies. A caller can carry no accumulated records into the next attempt. -/
inductive Attempt (Payload : Type) where
  | page (page : Page Payload)
  | below (floor : Nat)
  | deleted
  | failed

inductive ReadOutcome (Payload : Type) where
  | page (page : Page Payload)
  | trimmed (floor : Nat)
  | deleted
  | unavailable

def selectPage (maxRecords : Nat) (fallback : List (Attempt Payload))
    (empty : Option (Page Payload) := none) (floor : Option Nat := none) : ReadOutcome Payload :=
  match fallback with
  | [] => match floor, empty with
    | some floor, _ => .trimmed floor
    | none, some page => .page page
    | none, none => .unavailable
  | .page page :: rest =>
    if maxRecords = 0 || !page.records.isEmpty then .page page
    else selectPage maxRecords rest (empty.or (some page)) floor
  | .below observed :: rest =>
    selectPage maxRecords rest empty (some (max observed (floor.getD 0)))
  | .deleted :: _ => .deleted
  | .failed :: rest => selectPage maxRecords rest empty floor

theorem selected_floor_source (maxRecords floor : Nat) (attempts : List (Attempt Payload))
    (empty : Option (Page Payload)) (prior : Option Nat)
    (chosen : selectPage maxRecords attempts empty prior = .trimmed floor) :
    prior = some floor ∨ .below floor ∈ attempts := by
  induction attempts generalizing empty prior with
  | nil =>
      cases prior <;> cases empty <;> simp_all [selectPage]
  | cons attempt rest ih =>
      cases attempt with
      | deleted => cases chosen
      | failed =>
          rcases ih _ _ chosen with earlier | later
          · exact Or.inl earlier
          · exact Or.inr (List.mem_cons_of_mem _ later)
      | page current =>
          unfold selectPage at chosen
          split at chosen
          · cases chosen
          · rcases ih _ _ chosen with earlier | later
            · exact Or.inl earlier
            · exact Or.inr (List.mem_cons_of_mem _ later)
      | below observed =>
          rcases ih _ _ chosen with earlier | later
          · have selected : max observed (prior.getD 0) = floor := Option.some.inj earlier
            cases prior with
            | none =>
                simp at selected
                exact Or.inr (selected ▸ List.mem_cons_self)
            | some saved =>
                change max observed saved = floor at selected
                rcases Nat.le_total observed saved with keepSaved | keepObserved
                · rw [Nat.max_eq_right keepSaved] at selected
                  exact Or.inl (congrArg some selected)
                · rw [Nat.max_eq_left keepObserved] at selected
                  exact Or.inr (selected ▸ List.mem_cons_self)
          · exact Or.inr (List.mem_cons_of_mem _ later)

theorem selected_floor_observed (start maxRecords floor : Nat) (attempts : List (Attempt Payload))
    (valid : ∀ f, .below f ∈ attempts → start < f)
    (empty : Option (Page Payload)) (prior : Option Nat)
    (priorValid : ∀ p, prior = some p → start < p)
    (chosen : selectPage maxRecords attempts empty prior = .trimmed floor) :
    start < floor := by
  rcases selected_floor_source maxRecords floor attempts empty prior chosen with earlier | later
  · exact priorValid floor earlier
  · exact valid floor later

/-- Selection keeps the head, floor and bytes of one complete attempt. -/
theorem selected_page_origin (maxRecords : Nat) (attempts : List (Attempt Payload))
    (empty : Option (Page Payload)) (floor : Option Nat) {page : Page Payload}
    (chosen : selectPage maxRecords attempts empty floor = .page page) :
    empty = some page ∨ .page page ∈ attempts := by
  induction attempts generalizing empty floor with
  | nil =>
      cases floor <;> cases empty <;> simp_all [selectPage]
  | cons attempt rest ih =>
      cases attempt with
      | deleted => cases chosen
      | failed | below =>
          rcases ih _ _ chosen with saved | member
          · exact Or.inl saved
          · exact Or.inr (List.mem_cons_of_mem _ member)
      | page current =>
          unfold selectPage at chosen
          split at chosen
          · cases chosen
            exact Or.inr List.mem_cons_self
          · rcases ih _ _ chosen with saved | member
            · cases empty with
              | none =>
                  simp only [Option.or, Option.some.injEq] at saved
                  subst page
                  exact Or.inr List.mem_cons_self
              | some => exact Or.inl saved
            · exact Or.inr (List.mem_cons_of_mem _ member)

def remainingWait (deadline now : Nat) : Nat := deadline - now

def parkRead (start count head wait : Nat) : Bool :=
  decide (0 < wait ∧ 0 < count ∧ head < start)

/-- When the keeper wakes on a state change, it rechecks the request. A
    successful poll with a positive count can finish early only after coverage. -/
theorem early_poll_has_head {start count head deadline now : Nat}
    (before : now < deadline) (positive : 0 < count)
    (returned : parkRead start count head (remainingWait deadline now) = false) : start ≤ head := by
  apply Nat.le_of_not_gt
  intro below
  have waiting : 0 < remainingWait deadline now := by unfold remainingWait; omega
  simp [parkRead, waiting, positive, below] at returned

theorem fallback_wait_budget {deadline first next : Nat} (ordered : first ≤ next) :
    remainingWait deadline next ≤ remainingWait deadline first := by
  unfold remainingWait
  omega

theorem no_wait_after_timeout {deadline now : Nat} (elapsed : deadline ≤ now) :
    remainingWait deadline now = 0 := by
  unfold remainingWait
  omega

#print axioms read_continuation
#print axioms empty_page_origin
#print axioms selected_floor_observed
#print axioms selected_floor_source
#print axioms selected_page_origin
#print axioms early_poll_has_head
#print axioms no_wait_after_timeout

end Logkeeper.StreamRead
