import Logkeeper.SelectionFence

set_option warningAsError true

namespace Logkeeper.ConsensusAdditions.SegmentedWAL

structure LogId where
  index : Nat
  term : Nat
  deriving DecidableEq, Repr

/-- One stream and ownership generation of the shared WAL. -/
inductive Record where
  /-- `Record::Append`: Raft entries from index `first`, replacing the
  suffix there. -/
  | append (first : Nat) (ids : List LogId)
  /-- `Record::Truncate`: drops the entries from `since`. -/
  | truncate (since : Nat)
  | committed (id : LogId)
  | relocate (oldCopy newCopy : Nat)
  deriving DecidableEq, Repr

/-- The log holds the entry of index `i` at position `i`. -/
structure State where
  entries : List LogId := []
  committed : Option LogId := none
  deriving DecidableEq, Repr

/-- `WalState::apply` in storage/wal.rs. A non-contiguous append makes the
real decoder refuse the WAL; the model leaves the state as it was, and the
theorems below only replay appends the writer emits. An append or a
truncation that replaces the entry the commit index names clears it. -/
def apply (state : State) : Record → State
  | .append first ids =>
    if first ≤ state.entries.length then
      let entries := state.entries.take first ++ ids
      { entries
        committed := if state.committed.any (fun known =>
            decide (first ≤ known.index ∧ entries[known.index]? ≠ some known)) then none
          else state.committed }
    else state
  | .truncate since =>
    { entries := state.entries.take since
      committed := if state.committed.any (fun known => decide (since ≤ known.index)) then none
        else state.committed }
  | .committed id =>
    if state.committed.all (fun prior => prior.index < id.index) then
      { state with committed := some id }
    else state
  | .relocate .. => state

/-- Frame lengths and CRCs are checked by the decoder. A successfully decoded
frame includes its segment and start offset, along with the decoded body. -/
structure Frame where
  segment : Nat
  offset : Nat
  record : Record
  deriving DecidableEq, Repr

inductive Cell where
  | complete (frame : Frame)
  | badCrc
  | torn
  deriving DecidableEq, Repr

def scan : List Cell → Option (List Frame)
  | [] => some []
  | .complete frame :: tail => (scan tail).map (frame :: ·)
  | _ => none

private theorem scan_complete (frames : List Frame) :
    scan (frames.map Cell.complete) = some frames := by
  induction frames <;> simp_all [scan]

def reduce (base : State) (frames : List Frame) : State :=
  frames.foldl (fun state frame => apply state frame.record) base

/-- Symbolic SHA-256 chain. Equality of chains stands for equality of frame
sequences under the same incarnation, including the checked frame boundaries.
The real digest is finite and its binding is a premise of the model. -/
abbrev Chain := List Frame

inductive Format where
  | v5
  | v6
  deriving DecidableEq, Repr

structure Checkpoint where
  format : Format
  chain : Chain
  base : State
  deriving DecidableEq, Repr

def capture (format : Format) (capturedFrames : Chain) : Checkpoint :=
  let base := reduce {} capturedFrames
  ⟨format, capturedFrames, if format = .v6 then base else { base with committed := none }⟩

structure Slot where
  sequence : Nat
  /-- Rank of the byte cursor (segment, offset) among whole-frame ends. -/
  endRank : Nat
  chain : Chain
  checkpoint : Option Checkpoint := none
  deriving DecidableEq, Repr

abbrev Slots := Option Slot × Option Slot

def select (slots : Slots) : Option Slot :=
  match SelectionFence.selectSlot (slots.1.map Slot.sequence) (slots.2.map Slot.sequence) with
  | .ok (some false) => slots.1
  | .ok (some true) => slots.2
  | _ => none

def install (current : Slot) (atB : Bool) (other : Option Slot) : Slots :=
  if atB then (other, some current) else (some current, other)

private theorem selects_current (current : Slot) (atB : Bool) (other : Option Slot)
    (older : ∀ slot ∈ other, slot.sequence < current.sequence) :
    select (install current atB other) = some current := by
  cases atB <;> cases other with
  | none => rfl
  | some other =>
    have lt := older other rfl
    simp [install, select, SelectionFence.selectSlot, Nat.ne_of_lt lt, Nat.ne_of_gt lt,
      show ¬ current.sequence < other.sequence by omega, lt]

inductive Cut where
  | staged
  | tornData
  | dataSynced
  | tornSlot
  | wholeSlot
  | slotSynced
  | replied
  deriving DecidableEq, Repr

/-- Before boundary sync returns, a crash may leave a torn or complete
alternate slot. The current slot survives because writes target its peer. -/
def Cut.publishes : Cut → Bool
  | .wholeSlot | .slotSynced | .replied => true
  | _ => false

def crashSlots (cut : Cut) (current next : Slot) (currentAtB : Bool) : Slots :=
  install current currentAtB
    (if cut.publishes then some next else none)

theorem crash_selects_published_slot (cut : Cut) (current next : Slot) (atB : Bool)
    (advances : current.sequence < next.sequence) :
    select (crashSlots cut current next atB) =
      some (if cut.publishes then next else current) := by
  by_cases published : cut.publishes = true
  · have exchange : install current atB (some next) = install next (!atB) (some current) := by
      cases atB <;> rfl
    simp only [crashSlots, published, ite_true, exchange]
    exact selects_current _ _ _ (by intro slot same; cases same; exact advances)
  · have unpublished : cut.publishes = false := Bool.eq_false_iff.mpr published
    simp only [crashSlots, unpublished, Bool.false_eq_true, ite_false]
    exact selects_current _ _ _ (by simp)

structure Media where
  /-- The scan starts at the checkpoint cursor. This check covers missing
  segment names and invalid segment headers in the selected interval. -/
  headersValid : Bool
  cells : List Cell
  /-- The exact authenticated image named in the selected slot, if readable.
  A digest, size or live extent failure makes the image unavailable. -/
  image : Option Checkpoint := none

def replay (slot : Slot) (media : Media) : Option State := do
  if !media.headersValid || slot.checkpoint != media.image then none else
    let capturedFrames := media.image.elim [] Checkpoint.chain
    let base := media.image.elim {} Checkpoint.base
    if slot.endRank < capturedFrames.length then none else
      let count := slot.endRank - capturedFrames.length
      let frames ← scan (media.cells.take count)
      if frames.length = count ∧ capturedFrames ++ frames = slot.chain then
        some (reduce base frames)
      else none

/-- A replacement can become selected once it is synced and its exact base and
extents remain available. This is the installation implication from studies
13 and 25 at the WAL boundary. The suffix can grow while the image is written. -/
theorem v6_checkpoint_replays_intervening_frames (sequence : Nat) (capturedFrames suffix : Chain)
    (tail : List Cell) :
    let cp := capture .v6 capturedFrames
    replay ⟨sequence, (capturedFrames ++ suffix).length, capturedFrames ++ suffix, some cp⟩
      ⟨true, suffix.map Cell.complete ++ tail, some cp⟩ = some (reduce {} (capturedFrames ++ suffix)) := by
  simp [replay, capture, scan_complete, reduce, List.foldl_append]

/-- The trusted slot detects loss, reordering or substitution in its selected
interval even when the replacement frames have valid CRCs. -/
theorem rollback_rejected (slot : Slot) (media : Media)
    (changed : ∀ frames,
      scan (media.cells.take (slot.endRank - (media.image.elim [] Checkpoint.chain).length)) =
        some frames → (media.image.elim [] Checkpoint.chain) ++ frames ≠ slot.chain) :
    replay slot media = none := by
  unfold replay
  split
  · rfl
  · dsimp only
    split
    · rfl
    · cases read : scan (media.cells.take (slot.endRank -
        (media.image.elim [] Checkpoint.chain).length)) with
      | none => rfl
      | some frames =>
        change (if _ then _ else none) = none
        split
        · rename_i same
          exact absurd same.2 (changed frames read)
        · rfl

theorem missing_selected_frame_rejected (sequence : Nat) (frames : Chain) (last : Frame) :
    replay ⟨sequence, frames.length + 1, frames ++ [last], none⟩
      ⟨true, frames.map Cell.complete, none⟩ = none := by
  simp [replay, scan_complete, List.take_of_length_le]

/-- A later unselected segment or torn tail is outside the replay cursor. -/
theorem unselected_tail_is_ignored (sequence : Nat) (frames : Chain) (tail : List Cell) :
    replay ⟨sequence, frames.length, frames, none⟩ ⟨true, frames.map Cell.complete ++ tail, none⟩ =
      some (reduce {} frames) := by
  simp [replay, scan_complete]

def flatten (rounds : List Chain) : Chain := rounds.flatten

def selectedRounds (acknowledged : List Chain) (pending : Chain) (cut : Cut) : List Chain :=
  if cut.publishes then acknowledged ++ [pending] else acknowledged

/-- Study 25's prefix law, with a single serialized boundary publication in
flight. A completed publication may have no successful reply. -/
theorem crash_preserves_acknowledged_rounds (acknowledged : List Chain)
    (pending : Chain) (cut : Cut) :
    acknowledged <+: selectedRounds acknowledged pending cut ∧
    selectedRounds acknowledged pending cut <+: acknowledged ++ [pending] := by
  cases cut <;> simp [selectedRounds, Cut.publishes, List.prefix_append]

/-- Replay composition for any number of earlier acknowledged rounds. The CPU
may be interrupted in any phase of the next round. Headers, bytes and the
selected image are stable according to the data-sync-before-slot ordering. -/
theorem crash_replays_whole_published_rounds (acknowledged : List Chain)
    (pending capturedFrames : Chain) (cut : Cut) (tail : List Cell) (atB : Bool)
    (captured : capturedFrames <+: flatten acknowledged) :
    let earlier := flatten acknowledged
    let later := earlier ++ pending
    let cp := capture .v6 capturedFrames
    let old : Slot := ⟨1, earlier.length, earlier, some cp⟩
    let next : Slot := ⟨2, later.length, later, some cp⟩
    let whole := flatten (selectedRounds acknowledged pending cut)
    let media : Media := ⟨true, (whole.drop capturedFrames.length).map Cell.complete ++ tail, some cp⟩
    (select (crashSlots cut old next atB)).bind (fun slot => replay slot media) =
      some (reduce {} whole) := by
  dsimp only
  have rebuild (sequence : Nat) (whole : Chain) (keeps : capturedFrames <+: whole) :
      replay ⟨sequence, whole.length, whole, some (capture .v6 capturedFrames)⟩
        ⟨true, (whole.drop capturedFrames.length).map Cell.complete ++ tail, some (capture .v6 capturedFrames)⟩ =
      some (reduce {} whole) := by
    obtain ⟨suffix, rfl⟩ := keeps
    simpa using v6_checkpoint_replays_intervening_frames sequence capturedFrames suffix tail
  rw [crash_selects_published_slot _ _ _ _ (show 1 < 2 by decide)]
  have later : capturedFrames <+: flatten acknowledged ++ pending :=
    captured.trans (List.prefix_append _ _)
  have flattenMore : flatten (acknowledged ++ [pending]) = flatten acknowledged ++ pending := by
    simp [flatten]
  cases cut <;> simp only [selectedRounds, Cut.publishes, Bool.false_eq_true, ite_false,
    ite_true, Option.bind_some, flattenMore] <;> exact rebuild _ _ (by assumption)

/-- This equivalence describes a fresh carried watermark. A later truncate,
replacement, or reset can erase it, and an earlier equal index is excluded. -/
theorem commit_index_follows_its_round (base : Chain) (id : LogId) (address : Nat × Nat)
    (cut : Cut) (advances : (reduce {} base).committed.all (fun prior => prior.index < id.index) = true) :
    (reduce {} (flatten (selectedRounds [base] [⟨address.1, address.2, .committed id⟩] cut))).committed =
      some id ↔ cut.publishes = true := by
  have fresh : (reduce {} base).committed ≠ some id := by
    intro equal
    simp [equal] at advances
  have installCommit :
      (reduce {} (base ++ [⟨address.1, address.2, .committed id⟩])).committed = some id := by
    rw [reduce, List.foldl_append]
    change (apply (reduce {} base) (.committed id)).committed = some id
    simp [apply, advances]
  cases cut <;> simp [selectedRounds, Cut.publishes, flatten, installCommit, fresh]

/-- The commit index names an entry of the log. Recovery keeps the
survivor's log through it (`keeper/recovery.rs`), so it must. -/
def Sound (state : State) : Prop :=
  ∀ id, state.committed = some id → state.entries[id.index]? = some id

/-- The writer's discipline: a `Record::Committed` frame names an entry the
log holds when the frame is written (OpenRaft only reports a commit index
it has matched locally). -/
def Disciplined : State → List Frame → Prop
  | _, [] => True
  | state, frame :: rest =>
    (∀ id, frame.record = .committed id → state.entries[id.index]? = some id) ∧
      Disciplined (apply state frame.record) rest

theorem sound_step (state : State) (record : Record) (sound : Sound state)
    (named : ∀ id, record = .committed id → state.entries[id.index]? = some id) :
    Sound (apply state record) := by
  cases record with
  | append first ids =>
    simp only [apply]
    split
    · rename_i fits
      intro id committed
      split at committed
      · contradiction
      · rename_i kept
        dsimp only at committed ⊢
        have old := sound id committed
        simp only [committed, Option.any_some, decide_eq_true_eq, not_and, Decidable.not_not] at kept
        by_cases above : first ≤ id.index
        · exact kept above
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt (by omega), old]
    · exact sound
  | truncate since =>
    intro id committed
    simp only [apply] at committed ⊢
    split at committed
    · contradiction
    · rename_i kept
      simp only [committed, Option.any_some, decide_eq_true_eq] at kept
      rw [List.getElem?_take_of_lt (by omega), sound id committed]
  | committed id =>
    simp only [apply]
    split
    · intro named' same
      cases same
      exact named _ rfl
    · exact sound
  | relocate => exact sound

theorem reduce_sound (base : State) (frames : List Frame) (sound : Sound base)
    (disciplined : Disciplined base frames) : Sound (reduce base frames) := by
  induction frames generalizing base with
  | nil => exact sound
  | cons frame rest prior =>
    exact prior _ (sound_step _ _ sound disciplined.1) disciplined.2

theorem disciplined_prefix {base : State} {frames more : List Frame}
    (disciplined : Disciplined base (frames ++ more)) : Disciplined base frames := by
  induction frames generalizing base with
  | nil => trivial
  | cons frame rest prior => exact ⟨disciplined.1, prior disciplined.2⟩

/-- At every crash point, the commit index replay recovers names an entry of
the replayed log, from an LKRWAL06 base. Appends that replace the entry it
named, and truncations below it, cleared it on the way. -/
theorem crash_replays_a_sound_commit_index (acknowledged : List Chain)
    (pending capturedFrames : Chain) (cut : Cut) (tail : List Cell) (atB : Bool)
    (captured : capturedFrames <+: flatten acknowledged)
    (disciplined : Disciplined {} (flatten acknowledged ++ pending)) :
    let earlier := flatten acknowledged
    let later := earlier ++ pending
    let cp := capture .v6 capturedFrames
    let old : Slot := ⟨1, earlier.length, earlier, some cp⟩
    let next : Slot := ⟨2, later.length, later, some cp⟩
    let whole := flatten (selectedRounds acknowledged pending cut)
    let media : Media := ⟨true, (whole.drop capturedFrames.length).map Cell.complete ++ tail, some cp⟩
    ∃ state, (select (crashSlots cut old next atB)).bind (fun slot => replay slot media) = some state ∧
      Sound state := by
  intro earlier later cp old next whole media
  refine ⟨_, crash_replays_whole_published_rounds acknowledged pending capturedFrames cut tail atB
    captured, reduce_sound {} _ (by simp [Sound]) ?_⟩
  have selected : whole <+: flatten acknowledged ++ pending := by
    have := (crash_preserves_acknowledged_rounds acknowledged pending cut).2
    obtain ⟨rest, same⟩ := this
    refine ⟨flatten rest, ?_⟩
    have := congrArg flatten same
    simpa [whole, flatten, List.flatten_append] using this
  obtain ⟨rest, same⟩ := selected
  rw [← same] at disciplined
  exact disciplined_prefix disciplined

/-- Why LKRWAL06 carries the commit index: an LKRWAL05 base drops it, and a
replay with no later `Record::Committed` frame recovers none, so recovery
refuses the survivor. The LKRWAL06 base keeps it. -/
theorem v5_checkpoint_forgets_the_commit_index :
    let frames : Chain := [⟨0, 0, .append 0 [⟨0, 1⟩]⟩, ⟨0, 1, .committed ⟨0, 1⟩⟩]
    (replay ⟨1, 2, frames, some (capture .v5 frames)⟩ ⟨true, [], some (capture .v5 frames)⟩).map
        State.committed = some none ∧
      (replay ⟨1, 2, frames, some (capture .v6 frames)⟩ ⟨true, [], some (capture .v6 frames)⟩).map
        State.committed = some (some ⟨0, 1⟩) := by
  decide

theorem relocate_changes_no_replayed_state (before : State) (source target : Nat) :
    apply before (.relocate source target) = before := rfl

#print axioms crash_selects_published_slot
#print axioms v6_checkpoint_replays_intervening_frames
#print axioms rollback_rejected
#print axioms missing_selected_frame_rejected
#print axioms unselected_tail_is_ignored
#print axioms crash_preserves_acknowledged_rounds
#print axioms crash_replays_whole_published_rounds
#print axioms commit_index_follows_its_round
#print axioms relocate_changes_no_replayed_state
#print axioms sound_step
#print axioms reduce_sound
#print axioms crash_replays_a_sound_commit_index
#print axioms v5_checkpoint_forgets_the_commit_index

end Logkeeper.ConsensusAdditions.SegmentedWAL
