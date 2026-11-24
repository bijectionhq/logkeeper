import Logkeeper.StreamJournal

/-! The keeper WAL boundary. A frame has passed length, CRC and body validation before
it reaches this model. A completed entry supplies the durable image after applying the
entry, including both retained and staged records. -/

namespace Logkeeper.StreamWAL

set_option warningAsError true
set_option autoImplicit false

variable {Stream Image : Type} [DecidableEq Stream]

abbrev Entry (Stream Image : Type) := Stream × Image

inductive Frame (Stream Image : Type) where
  | start (stream : Stream)
  | middle (stream : Stream)
  | finish (entry : Entry Stream Image)
  | whole (entry : Entry Stream Image)
  | torn

def update {Value : Type} (f : Stream → Value) (stream : Stream) (value : Value) :
    Stream → Value :=
  fun s => if s = stream then value else f s

/-- Scan one segment. A torn suffix is allowed only in the newest segment.
    The fragment map is per stream and discarded at the end of each segment. -/
def scan (newest : Bool) (pending : Stream → Bool) :
    List (Frame Stream Image) → Option (List (Entry Stream Image))
  | [] => some []
  | .torn :: _ => if newest then some [] else none
  | .start stream :: frames =>
      if pending stream then none else scan newest (update pending stream true) frames
  | .middle stream :: frames =>
      if pending stream then scan newest pending frames else none
  | .finish entry :: frames =>
      if pending entry.1 then
        (scan newest (update pending entry.1 false) frames).map (entry :: ·)
      else none
  | .whole entry :: frames =>
      if pending entry.1 then none else (scan newest pending frames).map (entry :: ·)

theorem torn_tail_keeps_complete_entries (pending : Stream → Bool)
    (frames : List (Frame Stream Image)) :
    scan true pending (frames ++ [.torn]) = scan true pending frames := by
  induction frames generalizing pending with
  | nil => rfl -- torn tail
  | cons frame frames ih => cases frame <;> simp [scan, ih]

theorem torn_closed_segment_fails (pending : Stream → Bool) :
    scan false pending ([.torn] : List (Frame Stream Image)) = none := by
  rfl -- closed tear

theorem incomplete_entry_is_discarded (stream : Stream) :
    scan true (fun _ => false) ([.start stream, .middle stream, .torn] :
      List (Frame Stream Image)) = some [] := by
  simp [scan, update] -- partial entry

theorem fragments_are_demultiplexed (a b : Stream) (image : Image) (distinct : a ≠ b) :
    scan true (fun _ => false) [.start a, .finish (b, image)] = none := by
  simp [scan, update, distinct.symm] -- fragment owner

def replay (stream : Stream) (before : Image) (entries : List (Entry Stream Image)) : Image :=
  entries.foldl (fun image entry => if entry.1 = stream then entry.2 else image) before

/-- The old segment and the base image are fixed at the rotation boundary. Dirty
    streams can publish their checkpoint independently while new entries are synced. -/
structure Rotation (Stream Image : Type) where
  oldOnDisk : Bool := true
  checkpoints : Stream → Option Image := fun _ => none
  newer : List (Entry Stream Image) := []

def boundary (base : Stream → Image) (old : List (Entry Stream Image)) (stream : Stream) :
    Image := replay stream (base stream) old

def Dirty (old : List (Entry Stream Image)) (stream : Stream) : Prop :=
  ∃ entry ∈ old, entry.1 = stream

theorem clean_at_boundary (old : List (Entry Stream Image)) (stream : Stream) (before : Image)
    (clean : ¬ Dirty old stream) : replay stream before old = before := by
  induction old with
  | nil => rfl
  | cons entry old ih =>
      have other : entry.1 ≠ stream := fun same => clean ⟨entry, by simp, same⟩
      have rest : ¬ Dirty old stream := by
        rintro ⟨record, member, same⟩
        exact clean ⟨record, List.mem_cons_of_mem _ member, same⟩
      simpa only [replay, List.foldl_cons, ite_eq_right other] using ih rest

def readBack (base : Stream → Image) (old : List (Entry Stream Image))
    (rotation : Rotation Stream Image) (stream : Stream) : Image :=
  let prior := if rotation.oldOnDisk then boundary base old stream else base stream
  replay stream ((rotation.checkpoints stream).getD prior) rotation.newer

inductive Next (base : Stream → Image) (old : List (Entry Stream Image)) :
    Rotation Stream Image → Rotation Stream Image → Prop
  | append {r} (entries : List (Entry Stream Image)) :
      Next base old r { r with newer := r.newer ++ entries }
  | checkpoint {r} (stream : Stream) :
      Next base old r { r with
        checkpoints := update r.checkpoints stream (some (boundary base old stream)) }
  | retire {r} : (∀ stream, Dirty old stream →
      r.checkpoints stream = some (boundary base old stream)) →
      Next base old r { r with oldOnDisk := false }

inductive Reachable (base : Stream → Image) (old : List (Entry Stream Image)) :
    Rotation Stream Image → Prop
  | initial : Reachable base old {}
  | next {r r'} : Reachable base old r → Next base old r r' → Reachable base old r'

structure Sound (base : Stream → Image) (old : List (Entry Stream Image))
    (r : Rotation Stream Image) : Prop where
  exact : ∀ stream image, r.checkpoints stream = some image → image = boundary base old stream
  retirement : r.oldOnDisk = false → ∀ stream, Dirty old stream →
    r.checkpoints stream = some (boundary base old stream)

theorem next_sound {base : Stream → Image} {old : List (Entry Stream Image)} {r r'}
    (sound : Sound base old r) (step : Next base old r r') : Sound base old r' := by
  cases step with
  | append => exact ⟨sound.exact, sound.retirement⟩
  | checkpoint stream =>
      constructor
      · intro s image checkpoint
        by_cases same : s = stream
        · subst s
          exact (by simpa [update] using checkpoint.symm) -- checkpoint captures boundary
        · exact sound.exact s image (by simpa [update, same] using checkpoint)
      · intro retired s dirty
        by_cases same : s = stream
        · subst s
          simp [update]
        · simpa [update, same] using sound.retirement retired s dirty
  | retire all => exact ⟨sound.exact, fun _ => all⟩ -- retire after every checkpoint

theorem reachable_sound {base : Stream → Image} {old : List (Entry Stream Image)} {r}
    (reachable : Reachable base old r) : Sound base old r := by
  induction reachable with
  | initial => exact ⟨(fun _ _ h => by cases h), (fun h => by cases h)⟩
  | next _ step ih => exact next_sound ih step

theorem reopen_recovers_each_stream {base : Stream → Image} {old : List (Entry Stream Image)} {r}
    (reachable : Reachable base old r) (stream : Stream) :
    readBack base old r stream = replay stream (base stream) (old ++ r.newer) := by
  have sound := reachable_sound reachable
  rw [replay, List.foldl_append]
  unfold readBack
  have image : (r.checkpoints stream).getD
      (if r.oldOnDisk then boundary base old stream else base stream) = boundary base old stream := by
    cases checkpoint : r.checkpoints stream with
    | some saved => simpa using sound.exact stream saved checkpoint
    | none =>
        cases retired : r.oldOnDisk
        · by_cases dirty : Dirty old stream
          · rw [sound.retirement retired stream dirty] at checkpoint
            contradiction
          · simpa [retired, boundary] using (clean_at_boundary old stream (base stream) dirty).symm
        · simp
  change replay stream ((r.checkpoints stream).getD
    (if r.oldOnDisk then boundary base old stream else base stream)) r.newer = _
  rw [image]
  rfl

theorem background_checkpoint_witness :
    ∃ before after : Rotation Bool Nat,
      Reachable (fun _ => 0) [(false, 1), (true, 2)] before ∧
      Reachable (fun _ => 0) [(false, 1), (true, 2)] after ∧
      before.checkpoints false = some 1 ∧ before.checkpoints true = none ∧
      after.oldOnDisk = false ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] before false = 3 ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] before true = 2 ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] after false = 3 ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] after true = 4 := by
  let start : Rotation Bool Nat := {}
  let first := { start with checkpoints := update start.checkpoints false (some 1) }
  let before := { first with newer := [(false, 3)] }
  let second := { before with checkpoints := update before.checkpoints true (some 2) }
  let appended := { second with newer := before.newer ++ [(true, 4)] }
  let after := { appended with oldOnDisk := false }
  have rf : Reachable (fun _ => 0) [(false, 1), (true, 2)] first :=
    .next .initial (.checkpoint false)
  have rb : Reachable (fun _ => 0) [(false, 1), (true, 2)] before :=
    .next rf (.append [(false, 3)])
  have rs : Reachable (fun _ => 0) [(false, 1), (true, 2)] second :=
    .next rb (.checkpoint true)
  have ra : Reachable (fun _ => 0) [(false, 1), (true, 2)] appended :=
    .next rs (.append [(true, 4)])
  have retired : Reachable (fun _ => 0) [(false, 1), (true, 2)] after :=
    .next ra (.retire (fun stream _ => by cases stream <;> rfl))
  exact ⟨before, after, rb, retired, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms torn_tail_keeps_complete_entries
#print axioms torn_closed_segment_fails
#print axioms incomplete_entry_is_discarded
#print axioms fragments_are_demultiplexed
#print axioms next_sound
#print axioms reopen_recovers_each_stream
#print axioms background_checkpoint_witness

end Logkeeper.StreamWAL
