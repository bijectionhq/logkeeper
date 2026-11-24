import Logkeeper.StreamJournal

/-! The keeper WAL boundary. Frames have passed length, CRC and body validation.
A completed entry supplies the durable image after applying the entry, including
both retained and staged records. -/

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

def update (f : Stream → Bool) (stream : Stream) (value : Bool) : Stream → Bool :=
  fun s => if s = stream then value else f s

abbrev Scan (Stream Image : Type) := List (Entry Stream Image) × (Stream → Bool)

/-- Only the newest segment can have a torn final frame. Only completed
    entries contribute an image. -/
def scan (newest : Bool) (pending : Stream → Bool) :
    List (Frame Stream Image) → Option (Scan Stream Image)
  | [] => some ([], pending)
  | .torn :: _ => if newest then some ([], pending) else none
  | .start stream :: frames =>
      if pending stream then none else scan newest (update pending stream true) frames
  | .middle stream :: frames =>
      if pending stream then scan newest pending frames else none
  | .finish entry :: frames =>
      if pending entry.1 then
        (scan newest (update pending entry.1 false) frames).map fun (entries, remaining) =>
          (entry :: entries, remaining)
      else none
  | .whole entry :: frames =>
      if pending entry.1 then none
      else (scan newest pending frames).map fun (entries, remaining) => (entry :: entries, remaining)

/-- A continuation marker carries unfinished fragments across a physical rollover.
    A fresh segment after reopening clears them. -/
def scanSegment (newest continued : Bool) (pending : Stream → Bool)
    (frames : List (Frame Stream Image)) : Option (Scan Stream Image) :=
  scan newest (if continued then pending else fun _ => false) frames

theorem torn_tail_keeps_complete_entries (pending : Stream → Bool)
    (frames : List (Frame Stream Image)) :
    scan true pending (frames ++ [.torn]) = scan true pending frames := by
  induction frames generalizing pending with
  | nil => rfl
  | cons frame frames ih => cases frame <;> simp [scan, ih]

theorem torn_closed_segment_fails (pending : Stream → Bool) :
    scan false pending ([.torn] : List (Frame Stream Image)) = none := by
  rfl

theorem incomplete_entry_is_discarded (stream : Stream) :
    (scan true (fun _ => false) ([.start stream, .middle stream, .torn] :
      List (Frame Stream Image))).map Prod.fst = some [] := by
  simp [scan, update]

theorem fragments_are_demultiplexed (a b : Stream) (image : Image) (distinct : a ≠ b) :
    scan true (fun _ => false) [.start a, .finish (b, image)] = none := by
  simp [scan, update, distinct.symm]

theorem continued_fragments_finish_after_rollover (a b : Stream) (x y : Image) (distinct : a ≠ b) :
    ((scanSegment false false (fun _ => false) ([.start a] : List (Frame Stream Image))).bind fun prior =>
      scanSegment true true prior.2 [.whole (b, y), .finish (a, x), .torn]).map Prod.fst =
      some [(b, y), (a, x)] := by
  simp [scanSegment, scan, update, distinct.symm]

theorem fresh_segment_discards_incomplete_entries (stream : Stream) (image : Image) :
    scanSegment true false (fun _ => true) [.finish (stream, image)] = none := by
  rfl

def replay (stream : Stream) (before : Image) (entries : List (Entry Stream Image)) : Image :=
  entries.foldl (fun image entry => if entry.1 = stream then entry.2 else image) before

/-- The boundary is captured before a checkpoint starts. The index publication
    covers the entire prefix in one step. Newer synced entries accrue independently. -/
structure Rotation (Stream Image : Type) where
  oldOnDisk : Bool := true
  packDurable : Bool := false
  index : Option (Stream → Image) := none
  newer : List (Entry Stream Image) := []

def boundary (base : Stream → Image) (old : List (Entry Stream Image)) (stream : Stream) :
    Image := replay stream (base stream) old

def readBack (base : Stream → Image) (old : List (Entry Stream Image))
    (r : Rotation Stream Image) (stream : Stream) : Option Image :=
  match r.index with
  | some images =>
      if r.packDurable then some (replay stream (images stream) r.newer) else none
  | none =>
      if r.oldOnDisk then some (replay stream (boundary base old stream) r.newer) else none

inductive Next (base : Stream → Image) (old : List (Entry Stream Image)) :
    Rotation Stream Image → Rotation Stream Image → Prop
  | append {r} (entries : List (Entry Stream Image)) :
      Next base old r { r with newer := r.newer ++ entries }
  | syncPack {r} : Next base old r { r with packDurable := true }
  | publish {r} : r.packDurable = true →
      Next base old r { r with index := some (boundary base old) }
  | retire {r} : r.index.isSome = true →
      Next base old r { r with oldOnDisk := false }

inductive Reachable (base : Stream → Image) (old : List (Entry Stream Image)) :
    Rotation Stream Image → Prop
  | initial : Reachable base old {}
  | next {r r'} : Reachable base old r → Next base old r r' → Reachable base old r'

structure Sound (base : Stream → Image) (old : List (Entry Stream Image))
    (r : Rotation Stream Image) : Prop where
  exact : ∀ images, r.index = some images → images = boundary base old
  referenced : r.index.isSome = true → r.packDurable = true
  retirement : r.oldOnDisk = false → r.index.isSome = true

theorem next_sound {base : Stream → Image} {old : List (Entry Stream Image)} {r r'}
    (sound : Sound base old r) (step : Next base old r r') : Sound base old r' := by
  cases step with
  | append => exact ⟨sound.exact, sound.referenced, sound.retirement⟩
  | syncPack => exact ⟨sound.exact, fun _ => rfl, sound.retirement⟩
  | publish synced =>
      exact ⟨fun _ captured => (Option.some.inj captured).symm, fun _ => synced, fun _ => rfl⟩
  | retire published =>
      exact ⟨sound.exact, sound.referenced, fun _ => published⟩

theorem reachable_sound {base : Stream → Image} {old : List (Entry Stream Image)} {r}
    (reachable : Reachable base old r) : Sound base old r := by
  induction reachable with
  | initial => exact ⟨(fun _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
  | next _ step ih => exact next_sound ih step

theorem reopen_recovers_each_stream {base : Stream → Image} {old : List (Entry Stream Image)} {r}
    (reachable : Reachable base old r) (stream : Stream) :
    readBack base old r stream = some (replay stream (base stream) (old ++ r.newer)) := by
  have sound := reachable_sound reachable
  have suffix : replay stream (base stream) (old ++ r.newer) =
      replay stream (boundary base old stream) r.newer := by
    simp [replay, boundary, List.foldl_append]
  rw [suffix]
  cases published : r.index with
  | some images =>
      have exactImage := sound.exact images published
      have packed := sound.referenced (by simp [published])
      simp [readBack, published, packed, exactImage]
  | none =>
      cases oldOnDisk : r.oldOnDisk
      · have impossible := sound.retirement oldOnDisk
        simp [published] at impossible
      · simp [readBack, published, oldOnDisk]

theorem background_checkpoint_witness :
    ∃ copying published retired : Rotation Bool Nat,
      Reachable (fun _ => 0) [(false, 1), (true, 2)] copying ∧
      Reachable (fun _ => 0) [(false, 1), (true, 2)] published ∧
      Reachable (fun _ => 0) [(false, 1), (true, 2)] retired ∧
      copying.index.isNone = true ∧ published.oldOnDisk = true ∧ retired.oldOnDisk = false ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] copying false = some 3 ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] copying true = some 2 ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] published false = some 3 ∧
      readBack (fun _ => 0) [(false, 1), (true, 2)] retired true = some 4 := by
  let start : Rotation Bool Nat := {}
  let copying := { start with newer := [(false, 3)] }
  let packed := { copying with packDurable := true }
  let published := { packed with index := some (boundary (fun _ => 0) [(false, 1), (true, 2)]) }
  let appended := { published with newer := published.newer ++ [(true, 4)] }
  let retired := { appended with oldOnDisk := false }
  have rc : Reachable (fun _ => 0) [(false, 1), (true, 2)] copying :=
    .next .initial (.append [(false, 3)])
  have rp : Reachable (fun _ => 0) [(false, 1), (true, 2)] published :=
    .next (.next rc .syncPack) (.publish rfl)
  have rr : Reachable (fun _ => 0) [(false, 1), (true, 2)] retired :=
    .next (.next rp (.append [(true, 4)])) (.retire rfl)
  exact ⟨copying, published, retired, rc, rp, rr, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms torn_tail_keeps_complete_entries
#print axioms torn_closed_segment_fails
#print axioms incomplete_entry_is_discarded
#print axioms fragments_are_demultiplexed
#print axioms continued_fragments_finish_after_rollover
#print axioms fresh_segment_discards_incomplete_entries
#print axioms next_sound
#print axioms reopen_recovers_each_stream
#print axioms background_checkpoint_witness

end Logkeeper.StreamWAL
