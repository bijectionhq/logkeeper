import Logkeeper.StreamJournal

/-! The keeper WAL byte and publication boundary. A completed entry supplies
the durable image after applying the entry, including retained and staged records. -/

namespace Logkeeper.StreamWAL

set_option warningAsError true
set_option autoImplicit false

variable {Stream Image : Type} [DecidableEq Stream]

abbrev Entry (Stream Image : Type) := Stream × Image

def FrameBodyFits (remaining length limit : Nat) : Prop :=
  8 + length ≤ remaining ∧ length ≤ limit

def ChecksumMatches (expected actual : Nat) : Prop :=
  expected = actual

def ExtentFits (sequence boundary offset length limit size : Nat) : Prop :=
  sequence ≤ boundary ∧ length ≤ limit ∧ offset + length ≤ size

def PlaceExtent (offset length : Nat) : Option (Nat × Nat) :=
  if length ≤ 4294967295 ∧ offset + length ≤ 18446744073709551615 then
    some (length, offset + length)
  else none

abbrev Bytes := List UInt8

def FrameWire (word : Nat → Bytes) (crc : Bytes → Nat) (body : Bytes) : Bytes :=
  word (body.length % 2 ^ 32) ++ word (crc body) ++ body

def FragmentWire (stream : Bytes) (flags : UInt8) : Bytes :=
  stream ++ [flags]

def IndexWire (magic next count : Bytes) (word : Nat → Bytes) (crc : Bytes → Nat) : Bytes :=
  magic ++ (next ++ count) ++ word (crc (next ++ count))

def ExtentWire (epoch sequence offset length crc : Bytes) : Bytes :=
  epoch ++ sequence ++ offset ++ length ++ crc

def StreamIndexWire (stream : Bytes) (deleted : UInt8) (size view retained staged : Bytes) : Bytes :=
  stream ++ [deleted] ++ size ++ view ++ retained ++ staged

/-- The word codec is instantiated by the verified four-byte big-endian codec.
    The CRC parameter is the deterministic checksum of the exact body. -/
structure WordCodec where
  encode : Nat → Bytes
  decode : Bytes → Nat
  width : ∀ n, (encode n).length = 4
  roundTrip : ∀ n, n < 2 ^ 32 → decode (encode n) = n

def EncodeWord32 (n : Nat) : Bytes :=
  let word := BitVec.ofNat 32 n
  [UInt8.ofBitVec (word.extractLsb' 24 8), UInt8.ofBitVec (word.extractLsb' 16 8),
   UInt8.ofBitVec (word.extractLsb' 8 8), UInt8.ofBitVec (word.extractLsb' 0 8)]

def DecodeWord32 (bytes : Bytes) : Nat :=
  let byte := fun (index : Nat) => bytes[index]!.toBitVec.zeroExtend 32
  ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3).toNat

theorem word32_round_trip (n : Nat) (bounded : n < 2 ^ 32) :
    DecodeWord32 (EncodeWord32 n) = n := by
  have merged (bits : BitVec 32) :
      ((bits.extractLsb' 24 8).zeroExtend 32 <<< 24) |||
        ((bits.extractLsb' 16 8).zeroExtend 32 <<< 16) |||
        ((bits.extractLsb' 8 8).zeroExtend 32 <<< 8) |||
        (bits.extractLsb' 0 8).zeroExtend 32 = bits := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i inside
    have lane (start : Nat) :
        (((bits.extractLsb' start 8).zeroExtend 32) <<< start).getLsbD i =
          if start ≤ i ∧ i < start + 8 then bits.getLsbD i else false := by
      by_cases before : i < start
      · simp [before, show ¬ start ≤ i by omega]
      · have lower : start ≤ i := by omega
        have add : start + (i - start) = i := by omega
        by_cases within : i < start + 8
        · have offset : i - start < 8 := by omega
          simp [inside, before, lower, within, offset, add]
        · have offset : ¬ i - start < 8 := by omega
          simp [inside, before, lower, within, offset]
    have low : ((bits.extractLsb' 0 8).zeroExtend 32).getLsbD i =
        if i < 8 then bits.getLsbD i else false := by simpa using lane 0
    simp only [BitVec.getLsbD_or, lane, low]
    by_cases a : i < 8
    · simp [a, show ¬ 8 ≤ i by omega, show ¬ 16 ≤ i by omega, show ¬ 24 ≤ i by omega]
    by_cases b : i < 16
    · simp [a, b, show 8 ≤ i by omega, show ¬ 16 ≤ i by omega, show ¬ 24 ≤ i by omega]
    by_cases c : i < 24
    · simp [a, b, c, show 16 ≤ i by omega, show ¬ 24 ≤ i by omega]
    simp [a, b, c, inside, show 24 ≤ i by omega]
  simp [EncodeWord32, DecodeWord32, merged, Nat.mod_eq_of_lt bounded]

def word32 : WordCodec :=
  ⟨EncodeWord32, DecodeWord32, fun _ => rfl, word32_round_trip⟩

def FrameDecodeWire (bytes body : Bytes) (declared stored actual limit : Nat) : Prop :=
  bytes.length = 8 + declared ∧ declared ≤ limit ∧ body = bytes.drop 8 ∧ stored = actual

instance (bytes body : Bytes) (declared stored actual limit : Nat) :
    Decidable (FrameDecodeWire bytes body declared stored actual limit) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def decodeFrame (word : WordCodec) (crc : Bytes → Nat) (limit : Nat) (bytes : Bytes) :
    Option Bytes :=
  let length := word.decode (bytes.take 4)
  let body := bytes.drop 8
  if FrameDecodeWire bytes body length (word.decode ((bytes.drop 4).take 4)) (crc body) limit
      ∧ length < 2 ^ 32 then some body else none

private theorem encoded_frame_fields (word : WordCodec) (len stored : Nat) (body : Bytes) :
    let bytes := word.encode len ++ word.encode stored ++ body
    bytes.take 4 = word.encode len ∧ (bytes.drop 4).take 4 = word.encode stored ∧
      bytes.drop 8 = body ∧ bytes.length = 8 + body.length := by
  dsimp
  have first : (word.encode len).length = 4 := word.width len
  have second : (word.encode stored).length = 4 := word.width stored
  constructor
  · rw [List.append_assoc, ← first, List.take_left]
  constructor
  · have drop : (word.encode len ++ (word.encode stored ++ body)).drop 4 =
        word.encode stored ++ body := by rw [← first, List.drop_left]
    rw [List.append_assoc, drop, ← second, List.take_left]
  constructor
  · have both : (word.encode len ++ word.encode stored).length = 8 := by simp [first, second]
    rw [← both, List.drop_left]
  · simp [first, second]
    omega

theorem encoded_frame_decodes (word : WordCodec) (crc : Bytes → Nat) (body : Bytes) (limit : Nat)
    (bounded : body.length < 2 ^ 32) (fits : body.length ≤ limit)
    (checksumBound : crc body < 2 ^ 32) :
    decodeFrame word crc limit (FrameWire word.encode crc body) = some body := by
  have fields := encoded_frame_fields word body.length (crc body) body
  simp only [FrameWire, Nat.mod_eq_of_lt bounded, decodeFrame, FrameDecodeWire]
  rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2, word.roundTrip _ bounded]
  simp [fits, bounded, word.roundTrip _ checksumBound]

theorem encoded_frame_truncation (word : WordCodec) (crc : Bytes → Nat) (body : Bytes)
    (limit cut : Nat) (bounded : body.length < 2 ^ 32) (cutInside : cut < 8 + body.length) :
    decodeFrame word crc limit ((FrameWire word.encode crc body).take cut) = none := by
  have fields := encoded_frame_fields word body.length (crc body) body
  have total : (FrameWire word.encode crc body).length = 8 + body.length := by
    simpa [FrameWire, Nat.mod_eq_of_lt bounded, List.append_assoc] using fields.2.2.2
  by_cases short : cut < 4
  · simp [decodeFrame, FrameDecodeWire, List.length_take, total, Nat.min_eq_left (by omega : cut ≤ 8 + body.length)]
    omega
  · have head : ((FrameWire word.encode crc body).take cut).take 4 = word.encode body.length := by
      rw [List.take_take, Nat.min_eq_left (by omega : 4 ≤ cut)]
      simpa [FrameWire, Nat.mod_eq_of_lt bounded, List.append_assoc] using fields.1
    simp [decodeFrame, FrameDecodeWire, head, word.roundTrip _ bounded, List.length_take, total,
      Nat.min_eq_left (by omega : cut ≤ 8 + body.length), Nat.ne_of_lt cutInside]

theorem mismatched_frame_crc_is_rejected (word : WordCodec) (crc : Bytes → Nat)
    (body : Bytes) (stored limit : Nat) (bounded : body.length < 2 ^ 32)
    (storedBound : stored < 2 ^ 32)
    (different : stored ≠ crc body) :
    decodeFrame word crc limit (word.encode body.length ++ word.encode stored ++ body) = none := by
  have fields := encoded_frame_fields word body.length stored body
  simp only [decodeFrame, FrameDecodeWire]
  rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2,
    word.roundTrip _ bounded, word.roundTrip _ storedBound]
  simp [different]

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

/-- Each input chunk is the physical range selected by the bounded frame reader.
    The classifier represents reassembly and semantic validation of the exact body. -/
def byteFrame (word : WordCodec) (crc : Bytes → Nat) (limit : Nat)
    (classify : Bytes → Frame Stream Image) (bytes : Bytes) : Frame Stream Image :=
  match decodeFrame word crc limit bytes with
  | none => .torn
  | some body => classify body

theorem encoded_frame_replays (word : WordCodec) (crc : Bytes → Nat) (limit : Nat)
    (classify : Bytes → Frame Stream Image) (bodies : List Bytes)
    (bounded : ∀ body ∈ bodies, body.length < 2 ^ 32 ∧ body.length ≤ limit ∧ crc body < 2 ^ 32)
    (newest continued : Bool) (pending : Stream → Bool) :
    scanSegment newest continued pending
      ((bodies.map (FrameWire word.encode crc)).map (byteFrame word crc limit classify)) =
    scanSegment newest continued pending (bodies.map classify) := by
  have decoded : (bodies.map (FrameWire word.encode crc)).map (byteFrame word crc limit classify) =
      bodies.map classify := by
    rw [List.map_map]
    apply List.map_congr_left
    intro body member
    have ⟨size, fits, checksumBound⟩ := bounded body member
    simp [byteFrame, encoded_frame_decodes word crc body limit size fits checksumBound]
  rw [decoded]

theorem torn_encoded_frame_keeps_complete_entries (word : WordCodec) (crc : Bytes → Nat)
    (limit cut : Nat) (classify : Bytes → Frame Stream Image) (body : Bytes)
    (bounded : body.length < 2 ^ 32) (truncated : cut < 8 + body.length)
    (pending : Stream → Bool) (frames : List (Frame Stream Image)) :
    scan true pending
      (frames ++ [byteFrame word crc limit classify ((FrameWire word.encode crc body).take cut)]) =
    scan true pending frames := by
  simpa [byteFrame, encoded_frame_truncation word crc body limit cut bounded truncated] using
    torn_tail_keeps_complete_entries pending frames

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

/-- A file sync persists contents. The directory sync persists its name. A crash
    after rename and before the directory sync may select either complete index. -/
structure Publication where
  segmentSynced : Bool := false
  segmentNamed : Bool := false
  packSynced : Bool := false
  packNamed : Bool := false
  indexSynced : Bool := false
  indexRenamed : Bool := false
  indexNamed : Bool := false
  retired : Bool := false

inductive PublishStep : Publication → Publication → Prop
  | syncSegmentFile {p} : PublishStep p { p with segmentSynced := true }
  | nameSegment {p} : p.segmentSynced = true → PublishStep p { p with segmentNamed := true }
  | syncPackFile {p} : p.segmentNamed = true → PublishStep p { p with packSynced := true }
  | syncPackDirectory {p} : p.packSynced = true → PublishStep p { p with packNamed := true }
  | syncIndexFile {p} : p.packNamed = true → PublishStep p { p with indexSynced := true }
  | renameIndex {p} : p.indexSynced = true → PublishStep p { p with indexRenamed := true }
  | syncIndexDirectory {p} : p.indexRenamed = true → PublishStep p { p with indexNamed := true }
  | retireFiles {p} : p.indexNamed = true → PublishStep p { p with retired := true }

inductive PublicationReached : Publication → Prop
  | initial : PublicationReached {}
  | step {p q} : PublicationReached p → PublishStep p q → PublicationReached q

structure Ordered (p : Publication) : Prop where
  segmentVisible : p.segmentNamed = true → p.segmentSynced = true
  packed : p.packSynced = true → p.segmentNamed = true
  packVisible : p.packNamed = true → p.packSynced = true
  indexed : p.indexSynced = true → p.packNamed = true
  renamed : p.indexRenamed = true → p.indexSynced = true
  indexVisible : p.indexNamed = true → p.indexRenamed = true
  retired : p.retired = true → p.indexNamed = true

theorem publish_step_ordered {p q : Publication} (o : Ordered p) (step : PublishStep p q) :
    Ordered q := by
  obtain ⟨segmentVisible, packed, packVisible, indexed, renamed, indexVisible, retired⟩ := o
  cases step with
  | syncSegmentFile => exact ⟨fun _ => rfl, packed, packVisible, indexed, renamed, indexVisible, retired⟩
  | nameSegment h => exact ⟨fun _ => h, fun _ => rfl, packVisible, indexed, renamed, indexVisible, retired⟩
  | syncPackFile h => exact ⟨segmentVisible, fun _ => h, fun _ => rfl, indexed, renamed, indexVisible, retired⟩
  | syncPackDirectory h => exact ⟨segmentVisible, packed, fun _ => h, fun _ => rfl, renamed, indexVisible, retired⟩
  | syncIndexFile h => exact ⟨segmentVisible, packed, packVisible, fun _ => h, fun _ => rfl, indexVisible, retired⟩
  | renameIndex h => exact ⟨segmentVisible, packed, packVisible, indexed, fun _ => h, fun _ => rfl, retired⟩
  | syncIndexDirectory h => exact ⟨segmentVisible, packed, packVisible, indexed, renamed, fun _ => h, fun _ => rfl⟩
  | retireFiles h => exact ⟨segmentVisible, packed, packVisible, indexed, renamed, indexVisible, fun _ => h⟩

theorem publication_ordered {p : Publication} (reach : PublicationReached p) : Ordered p := by
  induction reach with
  | initial => exact ⟨nofun, nofun, nofun, nofun, nofun, nofun, nofun⟩
  | step _ step ih => exact publish_step_ordered ih step

inductive PublishEvent where
  | syncSegmentFile | nameSegment | syncPackFile | syncPackDirectory
  | syncIndexFile | renameIndex | syncIndexDirectory | retireFiles

def publishEvent (p : Publication) : PublishEvent → Option Publication
  | .syncSegmentFile => some { p with segmentSynced := true }
  | .nameSegment => if p.segmentSynced then some { p with segmentNamed := true } else none
  | .syncPackFile => if p.segmentNamed then some { p with packSynced := true } else none
  | .syncPackDirectory => if p.packSynced then some { p with packNamed := true } else none
  | .syncIndexFile => if p.packNamed then some { p with indexSynced := true } else none
  | .renameIndex => if p.indexSynced then some { p with indexRenamed := true } else none
  | .syncIndexDirectory => if p.indexRenamed then some { p with indexNamed := true } else none
  | .retireFiles => if p.indexNamed then some { p with retired := true } else none

theorem publish_event_step {p q : Publication} {event : PublishEvent}
    (accepted : publishEvent p event = some q) : PublishStep p q := by
  cases event <;> simp only [publishEvent] at accepted
  · cases accepted; exact .syncSegmentFile
  all_goals split at accepted <;> cases accepted <;> constructor <;> assumption

def PublicationOrder (events : List PublishEvent) : Prop :=
  ((events.foldlM publishEvent ({} : Publication)).map (·.retired)) = some true

instance (events : List PublishEvent) : Decidable (PublicationOrder events) :=
  inferInstanceAs (Decidable (_ = some true))

theorem execute_publication {p q : Publication} (start : PublicationReached p)
    (events : List PublishEvent) (run : events.foldlM publishEvent p = some q) :
    PublicationReached q := by
  induction events generalizing p with
  | nil => cases run; exact start
  | cons event rest ih =>
    simp only [List.foldlM_cons] at run
    cases performed : publishEvent p event with
    | none => simp [performed] at run
    | some next =>
      exact ih (.step start (publish_event_step performed)) (by simpa [performed] using run)

theorem publication_prefix_reachable {done later : List PublishEvent}
    (ordered : PublicationOrder (done ++ later)) :
    ∃ p, done.foldlM publishEvent ({} : Publication) = some p ∧ PublicationReached p := by
  cases atPrefix : done.foldlM publishEvent ({} : Publication) with
  | none => simp [PublicationOrder, List.foldlM_append, atPrefix] at ordered
  | some p => exact ⟨p, rfl, execute_publication .initial done atPrefix⟩

/-- The storage interface permits either name at the unsynced rename boundary.
    Old files may be missing after retirement. -/
def CrashChoice (p : Publication) (newIndex : Bool) : Prop :=
  if newIndex then p.indexRenamed = true else p.indexNamed = false

def durableRotation (base : Stream → Image) (old newer : List (Entry Stream Image))
    (p : Publication) (newIndex : Bool) : Rotation Stream Image :=
  { oldOnDisk := !p.retired
    packDurable := p.packNamed
    index := if newIndex then some (boundary base old) else none
    newer }

theorem crash_recovers_across_index_rename {p : Publication} (reach : PublicationReached p)
    {newIndex : Bool} (choice : CrashChoice p newIndex)
    (base : Stream → Image) (old newer : List (Entry Stream Image)) (stream : Stream) :
    readBack base old (durableRotation base old newer p newIndex) stream =
      some (replay stream (base stream) (old ++ newer)) := by
  have ordered := publication_ordered reach
  have appended : replay stream (base stream) (old ++ newer) =
      replay stream (boundary base old stream) newer := by
    simp [replay, boundary, List.foldl_append]
  cases newIndex
  · have named : p.indexNamed = false := choice
    have kept : p.retired = false := by
      cases retired : p.retired
      · rfl
      · have impossible := ordered.retired retired
        simp [named] at impossible
    simp [readBack, durableRotation, kept, appended]
  · have renamed : p.indexRenamed = true := choice
    have pack : p.packNamed = true := ordered.indexed (ordered.renamed renamed)
    simp [readBack, durableRotation, pack, appended]

theorem rename_crash_witness :
    ∃ p : Publication, PublicationReached p ∧ CrashChoice p false ∧ CrashChoice p true := by
  let segment : Publication := { segmentSynced := true }
  let openSegment := { segment with segmentNamed := true }
  let packed := { openSegment with packSynced := true }
  let named := { packed with packNamed := true }
  let indexed := { named with indexSynced := true }
  let renamed := { indexed with indexRenamed := true }
  have step0 : PublicationReached openSegment := .step (.step .initial .syncSegmentFile) (.nameSegment rfl)
  have step1 : PublicationReached packed := .step step0 (.syncPackFile rfl)
  have step2 : PublicationReached named := .step step1 (.syncPackDirectory rfl)
  have step3 : PublicationReached indexed := .step step2 (.syncIndexFile rfl)
  exact ⟨renamed, .step step3 (.renameIndex rfl), rfl, rfl⟩

#print axioms word32_round_trip
#print axioms encoded_frame_decodes
#print axioms encoded_frame_truncation
#print axioms mismatched_frame_crc_is_rejected
#print axioms encoded_frame_replays
#print axioms torn_encoded_frame_keeps_complete_entries
#print axioms torn_tail_keeps_complete_entries
#print axioms torn_closed_segment_fails
#print axioms incomplete_entry_is_discarded
#print axioms fragments_are_demultiplexed
#print axioms continued_fragments_finish_after_rollover
#print axioms fresh_segment_discards_incomplete_entries
#print axioms next_sound
#print axioms reopen_recovers_each_stream
#print axioms background_checkpoint_witness
#print axioms publish_step_ordered
#print axioms execute_publication
#print axioms publication_prefix_reachable
#print axioms crash_recovers_across_index_rename
#print axioms rename_crash_witness

end Logkeeper.StreamWAL
