import JournalRefinement

set_option warningAsError true

namespace MediaCrash

def decodePrefix : List (Option Record) → List Record
  | [] => []
  | .none :: _ => []
  | .some record :: rest => record :: decodePrefix rest

theorem decode_preserves_synced_frames (durable : List Record) (tail : List (Option Record)) :
    decodePrefix (durable.map some ++ tail) = durable ++ decodePrefix tail := by
  induction durable with
  | nil => rfl
  | cons record _ rest =>
      simp [decodePrefix, rest]

theorem decode_stops_at_first_invalid (valid : List Record) (tail : List (Option Record)) :
    decodePrefix (valid.map some ++ none :: tail) = valid := by
  rw [decode_preserves_synced_frames]
  exact List.append_nil valid

inductive Selector where
  | predecessor
  | replacement

inductive Phase where
  | current
  | imageStable
  | selectorVolatile
  | selectorStable
  deriving DecidableEq

structure Rotation where
  phase : Phase
  oldRemoved : Bool

def initial : Rotation := ⟨.current, false⟩

def ImageStable (rotation : Rotation) : Prop := rotation.phase ≠ .current

def SelectorAllows (rotation : Rotation) : Selector → Prop
  | .predecessor => rotation.phase ≠ .selectorStable
  | .replacement => rotation.phase = .selectorVolatile ∨ rotation.phase = .selectorStable

def ReclaimAdmissible (rotation : Rotation) : Prop :=
  rotation.phase = .selectorStable

inductive Step : Rotation → Rotation → Prop
  | syncImage : Step initial ⟨.imageStable, false⟩
  | rename : Step ⟨.imageStable, false⟩ ⟨.selectorVolatile, false⟩
  | syncSelector : Step ⟨.selectorVolatile, false⟩ ⟨.selectorStable, false⟩
  | reclaim {rotation : Rotation} (admitted : ReclaimAdmissible rotation) :
      Step rotation {rotation with oldRemoved := true}

inductive Reachable : Rotation → Prop
  | initial : Reachable initial
  | extend {before after : Rotation} : Reachable before → Step before after → Reachable after

theorem reachable_preserves_predecessor {rotation : Rotation} (reached : Reachable rotation) :
    rotation.oldRemoved = true → rotation.phase = .selectorStable := by
  induction reached with
  | initial => simp [initial]
  | extend _ step _ =>
      cases step with
      | reclaim admitted =>
          have stableSelector : _ = Phase.selectorStable := admitted
          exact fun _ => stableSelector
      | _ => simp

theorem selector_can_choose_only_readable_generation {rotation : Rotation} {selector : Selector}
    (reached : Reachable rotation) (allowed : SelectorAllows rotation selector) :
    match selector with
    | .predecessor => rotation.oldRemoved = false
    | .replacement => ImageStable rotation := by
  cases selector with
  | predecessor =>
      cases removed : rotation.oldRemoved
      · rfl
      · have stable := reachable_preserves_predecessor reached removed
        exact False.elim (allowed stable)
  | replacement =>
      rcases allowed with selected | selected <;> simp [ImageStable, selected]

structure AckEvidence (Record : Type) where
  records : List Record
  bytesStable : Bool
  nameStable : Bool

def Admissible (vote : AckEvidence Record) : Prop :=
  vote.bytesStable = true ∧ vote.nameStable = true

def recoverTail (nameSurvives : Bool) (frames : List (Option Record)) : List Record :=
  if nameSurvives then decodePrefix frames else []

theorem durable_vote_recovers_prefix (vote : AckEvidence Record)
    (admitted : Admissible vote) (nameSurvives : Bool) (frames residue : List (Option Record))
    (persistedBytes : vote.bytesStable = true → frames = vote.records.map some ++ residue)
    (persistedName : vote.nameStable = true → nameSurvives = true)
    : recoverTail nameSurvives frames = vote.records ++ decodePrefix residue := by
  have bytes : vote.bytesStable = true := by
    exact And.left admitted
  have name : vote.nameStable = true := by
    exact And.right admitted
  simp [recoverTail, persistedName name, persistedBytes bytes, decode_preserves_synced_frames]

def replaceBase (copied : List Record) (cut : Nat) (tail : List Record) : List Record :=
  copied.take cut ++ tail.drop cut

theorem fixed_copy_keeps_intervening_appends (captured added : List Record) (cut : Nat)
    (inCapture : cut ≤ captured.length) :
    replaceBase captured cut (captured ++ added) = captured ++ added := by
  unfold replaceBase
  rw [← List.take_append_of_le_length (l₂ := added) inCapture, List.take_append_drop]

def recover (rotation : Rotation) (selector : Selector) (copied : List Record) (cut : Nat)
    (nameSurvives : Bool) (frames : List (Option Record)) : Option (List Record) :=
  let tail := recoverTail nameSurvives frames
  match selector with
  | .predecessor => if rotation.oldRemoved then none else some tail
  | .replacement => if rotation.phase = .current then none else some (replaceBase copied cut tail)

theorem acknowledged_records_survive_every_legal_selector (vote : AckEvidence Record)
    (admitted : Admissible vote) {rotation : Rotation} {selector : Selector}
    (reached : Reachable rotation) (allowed : SelectorAllows rotation selector)
    (captured later : List Record) (exactSync : vote.records = captured ++ later)
    (cut : Nat) (inCapture : cut ≤ captured.length)
    (nameSurvives : Bool) (frames residue : List (Option Record))
    (persistedBytes : vote.bytesStable = true → frames = vote.records.map some ++ residue)
    (persistedName : vote.nameStable = true → nameSurvives = true) :
    recover rotation selector captured cut nameSurvives frames =
      some (vote.records ++ decodePrefix residue) := by
  have readable := selector_can_choose_only_readable_generation reached allowed
  have tail := durable_vote_recovers_prefix vote admitted nameSurvives frames residue
    persistedBytes persistedName
  cases selector with
  | predecessor =>
      simp [recover, tail, readable]
  | replacement =>
      change rotation.phase ≠ .current at readable
      simp only [recover, tail, ite_eq_right readable, Option.some.injEq]
      rw [exactSync, List.append_assoc, fixed_copy_keeps_intervening_appends _ _ _ inCapture]

theorem recovery_majority_contains_exact_media_vote (members : List Replica)
    (voted available : Replica → Bool) (writeQuorum : JournalRefinement.Majority members voted)
    (readQuorum : JournalRefinement.Majority members available)
    (records : List Record) (recovered : Replica → Option (List Record))
    (retains : ∀ replica ∈ members, voted replica = true → available replica = true →
      ∃ trail, recovered replica = some (records ++ trail)) :
    ∃ replica ∈ members, available replica = true ∧
      ∃ trail, recovered replica = some (records ++ trail) := by
  obtain ⟨replica, member, vote, online⟩ :=
    JournalRefinement.majorities_overlap members voted available writeQuorum readQuorum
  exact ⟨replica, member, online, retains replica member vote online⟩

theorem advanced_head_disqualifies_fixed_copy (cut advance : Nat) (later : 0 < advance) :
    cut + advance ≠ cut := by
  omega

#print axioms decode_preserves_synced_frames
#print axioms decode_stops_at_first_invalid
#print axioms reachable_preserves_predecessor
#print axioms selector_can_choose_only_readable_generation
#print axioms durable_vote_recovers_prefix
#print axioms fixed_copy_keeps_intervening_appends
#print axioms acknowledged_records_survive_every_legal_selector
#print axioms recovery_majority_contains_exact_media_vote
#print axioms advanced_head_disqualifies_fixed_copy

end MediaCrash
