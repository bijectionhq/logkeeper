import Logkeeper.StreamIO

/-! The authority and durable copy projection of a single replacement. The surviving
identities stay in their slots. The lost identity never votes again. -/

namespace Logkeeper.StreamReplacement

open StreamJournal

set_option warningAsError true
set_option autoImplicit false

inductive Route where
  | old | new
  deriving DecidableEq

inductive Node where
  | lost | first | second | learner
  deriving DecidableEq

inductive Phase where
  | intact
  | lost
  | repaired
  | installing (first second : Bool)
  | promoted
  deriving DecidableEq

/-- A fresh Seal counts towards an election only at a live voter whose durable
    ensemble matches the requested route. -/
def voter : Phase → Node → Option Route
  | .intact, .lost => some .old
  | .intact, .first | .intact, .second
  | .lost, .first | .lost, .second
  | .repaired, .first | .repaired, .second => some .old
  | .installing first _, .first => some (if first then .new else .old)
  | .installing _ second, .second => some (if second then .new else .old)
  | .promoted, .first | .promoted, .second | .promoted, .learner => some .new
  | _, _ => none

def routedSeal (phase : Phase) (node : Node) (route : Route) : Bool :=
  voter phase node == some route

def Quorum (phase : Phase) (route : Route) : Prop :=
  ∃ a b, a ≠ b ∧ routedSeal phase a route = true ∧ routedSeal phase b route = true

def mayInstallLearner (first second : Bool) : Bool := first && second

def ReplaceAllowed (current synced member : Bool) (changed : Nat) : Prop :=
  current = true ∧ synced = true ∧ member = true ∧ changed = 1

def ValidEnsemble (first second third : Nat) : Prop :=
  0 ∉ [first, second, third] ∧ [first, second, third].Nodup

def installEnsemble {Ensemble : Type} (to : Ensemble) : Ensemble × Bool :=
  (to, false)

inductive ReplaceDecision where
  | fenced | notSynced | replaced | wrongEnsemble | unauthorized | persist
  deriving DecidableEq

/-- The per-keeper decision after locating a live stream and projecting the
    authenticated promise, sync and ensemble checks. The install order is a
    separate protocol rule. -/
def replaceDecision (promised synced installed current valid member : Bool)
    (changed : Nat) : ReplaceDecision :=
  match promised, synced, installed, current with
  | false, _, _, _ => .fenced
  | true, false, _, _ => .notSynced
  | true, true, true, _ => .replaced
  | true, true, false, false => .wrongEnsemble
  | true, true, false, true =>
      if valid = true ∧ member = true ∧ changed = 1 then .persist else .unauthorized

inductive Next : Phase → Phase → Prop
  | lose : Next .intact .lost
  | repair : Next .lost .repaired
  | syncLearner : Next .repaired (.installing false false)
  | installFirst {second} : Next (.installing false second) (.installing true second)
  | installSecond {first} : Next (.installing first false) (.installing first true)
  | replaceLearner {first second} : mayInstallLearner first second = true →
      Next (.installing first second) .promoted
  | retry {phase} : Next phase phase

inductive Reachable : Phase → Prop
  | initial : Reachable .intact
  | next {phase phase'} : Reachable phase → Next phase phase' → Reachable phase'

theorem learner_install_requires_both {first second : Bool}
    (step : Next (.installing first second) .promoted) : first = true ∧ second = true := by
  cases step with
  | replaceLearner guard => exact Bool.and_eq_true_iff.mp guard -- both survivor installs

private theorem noVoter {phase : Phase} {route : Route}
    (none : ∀ a, routedSeal phase a route = false) : ¬ Quorum phase route := by
  rintro ⟨a, _, _, accepts, _⟩
  simp [none a] at accepts

private theorem soleVoter {phase : Phase} {route : Route} (member : Node)
    (only : ∀ a, routedSeal phase a route = true → a = member) : ¬ Quorum phase route := by
  rintro ⟨a, b, distinct, acceptA, acceptB⟩
  exact distinct ((only a acceptA).trans (only b acceptB).symm)

theorem exclusive_ensemble_authority (phase : Phase) :
    ¬ Quorum phase .old ∨ ¬ Quorum phase .new := by
  cases phase with
  | intact => exact Or.inr (noVoter (by intro a; cases a <;> decide))
  | lost => exact Or.inr (noVoter (by intro a; cases a <;> decide))
  | repaired => exact Or.inr (noVoter (by intro a; cases a <;> decide))
  | promoted => exact Or.inl (noVoter (by intro a; cases a <;> decide))
  | installing first second =>
      cases first <;> cases second
      · exact Or.inr (noVoter (by intro a; cases a <;> decide))
      · exact Or.inl (soleVoter .first (by intro a; cases a <;> decide))
      · exact Or.inl (soleVoter .second (by intro a; cases a <;> decide))
      · exact Or.inl (noVoter (by intro a; cases a <;> decide))

theorem split_install_has_no_quorum :
    (¬ Quorum (.installing true false) .old ∧ ¬ Quorum (.installing true false) .new) ∧
    (¬ Quorum (.installing false true) .old ∧ ¬ Quorum (.installing false true) .new) := by
  refine ⟨⟨soleVoter .second ?_, soleVoter .first ?_⟩, ⟨soleVoter .first ?_, soleVoter .second ?_⟩⟩
  all_goals intro a; cases a <;> decide

theorem stale_route_refused {phase : Phase} {node : Node}
    (installed : voter phase node = some .new) : routedSeal phase node .old = false := by
  simp [routedSeal, installed] -- seal must match the installed route

variable {Payload : Type}

def survivorCopy (phase : Phase) (original seed : History Payload) : History Payload :=
  match phase with
  | .intact | .lost => original
  | .repaired | .installing .. | .promoted => seed

def learnerCopy (phase : Phase) (seed : History Payload) : Option (History Payload) :=
  match phase with
  | .installing .. | .promoted => some seed
  | _ => none

/-- The original execution supplies a surviving vote and a ranked winner that
    carries the acknowledged cut when the survivors elect a higher epoch. -/
theorem surviving_copy_and_adopted_seed {s : StreamIO.State Payload} (reached : StreamIO.Reachable s)
    {old epoch : Nat} {cut : History Payload} {round : Round Payload} (lost : KeeperId)
    (acknowledged : QuorumAccepted s.keeper old cut) (higher : old < epoch)
    (elected : s.writer.round epoch = some round)
    (survivingSigners : round.first ≠ lost ∧ round.second ≠ lost) :
    (∃ k, k ≠ lost ∧ ∃ held, (s.keeper k).durable.votes ⟨old, held⟩ ∧ cut <+: held) ∧
      round.source ≠ lost ∧ cut <+: round.winner.history := by
  refine ⟨StreamIO.acknowledged_survives_one_disk_loss acknowledged lost, ?_,
    StreamIO.seal_covers_acknowledged reached elected higher acknowledged⟩
  unfold Round.source
  split
  · exact survivingSigners.2
  · exact survivingSigners.1

/-- Once repair publishes its seed, each surviving member holds the acknowledged prefix. -/
theorem repaired_survivors_cover {cut seed first second : History Payload}
    (adopted : cut <+: seed) {phase : Phase} (repaired : phase ≠ .intact ∧ phase ≠ .lost) :
    cut <+: survivorCopy phase first seed ∧ cut <+: survivorCopy phase second seed := by
  cases phase <;> simp_all [survivorCopy] -- both copies cover the seed

def availableAfterPromotion (seed : History Payload) (disk node : Node) : Option (History Payload) :=
  if disk = node then none
  else match node with
    | .lost => none
    | .first | .second => some (survivorCopy .promoted [] seed)
    | .learner => learnerCopy .promoted seed

theorem promoted_cut_survives_any_one_loss {cut seed : History Payload} (adopted : cut <+: seed)
    (disk : Node) :
    ∃ a b, a ≠ b ∧ availableAfterPromotion seed disk a = some seed ∧
      availableAfterPromotion seed disk b = some seed ∧ cut <+: seed := by
  cases disk
  · exact ⟨.first, .second, by decide, rfl, rfl, adopted⟩
  · exact ⟨.second, .learner, by decide, rfl, rfl, adopted⟩ -- first survivor lost
  · exact ⟨.first, .learner, by decide, rfl, rfl, adopted⟩
  · exact ⟨.first, .second, by decide, rfl, rfl, adopted⟩

/-- A transferred quorum certificate connects the two fixed-ensemble executions. -/
theorem seal_after_replacement_covers_acknowledged
    {before after : StreamIO.State Payload}
    (beforeReached : StreamIO.Reachable before) (afterReached : StreamIO.Reachable after)
    {old repair epoch : Nat} {cut : History Payload} {moved next : Round Payload}
    (acknowledged : QuorumAccepted before.keeper old cut)
    (repairElected : before.writer.round repair = some moved)
    (repairHigher : old < repair)
    (installed : QuorumAccepted after.keeper repair moved.winner.history)
    (nextElected : after.writer.round epoch = some next) (nextHigher : repair < epoch) :
    cut <+: next.winner.history :=
  (StreamIO.seal_covers_acknowledged beforeReached repairElected repairHigher acknowledged).trans
    (StreamIO.seal_covers_acknowledged afterReached nextElected nextHigher installed)

theorem split_then_promote_witness :
    Reachable (.installing true false) ∧
    routedSeal (.installing true false) .first .old = false ∧
    routedSeal (.installing true false) .first .new = true ∧
    Reachable .promoted ∧ Quorum .promoted .new := by
  have prepared := Reachable.next (Reachable.next (.next .initial .lose) .repair) .syncLearner
  have split := Reachable.next prepared .installFirst
  have retry := Reachable.next split .retry
  have both := Reachable.next retry .installSecond
  exact ⟨split, rfl, rfl, .next both (.replaceLearner rfl),
    .intro .first (.intro .learner ⟨by decide, rfl, rfl⟩)⟩

#print axioms learner_install_requires_both
#print axioms exclusive_ensemble_authority
#print axioms split_install_has_no_quorum
#print axioms stale_route_refused
#print axioms surviving_copy_and_adopted_seed
#print axioms repaired_survivors_cover
#print axioms promoted_cut_survives_any_one_loss
#print axioms seal_after_replacement_covers_acknowledged
#print axioms split_then_promote_witness

end Logkeeper.StreamReplacement
