import Logkeeper.StreamHead

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

/-- Replace is routed outside the fixed-ensemble I/O automaton. The
    installation phase starts after survivor repair and learner Sync.
    Completed installs remain eligible for an idempotent retry. -/
def ReplaceSendable : Phase → Node → Prop
  | .installing first second, .learner => mayInstallLearner first second = true
  | .installing .., .first | .installing .., .second => True
  | .promoted, .first | .promoted, .second | .promoted, .learner => True
  | _, _ => False

theorem sendable_learner_replace_has_installed_survivors {phase : Phase}
    (sent : ReplaceSendable phase .learner) :
    voter phase .first = some .new ∧ voter phase .second = some .new := by
  cases phase with
  | intact | lost | repaired => exact False.elim sent
  | installing first second =>
      change (first && second) = true at sent
      obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.mp sent
      exact ⟨rfl, rfl⟩
  | promoted => exact ⟨rfl, rfl⟩

theorem replace_sendability_witness :
    ∃ phase, Reachable phase ∧
      ReplaceSendable phase .first ∧ ReplaceSendable phase .second ∧ ReplaceSendable phase .learner := by
  refine ⟨.installing true true, ?_, trivial, trivial, rfl⟩
  exact (((((Reachable.initial.next .lose).next .repair).next .syncLearner).next .installFirst).next .installSecond)

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

/-- An empty Append at the adopted tail, which the sweep requires from each survivor
    after the complete Syncs. -/
def publishSeed (epoch : Nat) (round : Round Payload) : StreamIO.Request Payload :=
  .publish epoch round.winner.history.length

def SweepPublished (s : StreamIO.State Payload) (epoch : Nat) (round : Round Payload) :
    StreamIO.State Payload :=
  let req := publishSeed epoch round
  (s.apply round.first round.identity req).apply round.second round.identity req

/-- The two publication acknowledgements are projected from deliveries. The sweep
    issues no records at its repair epoch, so both synced histories are the adopted seed. -/
structure SweepPublications (s : StreamIO.State Payload) (epoch : Nat) (round : Round Payload) : Prop where
  elected : s.writer.round epoch = some round
  idle : s.writer.issued epoch = round.winner.history
  first : StreamIO.Next s (.deliver (.call round.first round.identity (publishSeed epoch round)))
    (s.apply round.first round.identity (publishSeed epoch round))
  second : StreamIO.Next (s.apply round.first round.identity (publishSeed epoch round))
    (.deliver (.call round.second round.identity (publishSeed epoch round)))
    (SweepPublished s epoch round)

private theorem published_seed_vote {s : StreamIO.State Payload} (reached : StreamIO.Reachable s)
    {epoch : Nat} {round : Round Payload} (elected : s.writer.round epoch = some round)
    (idle : s.writer.issued epoch = round.winner.history) {k : KeeperId}
    (rpc : StreamIO.Next s (.deliver (.call k round.identity (publishSeed epoch round)))
      (s.apply k round.identity (publishSeed epoch round))) :
    (s.apply k round.identity (publishSeed epoch round) |>.keeper k).durable.votes
      ⟨epoch, round.winner.history⟩ := by
  cases rpc with
  | deliver _ admitted =>
      have inv := StreamIO.reachable_inv reached
      have sync : (s.keeper k).synced = epoch := admitted.2.1.2
      have between := StreamIO.synced_history (inv.reached k) inv.reserved (inv.unelected 0 inv.reserved) sync
      have adopted : s.writer.seed epoch = round.winner.history := by simp [Writer.seed, elected]
      rw [adopted, idle] at between
      have len := Nat.le_antisymm between.2.length_le between.1.length_le
      have image := StreamIO.take_of_issued between.2
      rw [len, List.take_length] at image
      have vote := StreamIO.latest_voted (inv.reached k)
      rw [StreamIO.latest_eta, sync, image] at vote
      simpa [StreamIO.State.apply, publishSeed, StreamIO.effect] using vote

/-- Replacing the failed slot keeps the durable survivor images used as signers. -/
theorem survivor_installs_transfer_certificate {s : StreamIO.State Payload} (reached : StreamIO.Reachable s)
    {repair : Nat} {round : Round Payload} (publications : SweepPublications s repair round)
    (after : KeeperId → Keeper Payload)
    (first : after round.first = (SweepPublished s repair round).keeper round.first)
    (second : after round.second = (SweepPublished s repair round).keeper round.second) :
    QuorumAccepted after repair round.winner.history := by
  have left := published_seed_vote reached publications.elected publications.idle publications.first
  have right := published_seed_vote (reached.extend publications.first)
    publications.elected publications.idle publications.second
  refine ⟨fun k => decide (k = round.first ∨ k = round.second),
    two_of_three_is_majority _ _ round.distinct, ?_⟩
  intro k _ answered
  rcases of_decide_eq_true answered with same | same
  · subst k
    refine ⟨_, ?_, List.prefix_rfl⟩
    rw [first]
    simpa [SweepPublished, StreamIO.State.apply, round.distinct] using left
  · subst k
    refine ⟨_, ?_, List.prefix_rfl⟩
    rw [second]
    exact right

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

theorem seal_after_sweep_covers_acknowledged
    {before after : StreamIO.State Payload}
    (beforeReached : StreamIO.Reachable before) (afterReached : StreamIO.Reachable after)
    {old repair epoch : Nat} {cut : History Payload} {moved next : Round Payload}
    (acknowledged : QuorumAccepted before.keeper old cut)
    (publication : SweepPublications before repair moved)
    (repairHigher : old < repair)
    (first : after.keeper moved.first = (SweepPublished before repair moved).keeper moved.first)
    (second : after.keeper moved.second = (SweepPublished before repair moved).keeper moved.second)
    (nextElected : after.writer.round epoch = some next) (nextHigher : repair < epoch) :
    cut <+: next.winner.history :=
  seal_after_replacement_covers_acknowledged beforeReached afterReached acknowledged
    publication.elected repairHigher
    (survivor_installs_transfer_certificate beforeReached publication after.keeper first second)
    nextElected nextHigher

/-- The original cut can cross any number of sweep publications. Between those
    boundaries the fixed-ensemble automaton can process ordinary journal calls. -/
inductive RepairHistory (original : History Payload) :
    StreamIO.State Payload → Nat → History Payload → Prop
  | original {s epoch} : StreamIO.Reachable s →
      QuorumAccepted s.keeper epoch original → RepairHistory original s epoch original
  | advance {s next action epoch cut} : RepairHistory original s epoch cut →
      StreamIO.Next s action next → RepairHistory original next epoch cut
  | transfer {s next old epoch cut round} : RepairHistory original s old cut →
      StreamIO.Reachable next → old < epoch → SweepPublications s epoch round →
      next.keeper round.first = (SweepPublished s epoch round).keeper round.first →
      next.keeper round.second = (SweepPublished s epoch round).keeper round.second →
      RepairHistory original next epoch round.winner.history

theorem repair_history_carries_original {original cut : History Payload} {s : StreamIO.State Payload}
    {epoch : Nat} (trace : RepairHistory original s epoch cut) :
    StreamIO.Reachable s ∧ QuorumAccepted s.keeper epoch cut ∧ original <+: cut := by
  induction trace with
  | original reached accepted => exact ⟨reached, accepted, List.prefix_rfl⟩
  | advance _ step ih =>
    obtain ⟨reached, accepted, prefixCut⟩ := ih
    have preserved := (StreamIO.next_inv (StreamIO.reachable_inv reached) step).2.1
    exact ⟨reached.extend step, StreamIO.quorum_persists (fun k _ => preserved.votes k) accepted, prefixCut⟩
  | transfer _ nextReached higher publications first second ih =>
    obtain ⟨reached, accepted, prefixCut⟩ := ih
    exact ⟨nextReached, survivor_installs_transfer_certificate reached publications _ first second,
      prefixCut.trans (StreamIO.seal_covers_acknowledged reached publications.elected higher accepted)⟩

/-- A fresh call in the installed ensemble keeps the original invocation bound
    after any number of completed transfers. -/
theorem head_after_repairs (trace : StreamHead.Timeline Payload) {call : Invocation}
    {original cut : History Payload} {epoch result : Nat}
    (repaired : RepairHistory original (trace.state call.started) epoch cut)
    {sampled confirmed : CheckRound} (samples : StreamHead.Samples call sampled)
    (confirmation : StreamHead.Samples call confirmed)
    (observes : ∀ k ∈ ensemble, sampled.answered k = true →
      sampled.view k = check (trace.state (sampled.sampled k) |>.keeper k))
    (confirms : ∀ k ∈ ensemble, confirmed.answered k = true →
      confirmed.view k = check (trace.state (confirmed.sampled k) |>.keeper k))
    (covers : SamplesCovered sampled result)
    (published : JournalRefinement.Majority ensemble
      (fun k => confirmed.answered k && decide (result ≤ (confirmed.view k).head))) :
    original.length ≤ result ∧ ∃ event, call.started ≤ event ∧ event ≤ call.replied ∧
      StreamHead.AtCut trace sampled.opened result event := by
  obtain ⟨_, held, includes⟩ := repair_history_carries_original repaired
  have bound := StreamHead.head_after_publication trace samples confirmation observes confirms
    covers published ⟨epoch, cut, held, Nat.le_refl _⟩
  exact ⟨Nat.le_trans includes.length_le bound.1, bound.2⟩

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

#print axioms sendable_learner_replace_has_installed_survivors
#print axioms replace_sendability_witness
#print axioms learner_install_requires_both
#print axioms exclusive_ensemble_authority
#print axioms split_install_has_no_quorum
#print axioms stale_route_refused
#print axioms surviving_copy_and_adopted_seed
#print axioms repaired_survivors_cover
#print axioms promoted_cut_survives_any_one_loss
#print axioms survivor_installs_transfer_certificate
#print axioms seal_after_replacement_covers_acknowledged
#print axioms seal_after_sweep_covers_acknowledged
#print axioms repair_history_carries_original
#print axioms head_after_repairs
#print axioms split_then_promote_witness

end Logkeeper.StreamReplacement
