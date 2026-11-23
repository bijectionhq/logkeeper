import OrderedApplication

set_option warningAsError true

namespace ReadIndexProof

structure Scope where
  group : Nat
  incarnation : Nat
  placement : Nat
  configuration : Nat
  ballot : Nat
  deriving DecidableEq

structure ReplicaState (Command : Type) where
  scope : Scope
  promised : Nat
  held : List Command

abbrev Stores (Replica Command : Type) := Nat → Replica → ReplicaState Command

structure Invocation where
  nonce : Nat
  started : Nat
  replied : Nat

structure Observation (Command : Type) where
  round : Nat
  sampled : Nat
  scope : Scope
  held : List Command

structure Round (Replica Command : Type) where
  identity : Nat
  invocation : Nat
  scope : Scope
  opened : Nat
  answered : Replica → Bool
  observed : Replica → Observation Command
  target : List Command

def DurableBasis (members : List Replica) (stores : Stores Replica Command)
    (scope : Scope) (time : Nat) (chosen : List Command) : Prop :=
  ∃ votes, JournalRefinement.Majority members votes ∧
    ∀ replica ∈ members, votes replica = true →
      (stores time replica).scope = scope ∧ chosen <+: (stores time replica).held

def MonotoneWithinScope (stores : Stores Replica Command) : Prop :=
  ∀ replica before after, before ≤ after →
    (stores before replica).scope = (stores after replica).scope →
    (stores before replica).held <+: (stores after replica).held

def Dominates (round : Round Replica Command) (replica : Replica) : Prop :=
  (round.observed replica).held.length ≤ round.target.length

def RoundIsFresh (call : Invocation) (round : Round Replica Command) : Prop :=
  call.started ≤ round.opened

def EligiblePromise (state : ReplicaState Command) (scope : Scope) : Prop :=
  state.promised = scope.ballot

def PromisesAdvance (stores : Stores Replica Command) : Prop :=
  ∀ replica before after, before ≤ after →
    (stores before replica).promised ≤ (stores after replica).promised

def FencedByHigherBallot (members : List Replica) (stores : Stores Replica Command)
    (scope : Scope) (time : Nat) : Prop :=
  ∃ fences, JournalRefinement.Majority members fences ∧
    ∀ replica ∈ members, fences replica = true → scope.ballot < (stores time replica).promised

structure Evidence (members : List Replica) (stores : Stores Replica Command)
    (call : Invocation) (round : Round Replica Command) : Prop where
  invocation : round.invocation = call.nonce
  fresh : RoundIsFresh call round
  finishes : round.opened ≤ call.replied
  quorum : JournalRefinement.Majority members round.answered
  observations : ∀ replica ∈ members, round.answered replica = true →
    let sample := round.observed replica
    sample.round = round.identity ∧ round.opened ≤ sample.sampled ∧ sample.sampled ≤ call.replied ∧
      sample.scope = round.scope ∧ sample.scope = (stores sample.sampled replica).scope ∧
      sample.held = (stores sample.sampled replica).held ∧
      EligiblePromise (stores sample.sampled replica) round.scope
  picked : ∃ replica ∈ members, round.answered replica = true ∧
    round.target = (round.observed replica).held
  maximum : ∀ replica ∈ members, round.answered replica = true → Dominates round replica

theorem successful_round_follows_invocation {members : List Replica} {stores : Stores Replica Command}
    {call : Invocation} {round : Round Replica Command} (checked : Evidence members stores call round) :
    call.started ≤ round.opened ∧ round.opened ≤ call.replied := by
  have startsInside : call.started ≤ round.opened := by
    exact checked.fresh
  exact ⟨startsInside, checked.finishes⟩

theorem target_is_exact_fresh_observation {members : List Replica} {stores : Stores Replica Command}
    {call : Invocation} {round : Round Replica Command} (checked : Evidence members stores call round) :
    round.invocation = call.nonce ∧ ∃ replica ∈ members, round.answered replica = true ∧
      let sample := round.observed replica
      sample.round = round.identity ∧ call.started ≤ sample.sampled ∧ sample.sampled ≤ call.replied ∧
      sample.scope = round.scope ∧ round.target = (stores sample.sampled replica).held := by
  obtain ⟨replica, member, answered, picked⟩ := checked.picked
  obtain ⟨identity, afterOpen, beforeReply, scope, _, exactHeld, _⟩ :=
    checked.observations replica member answered
  exact ⟨checked.invocation, replica, member, answered, identity,
    Nat.le_trans (successful_round_follows_invocation checked).1 afterOpen,
    beforeReply, scope, picked.trans exactHeld⟩

theorem earlier_higher_fence_excludes_a_read_quorum {members : List Replica}
    {stores : Stores Replica Command} {call : Invocation} {round : Round Replica Command} {time : Nat}
    (checked : Evidence members stores call round) (persistent : PromisesAdvance stores)
    (fencesBeforeOpen : time ≤ round.opened)
    (fenced : FencedByHigherBallot members stores round.scope time) : False := by
  obtain ⟨fences, enough, raised⟩ := fenced
  obtain ⟨replica, member, promised, answered⟩ :=
    JournalRefinement.majorities_overlap members fences round.answered enough checked.quorum
  obtain ⟨_, afterOpen, _, _, _, _, eligible⟩ := checked.observations replica member answered
  have livePromise : (stores (round.observed replica).sampled replica).promised = round.scope.ballot := by
    exact eligible
  have advances := persistent replica time _ (Nat.le_trans fencesBeforeOpen afterOpen)
  exact Nat.not_lt_of_ge (livePromise ▸ advances) (raised replica member promised)

theorem sampled_maximum_covers_prior_choice {members : List Replica} {stores : Stores Replica Command}
    {call : Invocation} {round : Round Replica Command} {time : Nat} {chosen : List Command}
    (checked : Evidence members stores call round) (keeps : MonotoneWithinScope stores)
    (beforeRound : time ≤ round.opened) (basis : DurableBasis members stores round.scope time chosen) :
    chosen.length ≤ round.target.length := by
  obtain ⟨votes, moreThanHalf, stored⟩ := basis
  obtain ⟨replica, belongs, voted, answered⟩ :=
    JournalRefinement.majorities_overlap members votes round.answered moreThanHalf checked.quorum
  obtain ⟨scopeBefore, prefixBefore⟩ := stored replica belongs voted
  obtain ⟨_, afterOpen, _, readScope, observedScope, observedData, _⟩ :=
    checked.observations replica belongs answered
  have stillScoped : (stores time replica).scope =
      (stores (round.observed replica).sampled replica).scope :=
    scopeBefore.trans (readScope.symm.trans observedScope)
  have oldVotePersists := keeps replica time _ (Nat.le_trans beforeRound afterOpen) stillScoped
  have sampleDominated : (round.observed replica).held.length ≤ round.target.length := by
    exact checked.maximum replica belongs answered
  have capturedContains : chosen <+: (round.observed replica).held :=
    observedData.symm ▸ prefixBefore.trans oldVotePersists
  exact Nat.le_trans capturedContains.length_le sampleDominated

structure ChoiceTrace (Command : Type) where
  chosen : Nat → List Command
  extendsEarlier : ∀ earlier later, earlier ≤ later → chosen earlier <+: chosen later

def UnitChoices (trace : ChoiceTrace Command) : Prop :=
  ∀ time, (trace.chosen (time + 1)).length ≤ (trace.chosen time).length + 1

theorem any_intermediate_length_occurs (trace : ChoiceTrace Command)
    (unit : UnitChoices trace) {fromTime through length : Nat}
    (ordered : fromTime ≤ through)
    (lower : (trace.chosen fromTime).length ≤ length)
    (upper : length ≤ (trace.chosen through).length) :
    ∃ time, fromTime ≤ time ∧ time ≤ through ∧ (trace.chosen time).length = length := by
  induction through with
  | zero =>
      have atStart : fromTime = 0 := Nat.eq_zero_of_le_zero ordered
      subst fromTime
      exact ⟨0, by omega, by omega, Nat.le_antisymm lower upper⟩
  | succ previous prior =>
      by_cases earlier : length ≤ (trace.chosen previous).length
      · by_cases fits : fromTime ≤ previous
        · obtain ⟨point, afterStart, beforeEnd, exactLength⟩ := prior fits earlier
          exact ⟨point, afterStart, Nat.le_trans beforeEnd (Nat.le_succ _), exactLength⟩
        · have atEnd : fromTime = previous + 1 := by omega
          subst fromTime
          exact ⟨previous + 1, by omega, by omega, Nat.le_antisymm lower upper⟩
      · have grows := unit previous
        exact ⟨previous + 1, ordered, by omega, by omega⟩

def AppliesExactTarget (round : Round Replica Command) (applied : List Command) : Prop :=
  round.target <+: applied

def AppliedThrough (trace : ChoiceTrace Command) (call : Invocation)
    (round : Round Replica Command) (applied : List Command) : Prop :=
  AppliesExactTarget round applied ∧ applied <+: trace.chosen call.replied

theorem matching_prefix_is_exact_at_cut {trace : ChoiceTrace Command}
    {time replied : Nat} {target : List Command} (beforeReply : time ≤ replied)
    (sameLength : (trace.chosen time).length = target.length)
    (exactTarget : target <+: trace.chosen replied) : trace.chosen time = target := by
  exact (List.prefix_of_prefix_length_le (trace.extendsEarlier time replied beforeReply)
    exactTarget (Nat.le_of_eq sameLength)).eq_of_length sameLength

theorem read_at_applied_cut_covering_sample {members : List Replica} {stores : Stores Replica Command}
    {call : Invocation} {round : Round Replica Command} {trace : ChoiceTrace Command}
    (checked : Evidence members stores call round) (keeps : MonotoneWithinScope stores)
    (unit : UnitChoices trace)
    (ready : DurableBasis members stores round.scope round.opened (trace.chosen round.opened))
    (snapshot applied : List Command) (covers : round.target.length ≤ snapshot.length)
    (exactApplied : snapshot <+: applied) (installed : applied <+: trace.chosen call.replied) :
    ∃ point, call.started ≤ point ∧ point ≤ call.replied ∧ trace.chosen point = snapshot := by
  have interval := successful_round_follows_invocation checked
  have lower := sampled_maximum_covers_prior_choice checked keeps (Nat.le_refl _) ready
  have exactChosen := exactApplied.trans installed
  obtain ⟨point, afterStart, beforeReply, sameLength⟩ :=
    any_intermediate_length_occurs trace unit interval.2 (Nat.le_trans lower covers) exactChosen.length_le
  exact ⟨point, Nat.le_trans interval.1 afterStart, beforeReply,
    matching_prefix_is_exact_at_cut beforeReply sameLength exactChosen⟩

theorem no_marker_round_refines_logical_read {members : List Replica} {stores : Stores Replica Command}
    {call : Invocation} {round : Round Replica Command} {trace : ChoiceTrace Command}
    (checked : Evidence members stores call round) (keeps : MonotoneWithinScope stores)
    (unit : UnitChoices trace)
    (ready : DurableBasis members stores round.scope round.opened (trace.chosen round.opened))
    (applied : List Command) (installed : AppliedThrough trace call round applied) :
    ∃ point, call.started ≤ point ∧ point ≤ call.replied ∧ trace.chosen point = round.target := by
  have exactApplied : round.target <+: applied := by
    exact installed.1
  exact read_at_applied_cut_covering_sample checked keeps unit ready
    round.target applied (Nat.le_refl _) exactApplied installed.2

theorem matching_certified_and_sampled_cuts_refines_atomic_batch
    {members : List Replica} {stores : Stores Replica Command}
    {call : Invocation} {round : Round Replica Command} {trace : ChoiceTrace Command}
    (checked : Evidence members stores call round) (keeps : MonotoneWithinScope stores)
    (ready : DurableBasis members stores round.scope round.opened (trace.chosen round.opened))
    (alreadyCertified : round.target <+: trace.chosen round.opened) :
    call.started ≤ round.opened ∧ round.opened ≤ call.replied ∧
      trace.chosen round.opened = round.target := by
  have interval := successful_round_follows_invocation checked
  have upper := sampled_maximum_covers_prior_choice checked keeps (Nat.le_refl _) ready
  exact ⟨interval.1, interval.2, (alreadyCertified.eq_of_length_le upper).symm⟩

theorem applied_barrier_from_exact_choice {trace : ChoiceTrace (OrderedApplication.Command Payload)}
    {call : Invocation} {target : List (OrderedApplication.Command Payload)}
    {limits : Kernel.Limits} {initial : Kernel.State Payload} {writer : Kernel.Writer} {cut : Nat}
    (existsPoint : ∃ point, call.started ≤ point ∧ point ≤ call.replied ∧ trace.chosen point = target)
    (response : (OrderedApplication.decideCommand limits
      (OrderedApplication.replay limits initial target).1 (.read writer call.nonce)).2 =
        .readCut call.nonce cut) :
    ∃ point, call.started ≤ point ∧ point ≤ call.replied ∧
      (OrderedApplication.replay limits initial (trace.chosen point)).1.authority = .active writer ∧
      (OrderedApplication.replay limits initial (trace.chosen point)).1.history.length = cut := by
  obtain ⟨point, afterStart, beforeReply, exactAt⟩ := existsPoint
  have properties := OrderedApplication.applied_read_reports_exact_cut response
  exact ⟨point, afterStart, beforeReply, exactAt.symm ▸ properties.2.1, exactAt.symm ▸ properties.2.2.symm⟩

theorem no_marker_reply_has_an_ordered_barrier_witness
    {members : List Replica} {stores : Stores Replica (OrderedApplication.Command Payload)}
    {trace : ChoiceTrace (OrderedApplication.Command Payload)} {call : Invocation}
    {round : Round Replica (OrderedApplication.Command Payload)}
    (checked : Evidence members stores call round) (keeps : MonotoneWithinScope stores)
    (unit : UnitChoices trace)
    (ready : DurableBasis members stores round.scope round.opened (trace.chosen round.opened))
    (applied : List (OrderedApplication.Command Payload))
    (installed : AppliedThrough trace call round applied)
    (limits : Kernel.Limits) (initial : Kernel.State Payload) (writer : Kernel.Writer) (cut : Nat)
    (response : (OrderedApplication.decideCommand limits
      (OrderedApplication.replay limits initial round.target).1 (.read writer call.nonce)).2 =
        .readCut call.nonce cut) :
    ∃ point, call.started ≤ point ∧ point ≤ call.replied ∧
      (OrderedApplication.replay limits initial (trace.chosen point)).1.authority = .active writer ∧
      (OrderedApplication.replay limits initial (trace.chosen point)).1.history.length = cut :=
  applied_barrier_from_exact_choice
    (no_marker_round_refines_logical_read checked keeps unit ready applied installed) response

theorem an_atomic_choice_can_skip_a_covered_length :
    ∃ trace : ChoiceTrace Nat,
      (trace.chosen 0).length ≤ 1 ∧ 1 ≤ (trace.chosen 1).length ∧
      ∀ point, point ≤ 1 → (trace.chosen point).length ≠ 1 := by
  let chosen : Nat → List Nat := fun time => if time = 0 then [] else [10, 20]
  have grows : ∀ earlier later, earlier ≤ later → chosen earlier <+: chosen later := by
    intro earlier later time
    by_cases first : earlier = 0
    · simp [chosen, first]
    · have second : later ≠ 0 := by omega
      simp [chosen, first, second]
  refine ⟨⟨chosen, grows⟩, by simp [chosen], by simp [chosen], ?_⟩
  intro point _
  change (chosen point).length ≠ 1
  by_cases first : point = 0 <;> simp [chosen, first]

#print axioms successful_round_follows_invocation
#print axioms target_is_exact_fresh_observation
#print axioms earlier_higher_fence_excludes_a_read_quorum
#print axioms sampled_maximum_covers_prior_choice
#print axioms any_intermediate_length_occurs
#print axioms matching_prefix_is_exact_at_cut
#print axioms read_at_applied_cut_covering_sample
#print axioms no_marker_round_refines_logical_read
#print axioms matching_certified_and_sampled_cuts_refines_atomic_batch
#print axioms applied_barrier_from_exact_choice
#print axioms no_marker_reply_has_an_ordered_barrier_witness
#print axioms an_atomic_choice_can_skip_a_covered_length

end ReadIndexProof
