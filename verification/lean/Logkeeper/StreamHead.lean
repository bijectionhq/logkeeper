import Logkeeper.StreamIOWitness

namespace Logkeeper.StreamHead

open PrefixAgreement StreamJournal StreamIO
open JournalRefinement (Majority majorities_overlap)

set_option autoImplicit false
set_option warningAsError true

variable {Payload : Type}

def FreshSample (opened sent : Nat) : Prop := opened < sent

def SampleIndex (a b : Nat) : Nat := max a b

theorem sample_bounds (a b : Nat) :
    a ≤ SampleIndex a b ∧ b ≤ SampleIndex a b := ⟨Nat.le_max_left .., Nat.le_max_right ..⟩

/-- One physical event per automaton step. A call can open or reply at any event cut. -/
structure Timeline (Payload : Type) where
  state : Nat → State Payload
  start : StreamIO.Reachable (state 0)
  next : ∀ time, ∃ action, Next (state time) action (state (time + 1))

theorem Timeline.reachable (trace : Timeline Payload) (time : Nat) :
    StreamIO.Reachable (trace.state time) := by
  induction time with
  | zero => exact trace.start
  | succ time reached =>
      obtain ⟨_, step⟩ := trace.next time
      exact reached.extend step

/-- All cuts through a quorum-accepted batch become chosen at that physical event. -/
def Committed (s : State Payload) (cut : Nat) : Prop :=
  ∃ epoch history, QuorumAccepted s.keeper epoch history ∧ cut ≤ history.length

theorem Timeline.votes (trace : Timeline Payload) {first last : Nat} (before : first ≤ last)
    (keeper : KeeperId) (vote : Vote (Record Payload))
    (accepted : (trace.state first |>.keeper keeper).durable.votes vote) :
    (trace.state last |>.keeper keeper).durable.votes vote := by
  induction before with
  | refl => exact accepted
  | @step time _ prior =>
      obtain ⟨_, step⟩ := trace.next time
      exact ((next_inv (reachable_inv (trace.reachable time)) step).2.1).votes keeper prior

theorem Timeline.committed (trace : Timeline Payload) {first last cut : Nat} (before : first ≤ last)
    (committed : Committed (trace.state first) cut) : Committed (trace.state last) cut := by
  obtain ⟨epoch, history, copies, within⟩ := committed
  exact ⟨epoch, history, quorum_persists (trace.votes before) copies, within⟩

/-- A chosen opening prefix is still covered by a sampled copy, including after a takeover. -/
theorem sampled_copy_covers (trace : Timeline Payload) {opened sample epoch : Nat}
    (ordered : opened ≤ sample) {history held : History Payload} (keeper : KeeperId)
    (chosen : QuorumAccepted (trace.state opened).keeper epoch history)
    (vote : (trace.state opened |>.keeper keeper).durable.votes ⟨epoch, held⟩)
    (copied : history <+: held) : history.length ≤ (trace.state sample |>.keeper keeper).tail := by
  let s := trace.state sample
  let k := s.keeper keeper
  have reached := trace.reachable sample
  have inv := reachable_inv reached
  have sound := DurableAcceptor.reachable_replies_cover_every_lower_vote
    (reachable_keeper_refines_durable_acceptor (inv.reached keeper))
  have present := trace.votes ordered keeper _ vote
  obtain ⟨latest, exactView, dominates⟩ := sound.dominates _ present
  have exactLatest : k.latest = latest := by simp [k, s, Keeper.latest, exactView]
  change history.length ≤ k.latest.history.length
  rw [exactLatest]
  rcases Nat.eq_or_lt_of_le dominates.1 with same | higher
  · exact Nat.le_trans copied.length_le (dominates.2 same)
  · have latestVoted : k.durable.votes latest := exactLatest ▸ latest_voted (inv.reached keeper)
    have stays := quorum_persists (trace.votes ordered) chosen
    let x := execution reached
    have asChosen : Chosen x.ledger epoch history := by
      obtain ⟨copies, quorum, covers⟩ := stays
      exact ⟨copies, quorum, fun j member answered =>
        let ⟨image, held, prefixed⟩ := covers j member answered
        ⟨⟨epoch, image⟩, held, rfl, prefixed⟩⟩
    have follows := vote_follows_writer (inv.reached keeper) inv.reserved
      (inv.unelected 0 inv.reserved) latestVoted
    have elected : x.ledger.active latest.ballot := by
      rcases follows.1 with zero | active
      · omega
      · exact Or.inr active
    exact ((later_ballot_inherits_chosen_prefix (execution_refines_prefix_agreement x)
      asChosen latest.ballot higher elected).trans follows.2.1).length_le

/-- A logical cut between single appends in a physical batch. If selected at opening,
    the next LSN is still unchosen there. Otherwise the batch first chooses this LSN. -/
def AtCut (trace : Timeline Payload) (opened cut event : Nat) : Prop :=
  Committed (trace.state event) cut ∧
    ((event = opened ∧ ¬ Committed (trace.state event) (cut + 1)) ∨
      (opened < event ∧ ¬ Committed (trace.state (event - 1)) cut))

theorem cut_in_window (trace : Timeline Payload) {opened replied cut : Nat}
    (ordered : opened ≤ replied) (lower : ¬ Committed (trace.state opened) (cut + 1))
    (upper : Committed (trace.state replied) cut) :
    ∃ event, opened ≤ event ∧ event ≤ replied ∧ AtCut trace opened cut event := by
  induction ordered with
  | refl => exact ⟨opened, Nat.le_refl _, Nat.le_refl _, upper, Or.inl ⟨rfl, lower⟩⟩
  | @step time prior ih =>
      by_cases already : Committed (trace.state time) cut
      · obtain ⟨event, afterOpen, before, atCut⟩ := ih already
        exact ⟨event, afterOpen, Nat.le_trans before (Nat.le_succ _), atCut⟩
      · exact ⟨time + 1, Nat.le_trans prior (Nat.le_succ _), Nat.le_refl _, upper,
          Or.inr ⟨Nat.lt_succ_of_le prior, by simpa using already⟩⟩

/-- Provenance for a Check or a successful reused Append. The latter's matching request
    and durable reply supply the sample event just as Check does. -/
structure Samples (call : Invocation) (round : CheckRound) where
  sent : KeeperId → Nat
  queued : call.started ≤ round.opened
  quorum : Majority ensemble round.answered
  fresh : ∀ k ∈ ensemble, round.answered k = true →
    round.opened ≤ sent k ∧ sent k ≤ round.sampled k ∧ round.sampled k ≤ call.replied
  eligible : ∀ k ∈ ensemble, round.answered k = true →
    (round.view k).promised = round.epoch ∧ (round.view k).synced = round.epoch

theorem Samples.confirmed {call : Invocation} {round : CheckRound} (samples : Samples call round) :
    Confirmed call round := by
  obtain ⟨k, member, answered, _⟩ :=
    majorities_overlap ensemble round.answered round.answered samples.quorum samples.quorum
  obtain ⟨opened, sent, sampled⟩ := samples.fresh k member answered
  exact ⟨samples.queued, Nat.le_trans opened (Nat.le_trans sent sampled), samples.quorum,
    fun j m a => ⟨Nat.le_trans (samples.fresh j m a).1 (samples.fresh j m a).2.1,
      (samples.fresh j m a).2.2, samples.eligible j m a⟩⟩

theorem opening_covered (trace : Timeline Payload) {call : Invocation} {round : CheckRound}
    (samples : Samples call round)
    (observes : ∀ k ∈ ensemble, round.answered k = true →
      round.view k = check (trace.state (round.sampled k) |>.keeper k))
    {cut openedCut : Nat} (covers : SamplesCovered round cut)
    (chosen : Committed (trace.state round.opened) openedCut) : openedCut ≤ cut := by
  obtain ⟨epoch, history, accepted, within⟩ := chosen
  obtain ⟨copies, majority, voted⟩ := accepted
  obtain ⟨k, member, copied, answered⟩ :=
    majorities_overlap ensemble copies round.answered majority samples.quorum
  obtain ⟨held, vote, includes⟩ := voted k member copied
  have sample := sampled_copy_covers trace (samples.confirmed.samples k member answered).1 k
    ⟨copies, majority, voted⟩ vote includes
  have tail := covers k member answered
  rw [observes k member answered] at tail
  exact Nat.le_trans within (Nat.le_trans sample tail)

/-- Writer publication certifies a cut at least as large as its fresh samples. The
    observer keeps these opening samples and supplies confirmation from a later round. -/
theorem head_linearizable (trace : Timeline Payload) {call : Invocation} {round : CheckRound}
    (samples : Samples call round)
    (observes : ∀ k ∈ ensemble, round.answered k = true →
      round.view k = check (trace.state (round.sampled k) |>.keeper k))
    {result prior : Nat} (covers : SamplesCovered round result)
    (confirmed : Committed (trace.state call.replied) result)
    (priorAck : Committed (trace.state call.started) prior) :
    prior ≤ result ∧ ∃ event, call.started ≤ event ∧ event ≤ call.replied ∧
      AtCut trace round.opened result event := by
  have opening (n : Nat) := opening_covered trace samples observes (openedCut := n) covers
  have lower : ¬ Committed (trace.state round.opened) (result + 1) :=
    fun chosen => (Nat.not_succ_le_self result) (opening _ chosen)
  obtain ⟨event, afterOpen, beforeReply, atCut⟩ :=
    cut_in_window trace samples.confirmed.beforeReply lower confirmed
  exact ⟨opening _ (trace.committed samples.queued priorAck), event,
    Nat.le_trans samples.queued afterOpen, beforeReply, atCut⟩

theorem published_cut (trace : Timeline Payload) {sample replied cut : Nat} (keeper : KeeperId)
    (beforeReply : sample ≤ replied) (covered : cut ≤ (trace.state sample |>.keeper keeper).head) :
    Committed (trace.state replied) cut := by
  let k := (trace.state sample).keeper keeper
  let inv := reachable_inv (trace.reachable sample)
  have advertised := keeper_head_was_advertised inv.emptyAdvertised (inv.reached keeper)
  obtain ⟨epoch, quorum⟩ := inv.chosen _ advertised
  have within : k.head ≤ k.history.length := (keeper_bounds (inv.reached keeper)).1
  exact trace.committed beforeReply ⟨epoch, k.history.take k.head, quorum, by
    rw [List.length_take, Nat.min_eq_left within]
    exact covered⟩


/-- The confirming publication round can follow the sampling round. It need only cover
    the pinned index, irrespective of newer tails observed while waiting. -/
theorem head_after_publication (trace : Timeline Payload) {call : Invocation}
    {sampled confirmed : CheckRound} (samples : Samples call sampled)
    (confirmation : Samples call confirmed)
    (observes : ∀ k ∈ ensemble, sampled.answered k = true →
      sampled.view k = check (trace.state (sampled.sampled k) |>.keeper k))
    (confirms : ∀ k ∈ ensemble, confirmed.answered k = true →
      confirmed.view k = check (trace.state (confirmed.sampled k) |>.keeper k))
    {result prior : Nat} (covers : SamplesCovered sampled result)
    (published : Majority ensemble (fun k => confirmed.answered k && decide (result ≤ (confirmed.view k).head)))
    (priorAck : Committed (trace.state call.started) prior) :
    prior ≤ result ∧ ∃ event, call.started ≤ event ∧ event ≤ call.replied ∧
      AtCut trace sampled.opened result event := by
  obtain ⟨k, member, answered, covered⟩ :=
    majorities_overlap ensemble confirmed.answered _ confirmation.quorum published
  have localHead : result ≤ (confirmed.view k).head := by simpa [answered] using covered
  rw [confirms k member answered] at localHead
  exact head_linearizable trace samples observes covers
    (published_cut trace k (confirmation.fresh k member answered).2.2 localHead) priorAck


/-- Two fresh samples from the inherited-publication execution return its chosen LSN. -/
theorem inherited_head_witness :
    ∃ trace : Timeline Nat, ∃ event, 1 ≤ event ∧ event ≤ 3 ∧ AtCut trace 1 1 event := by
  obtain ⟨s, reached, head, first, second, left, right, _⟩ :=
    StreamIOWitness.automaton_witness
  let trace : Timeline Nat := ⟨fun _ => s, reached, fun _ => ⟨.restart 0, .restart⟩⟩
  let call : Invocation := ⟨0, 3⟩
  let round : CheckRound :=
    ⟨2, 1, fun k => decide (k = 0 ∨ k = 1), fun _ => 2, fun k => check (s.keeper k)⟩
  have samples : Samples call round := {
    sent := fun _ => 1
    queued := Nat.zero_le _
    quorum := two_of_three_is_majority 0 1 (by decide)
    fresh := fun _ _ _ => by
      change 1 ≤ 1 ∧ 1 ≤ 2 ∧ 2 ≤ 3
      decide
    eligible := by
      intro k _ answered
      simp only [round, decide_eq_true_eq] at answered
      rcases answered with rfl | rfl
      · exact first
      · exact second
  }
  have covered : SamplesCovered round 1 := by
    intro k _ answered
    simp only [round, decide_eq_true_eq] at answered
    rcases answered with rfl | rfl
    · change (s.keeper 0).history.length ≤ 1
      rw [left]
      decide
    · change (s.keeper 1).history.length ≤ 1
      rw [right]
      decide
  have chosen : Committed (trace.state call.replied) 1 :=
    published_cut trace (sample := 2) (replied := 3) 0 (by decide) (by simp [trace, head])
  obtain ⟨_, event, _, beforeReply, exactCut⟩ := head_linearizable trace samples
    (fun _ _ _ => rfl) covered chosen (prior := 0)
    (published_cut trace (sample := 0) (replied := 0) 0 (by decide) (Nat.zero_le _))
  have afterOpen : 1 ≤ event := by
    rcases exactCut.2 with ⟨same, _⟩ | ⟨later, _⟩
    · exact Nat.le_of_eq same.symm
    · exact Nat.le_of_lt later
  exact ⟨trace, event, afterOpen, beforeReply, exactCut⟩

#print axioms inherited_head_witness

#print axioms head_after_publication

#print axioms head_linearizable
#print axioms published_cut

end Logkeeper.StreamHead
