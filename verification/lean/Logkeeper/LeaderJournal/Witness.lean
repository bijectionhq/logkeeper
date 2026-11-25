import Logkeeper.LeaderJournal.Recovery

namespace Logkeeper.LeaderJournal
namespace Witness

set_option warningAsError true

private def members : List KeeperId := [0, 1, 2]
private def start : Cluster Nat := initial members
private def leader : Cluster Nat := { start with term := 1, leader := some 0 }

private theorem leader_step : Step start leader := by
  refine .elect 0 1 ([0, 1] : List KeeperId).contains (by decide) (by decide)
    (Or.inl rfl) (by decide) (by decide) ?_ ?_
  · intro _ _
    rfl
  · intro _ _
    exact Or.inr ⟨rfl, Nat.le_refl _⟩

private def write (s : Cluster Nat) (command : Command (Request Nat)) (voters : List KeeperId) :
    Cluster Nat :=
  let sent := s.issue command
  let saved := sent.replicateTo voters sent.issued
  { saved with
    committed := sent.issued
    leader := saved.leader.filter (saved.effectiveConfiguration.contains) }

private theorem write_trace (s : Cluster Nat) (command : Command (Request Nat))
    (voters : List KeeperId) (sound : Sound s) (active : s.active)
    (admitted : s.admits command)
    (online : s.responds voters.contains)
    (quorum : (s.issue command).effectiveConfiguration.quorum voters.contains) :
    Trace s (write s command voters) := by
  let sent := s.issue command
  let saved := sent.replicateTo voters sent.issued
  have issue : Step s sent := .issue command active admitted
  have copy : Trace sent saved :=
    replicate_to_trace sent voters sent.issued active
      (fun keeper member => online keeper (List.contains_iff_mem.mpr member)) List.prefix_rfl
  have commit : Step saved (write s command voters) := by
    apply Step.commit (s := saved) sent.issued voters.contains active
    · have bound := sound.leaderContains.length_le
      change s.committed.length ≤ (s.issued ++ [Entry.mk s.term command]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · exact List.prefix_rfl
    · simp [saved, sent, State.replicateTo, State.issue, lastTerm, List.getLast?_append]
    · rfl
    · exact quorum
    · intro keeper vote
      exact replicate_to_covers sent voters sent.issued (List.contains_iff_mem.mp vote)
  exact (issue.trace.trans copy).trans commit.trace

private def sealCommand : Command (Request Nat) := .apply (.seal 0 9)
private def sealed : Cluster Nat := write leader sealCommand [0, 1]
private def sealApplied : Cluster Nat :=
  { sealed with applied := update sealed.applied 0 sealed.committed }

private theorem seal_trace : Trace start sealApplied := by
  have sound := leader_step.trace.sound (initial_sound members (by decide))
  have writeSeal := write_trace leader sealCommand [0, 1] sound
    ⟨0, rfl, rfl⟩ trivial (fun _ _ => rfl) (by decide)
  have applySeal : Step sealed sealApplied :=
    .apply 0 sealed.committed (by decide) (by decide) List.prefix_rfl (by decide)
  exact (leader_step.trace.trans writeSeal).trans applySeal.trace

private def fence : Fence := ⟨1, 9⟩
private def appendCommand : Command (Request Nat) := .apply (.append fence 1 71)
private def written : Cluster Nat := write sealApplied appendCommand [0, 1]
private def acknowledged : Cluster Nat :=
  { written with applied := update written.applied 0 written.committed }

private theorem reached : Reachable members acknowledged := by
  have sound := seal_trace.sound (initial_sound members (by decide))
  have writeAppend := write_trace sealApplied appendCommand [0, 1] sound
    ⟨0, by decide, by decide⟩ trivial (fun _ _ => rfl) (by decide)
  have applyAppend : Step written acknowledged :=
    .apply 0 written.committed (by decide) (by decide) List.prefix_rfl (by decide)
  exact ⟨by decide, by decide, (seal_trace.trans writeAppend).trans applyAppend.trace⟩

private def reply : AppendReply acknowledged 1 71 where
  keeper := 0
  term := 1
  fence := fence
  prior := [⟨1, sealCommand⟩]
  leader := by decide
  applied := by decide
  result := by decide

private def afterFailure : Cluster Nat :=
  { acknowledged with
    online := update acknowledged.online 0 false
    leader := none }

private theorem failure : Trace acknowledged afterFailure :=
  (show Step acknowledged afterFailure from .fail 0).trace

private def replacement : Election afterFailure where
  candidate := 1
  term := 2
  voters := [1, 2]
  newer := by decide
  candidateOnline := by decide
  permitted := Or.inl (by decide)
  member := by decide
  quorum := by decide
  online := by
    intro keeper votes
    simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at votes
    rcases votes with rfl | rfl <;> decide
  rank := by
    intro keeper votes
    simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at votes
    rcases votes with rfl | rfl
    · exact Or.inr ⟨rfl, Nat.le_refl _⟩
    · exact Or.inl (by decide)

/-- Neither survivor knows the committed head. The chosen bytes still reach
    the fresh Head response via election and current-term recovery. -/
theorem failover_before_publication :
    (appliedView afterFailure 1).head = 0 ∧ (appliedView afterFailure 2).head = 0 ∧
      ∃ recovered : Cluster Nat, ∃ call : HeadRead afterFailure recovered,
        recovered.leader = some 1 ∧ (committedView recovered).record 1 = some 71 ∧
        call.reply = .ok 1 := by
  obtain ⟨recovered, call, carries, exactHistory, captured, leader, _⟩ :=
    recover_and_serve (failure.sound (reachable_sound reached)) replacement
  have exactRecord := (replay_progress carries).record
    (acknowledged_append_survives reached reply failure)
  refine ⟨rfl, rfl, recovered, call, leader, exactRecord, ?_⟩
  rw [call.reply_at_capture, captured, committedView, exactHistory]
  rfl

theorem behind_candidate_cannot_win_survivors :
    ¬ AtLeast (afterFailure.durable 1) (afterFailure.durable 2) := by
  unfold AtLeast
  decide

/-- Move to a disjoint roster. Membership is an internal log entry and the
    old leader completes the move without being a voter on the final entry. -/
private def nextMembers : List KeeperId := [3, 4, 5]
private def learners : Cluster Nat := acknowledged.replicateTo nextMembers acknowledged.issued
private def joint : Configuration := .joint members nextMembers
private def jointChosen : Cluster Nat := write learners (.configure joint) [0, 1, 3, 4]
private def finalChosen : Cluster Nat :=
  write jointChosen (.configure (.stable nextMembers)) [3, 4]

private theorem movement : Trace acknowledged finalChosen := by
  have sound := reachable_sound reached
  have active : acknowledged.active := ⟨0, by decide, by decide⟩
  have copied : Trace acknowledged learners :=
    replicate_to_trace acknowledged nextMembers acknowledged.issued active
      (fun _ _ => rfl) List.prefix_rfl
  have learnersReady : learners.learnersReady joint := by
    intro keeper inNext _
    exact replicate_to_covers acknowledged nextMembers acknowledged.issued inNext
  have enter := write_trace learners (.configure joint) [0, 1, 3, 4] (copied.sound sound)
    active ⟨rfl, .enter (by decide) (by decide), learnersReady⟩ (fun _ _ => rfl) (by decide)
  have finish := write_trace jointChosen (.configure (.stable nextMembers)) [3, 4]
    (enter.sound (copied.sound sound)) ⟨0, by decide, by decide⟩ ⟨rfl, .finish, trivial⟩
    (fun _ _ => rfl) (by decide)
  exact (copied.trans enter).trans finish

theorem disjoint_move_preserves_acknowledged_append :
    finalChosen.configuration = .stable nextMembers ∧ finalChosen.leader = none ∧
      (committedView finalChosen).record 1 = some 71 ∧
      ¬ (finalChosen.configuration = finalChosen.candidateConfiguration 0 ∨
        finalChosen.configuration.Change (finalChosen.candidateConfiguration 0)) := by
  refine ⟨rfl, rfl, acknowledged_append_survives reached reply movement, ?_⟩
  change ¬ ((.stable nextMembers : Configuration) = joint ∨
    (.stable nextMembers : Configuration).Change joint)
  intro route
  rcases route with equal | regressed
  · contradiction
  · cases regressed

private def newElection : Election finalChosen where
  candidate := 3
  term := 2
  voters := [3, 4]
  newer := by decide
  candidateOnline := by decide
  permitted := Or.inl (by decide)
  member := by decide
  quorum := by decide
  online := fun _ _ => rfl
  rank := by
    intro keeper votes
    simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at votes
    rcases votes with rfl | rfl <;> exact Or.inr ⟨rfl, Nat.le_refl _⟩

theorem disjoint_route_can_serve_fresh_head :
    ∃ recovered : Cluster Nat, ∃ call : HeadRead finalChosen recovered,
      recovered.leader = some 3 ∧ call.reply = .ok 1 := by
  obtain ⟨recovered, call, _, exactHistory, captured, leader, _⟩ :=
    recover_and_serve (movement.sound (reachable_sound reached)) newElection
  refine ⟨recovered, call, leader, ?_⟩
  rw [call.reply_at_capture, captured, committedView, exactHistory]
  rfl

#print axioms failover_before_publication
#print axioms disjoint_move_preserves_acknowledged_append
#print axioms disjoint_route_can_serve_fresh_head

end Witness
end Logkeeper.LeaderJournal
