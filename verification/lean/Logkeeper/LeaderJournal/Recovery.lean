import Logkeeper.LeaderJournal

namespace Logkeeper.LeaderJournal

set_option warningAsError true

/-- An available election under the stable or joint rules. The voting set is
    finite, and each vote names the candidate's durable election log. -/
structure Election [DecidableEq Payload] (s : Cluster Payload) where
  candidate : KeeperId
  term : Nat
  voters : List KeeperId
  newer : s.term < term
  candidateOnline : s.online candidate = true
  permitted : s.configuration = s.candidateConfiguration candidate ∨
    s.configuration.Change (s.candidateConfiguration candidate)
  member : (s.candidateConfiguration candidate).contains candidate = true
  quorum : (s.candidateConfiguration candidate).quorum voters.contains
  online : s.responds voters.contains
  rank : ∀ keeper, voters.contains keeper = true → AtLeast (s.durable keeper) (s.durable candidate)

private theorem rank_total (a b : Log Application) : AtLeast a b ∨ AtLeast b a := by
  unfold AtLeast
  by_cases same : lastTerm a = lastTerm b
  · rcases Nat.le_total a.length b.length with short | long
    · exact Or.inl (Or.inr ⟨same, short⟩)
    · exact Or.inr (Or.inr ⟨same.symm, long⟩)
  · by_cases less : lastTerm a < lastTerm b
    · exact Or.inl (Or.inl less)
    · exact Or.inr (Or.inl (by omega))

private theorem greatest_log (logs : KeeperId → Log Application) (voters : List KeeperId)
    (nonempty : voters ≠ []) :
    ∃ candidate ∈ voters, ∀ voter ∈ voters, AtLeast (logs voter) (logs candidate) := by
  induction voters with
  | nil => contradiction
  | cons keeper rest ih =>
      by_cases empty : rest = []
      · subst rest
        refine ⟨keeper, List.mem_cons_self, ?_⟩
        intro voter present
        have same : voter = keeper := List.mem_singleton.mp present
        subst voter
        exact Or.inr ⟨rfl, Nat.le_refl _⟩
      · obtain ⟨candidate, member, dominates⟩ := ih empty
        rcases rank_total (logs keeper) (logs candidate) with takeRest | takeFirst
        · refine ⟨candidate, List.mem_cons_of_mem _ member, ?_⟩
          intro voter present
          rcases List.mem_cons.mp present with rfl | inRest
          · exact takeRest
          · exact dominates voter inRest
        · refine ⟨keeper, List.mem_cons_self, ?_⟩
          intro voter present
          rcases List.mem_cons.mp present with rfl | inRest
          · exact Or.inr ⟨rfl, Nat.le_refl _⟩
          · exact (dominates voter inRest).trans takeFirst

/-- On a settled roster, reachable online voters can elect the most up-to-date
    member. A scheduler must still let the election and replication run. -/
theorem settled_election_available [DecidableEq Payload] {s : Cluster Payload}
    (voters : List KeeperId) (nonempty : voters ≠ [])
    (members : ∀ keeper ∈ voters, s.configuration.contains keeper = true)
    (settled : ∀ keeper ∈ voters, s.candidateConfiguration keeper = s.configuration)
    (majority : s.configuration.quorum voters.contains)
    (online : s.responds voters.contains) :
    Nonempty (Election s) := by
  obtain ⟨candidate, member, rank⟩ := greatest_log s.durable voters nonempty
  have same := settled candidate member
  exact ⟨{
    candidate
    term := s.term + 1
    voters
    newer := by omega
    candidateOnline := online candidate (List.contains_iff_mem.mpr member)
    permitted := Or.inl same.symm
    member := same.symm ▸ members candidate member
    quorum := same.symm ▸ majority
    online
    rank := fun keeper voted => rank keeper (List.contains_iff_mem.mp voted)
  }⟩

private theorem configuration_barrier (configuration : Configuration) (log : Log Application)
    (term : Nat) :
    configurationAt configuration (log ++ [⟨term, .barrier⟩]) =
      configurationAt configuration log := by
  simp [configurationAt, List.foldl_append]

/-- Construct the recovery path out of a successful election. The recovered
    leader can commit a current-term barrier, apply it, and answer Head. -/
theorem recover_and_serve [DecidableEq Payload] {s : Cluster Payload} (sound : Sound s)
    (election : Election s) :
    ∃ recovered : Cluster Payload, ∃ call : HeadRead s recovered,
      s.committed <+: recovered.committed ∧
      recovered.committed = s.durable election.candidate ++ [⟨election.term, .barrier⟩] ∧
      call.captured = recovered ∧
      recovered.leader = some election.candidate ∧ recovered.term = election.term := by
  let elected : Cluster Payload :=
    { s with
      term := election.term
      leader := some election.candidate
      issued := s.durable election.candidate }
  have elect : Step s elected :=
    .elect election.candidate election.term election.voters.contains election.newer
      election.candidateOnline election.permitted election.member election.quorum
      election.online election.rank
  have active : elected.active := ⟨election.candidate, rfl, election.candidateOnline⟩
  let issued := elected.issue .barrier
  have issue : Step elected issued := .issue .barrier active trivial
  have issuedActive : issued.active := active
  let cut := issued.issued
  let targets := election.candidate :: election.voters
  have online (keeper : KeeperId) (member : keeper ∈ targets) : issued.online keeper = true := by
    rcases List.mem_cons.mp member with atCandidate | atVoter
    · exact atCandidate ▸ election.candidateOnline
    · exact election.online keeper (List.contains_iff_mem.mpr atVoter)
  let replicated := issued.replicateTo targets cut
  have copy : Trace issued replicated :=
    replicate_to_trace issued targets cut issuedActive online List.prefix_rfl
  have quorum : (configurationAt replicated.genesis cut).quorum election.voters.contains := by
    change (configurationAt s.genesis (s.durable election.candidate ++
      [⟨election.term, .barrier⟩])).quorum election.voters.contains
    rw [configuration_barrier]
    exact election.quorum
  have member : (configurationAt replicated.genesis cut).contains election.candidate = true := by
    change (configurationAt s.genesis (s.durable election.candidate ++
      [⟨election.term, .barrier⟩])).contains election.candidate = true
    rw [configuration_barrier]
    exact election.member
  have carried : s.committed <+: cut :=
    (elected_log_contains_committed sound election.permitted election.quorum election.rank).trans
      (List.prefix_append _ _)
  have synced : replicated.supports election.voters.contains cut := by
    intro keeper votes
    exact replicate_to_covers issued targets cut (List.mem_cons_of_mem _ (List.contains_iff_mem.mp votes))
  have leaderSynced : cut <+: replicated.durable election.candidate :=
    replicate_to_covers issued targets cut List.mem_cons_self
  have cutTerm : lastTerm cut = election.term := by
    simp [cut, issued, elected, State.issue, lastTerm, List.getLast?_append]
  let committed : Cluster Payload :=
    { replicated with
      committed := cut
      leader := replicated.leader.filter ((configurationAt replicated.genesis cut).contains) }
  have choose : Step replicated committed :=
    .commit cut election.voters.contains issuedActive carried.length_le List.prefix_rfl cutTerm
      rfl quorum synced
  have committedLeader : committed.leader = some election.candidate := by
    change (some election.candidate).filter ((configurationAt replicated.genesis cut).contains) = _
    simp [Option.filter, member]
  let recovered : Cluster Payload :=
    { committed with applied := update committed.applied election.candidate cut }
  have appliedForward : committed.applied election.candidate <+: cut :=
    (sound.applied election.candidate).1.trans carried
  have apply : Step committed recovered :=
    .apply election.candidate cut election.candidateOnline appliedForward List.prefix_rfl leaderSynced
  have history := (((elect.trace.trans issue.trace).trans copy).trans choose.trace).trans apply.trace
  let call : HeadRead s recovered :=
    { keeper := election.candidate
      captured := recovered
      confirmed := recovered
      invokedBeforeCapture := history
      capturedBeforeConfirmation := (Step.idle : Step recovered recovered).trace
      confirmedBeforeReturn := .nil recovered
      capturedByLeader := committedLeader
      confirmedByLeader := committedLeader
      currentTermCommitted := cutTerm
      settledAtCapture := rfl
      settledAtConfirmation := rfl
      sameTerm := rfl
      sameMembership := rfl
      sameRevision := rfl
      voters := election.voters.contains
      quorum := quorum
      responds := election.online
      applied := by
        simp only [recovered, update_same]
        exact List.prefix_rfl }
  exact ⟨recovered, call, carried, rfl, rfl, committedLeader, rfl⟩

/-- An acknowledged append survives the whole recovery program, including a
    client-visible head. The recovered view can also report a later deletion. -/
theorem recover_head_after_acknowledged_append [DecidableEq Payload] {members : List KeeperId}
    {acknowledged afterFailure : Cluster Payload} {lsn : Nat} {payload : Payload}
    (reached : Reachable members acknowledged) (reply : AppendReply acknowledged lsn payload)
    (failure : Trace acknowledged afterFailure) (election : Election afterFailure) :
    ∃ recovered : Cluster Payload, ∃ call : HeadRead afterFailure recovered,
      recovered.leader = some election.candidate ∧
      (committedView recovered).record lsn = some payload ∧
      (call.reply = .error .deleted ∨ ∃ head, call.reply = .ok head ∧ lsn ≤ head) := by
  obtain ⟨recovered, call, carry, _, captured, leader, _⟩ :=
    recover_and_serve (failure.sound (reachable_sound reached)) election
  have record := (replay_progress carry).record (acknowledged_append_survives reached reply failure)
  refine ⟨recovered, call, leader, record, ?_⟩
  rw [call.reply_at_capture, captured]
  unfold observeHead
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, (record_bounds record).2⟩

#print axioms settled_election_available
#print axioms recover_and_serve
#print axioms recover_head_after_acknowledged_append

end Logkeeper.LeaderJournal
