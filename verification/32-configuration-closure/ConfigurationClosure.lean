import DurableAcceptor

set_option warningAsError true

namespace ConfigurationClosure

open PrefixAgreement JournalRefinement

variable {Voter Command : Type}

structure VoterState (Command : Type) where
  acceptor : DurableAcceptor.State Command
  closedFor : Option Nat

def initial : VoterState Command := ⟨DurableAcceptor.initial, none⟩

def CanOperate (state : VoterState Command) : Prop := state.closedFor = none

inductive Step (authorized : Nat → Prop) : VoterState Command → VoterState Command → Prop
  | operate {state next} (openScope : CanOperate state)
      (step : DurableAcceptor.Step state.acceptor next) :
      Step authorized state {state with acceptor := next}
  | fence {state} (successor : Nat) (permitted : authorized successor)
      (openScope : state.closedFor = none) :
      Step authorized state {state with closedFor := some successor}
  | restart {state} : Step authorized state state

inductive Trace (authorized : Nat → Prop) : VoterState Command → VoterState Command → Prop
  | same (state : VoterState Command) : Trace authorized state state
  | next {first before after} : Trace authorized first before → Step authorized before after →
      Trace authorized first after

theorem voter_trace_preserves_rank_evidence {authorized : Nat → Prop} {state : VoterState Command}
    (trace : Trace authorized initial state) : DurableAcceptor.Sound state.acceptor := by
  induction trace with
  | same => exact DurableAcceptor.initial_sound
  | next _ step prior =>
      cases step with
      | operate _ step => exact DurableAcceptor.every_step_preserves_durable_replies prior step
      | fence => exact prior
      | restart => exact prior

private theorem a_closed_voter_stutters {authorized : Nat → Prop}
    {before after : VoterState Command} (successor : Nat) (fenced : before.closedFor = some successor)
    (step : Step authorized before after) : after = before := by
  cases step with
  | operate openScope _ =>
      have impossible : before.closedFor = none := by
        exact openScope
      simp [fenced] at impossible
  | fence _ _ openScope => simp [fenced] at openScope
  | restart => rfl

theorem once_fenced_the_scoped_acceptor_is_immutable {authorized : Nat → Prop}
    {before after : VoterState Command} (successor : Nat) (fenced : before.closedFor = some successor)
    (trace : Trace authorized before after) : after = before := by
  induction trace with
  | same => rfl
  | next _ step unchanged =>
      exact (a_closed_voter_stutters successor (unchanged.symm ▸ fenced) step).trans unchanged

theorem a_fenced_majority_excludes_all_fresh_old_votes
    {authorized : Nat → Prop} {before after : Voter → VoterState Command}
    (members : List Voter) (fenced newVotes : Voter → Bool) (successor : Nat)
    (quorum : Majority members fenced)
    (closed : ∀ voter ∈ members, fenced voter = true → (before voter).closedFor = some successor)
    (traces : ∀ voter ∈ members, Trace authorized (before voter) (after voter))
    (issued : ∀ voter ∈ members, newVotes voter = true →
      ∃ vote, ¬ (before voter).acceptor.votes vote ∧ (after voter).acceptor.votes vote) :
    ¬ Majority members newVotes := by
  apply durable_fence_excludes_stale_majority members fenced newVotes quorum
  intro voter member fenceVote
  cases supplied : newVotes voter with
  | false => rfl
  | true =>
      obtain ⟨vote, missing, suppliedVote⟩ := issued voter member supplied
      have unchanged := once_fenced_the_scoped_acceptor_is_immutable
        successor (closed voter member fenceVote) (traces voter member)
      exact False.elim (missing (unchanged ▸ suppliedVote))

structure Certificate (Voter Command : Type) where
  successor : Nat
  replied : Voter → Bool
  captured : Voter → Option (Vote Command)
  winner : Option (Vote Command)

def EmptyRecovery (basis : List Command) : List Command := basis

def Recovered (basis : List Command) (certificate : Certificate Voter Command) : List Command :=
  certificate.winner.elim (EmptyRecovery basis) Vote.history

def CoversEveryVote (ledger : Ledger Voter Command) (certificate : Certificate Voter Command) : Prop :=
  ∀ voter ∈ ledger.members, certificate.replied voter = true → ∀ vote,
    ledger.voted voter vote → DurableAcceptor.Covers (certificate.captured voter) vote

structure Ranked (ledger : Ledger Voter Command) (certificate : Certificate Voter Command) : Prop where
  quorum : Majority ledger.members certificate.replied
  authenticated : ∀ best, certificate.winner = some best →
    ∃ source, source ∈ ledger.members ∧ certificate.replied source = true ∧
      certificate.captured source = some best ∧ ledger.voted source best
  maximal : ∀ voter ∈ ledger.members, certificate.replied voter = true →
    ∀ observed, certificate.captured voter = some observed →
      ∃ best, certificate.winner = some best ∧ RankLE observed best

theorem durable_fenced_reports_cover_even_delayed_certificate_assembly
    {authorized : Nat → Prop} {ledger : Ledger Voter Command}
    {certificate : Certificate Voter Command} (captured now : Voter → VoterState Command)
    (arrived : ∀ voter ∈ ledger.members, certificate.replied voter = true →
      Trace authorized initial (captured voter))
    (fenced : ∀ voter ∈ ledger.members, certificate.replied voter = true →
      (captured voter).closedFor = some certificate.successor)
    (duringDelivery : ∀ voter ∈ ledger.members, certificate.replied voter = true →
      Trace authorized (captured voter) (now voter))
    (scopedReceipt : ∀ voter ∈ ledger.members, certificate.replied voter = true →
      certificate.captured voter = (captured voter).acceptor.latest)
    (actualVotes : ∀ voter ∈ ledger.members, ∀ vote,
      ledger.voted voter vote → (now voter).acceptor.votes vote) :
    CoversEveryVote ledger certificate := by
  intro voter member replied vote accepted
  have immutable := once_fenced_the_scoped_acceptor_is_immutable certificate.successor
    (fenced voter member replied) (duringDelivery voter member replied)
  have sound := voter_trace_preserves_rank_evidence (arrived voter member replied)
  rw [scopedReceipt voter member replied]
  exact sound.dominates vote (immutable ▸ actualVotes voter member vote accepted)

theorem ranked_cut_covers_every_old_quorum_even_if_learned_late
    {ledger : Ledger Voter Command} (rules : Rules ledger)
    {certificate : Certificate Voter Command} (ranked : Ranked ledger certificate)
    (covers : CoversEveryVote ledger certificate) (basis : List Command)
    {ballot : Nat} {history : List Command} (chosen : Chosen ledger ballot history) :
    history <+: Recovered basis certificate := by
  obtain ⟨voters, quorum, accepts⟩ := chosen
  obtain ⟨replica, member, voted, replied⟩ :=
    majorities_overlap ledger.members voters certificate.replied quorum ranked.quorum
  obtain ⟨vote, oldVote, sameBallot, choicePrefix⟩ := accepts replica member voted
  obtain ⟨observed, sample, hasRank⟩ := covers replica member replied vote oldVote
  obtain ⟨best, selected, dominates⟩ := ranked.maximal replica member replied observed sample
  obtain ⟨source, _, _, _, newVote⟩ := ranked.authenticated best selected
  have winningRank := rank_trans hasRank dominates
  have onWinnerChain := rules.chain source best newVote
  have noEarlier : ballot ≤ best.ballot := sameBallot ▸ winningRank.1
  simp only [Recovered, selected, Option.elim_some]
  by_cases equal : ballot = best.ballot
  · have sameChain : vote.history <+: ledger.issued best.ballot :=
      (sameBallot.trans equal) ▸ (rules.chain replica vote oldVote).2.2
    exact choicePrefix.trans (List.prefix_of_prefix_length_le sameChain onWinnerChain.2.2
      (winningRank.2 (sameBallot.trans equal)))
  · have newer : ballot < best.ballot := by omega
    exact (later_ballot_inherits_chosen_prefix rules ⟨voters, quorum, accepts⟩
      best.ballot newer onWinnerChain.1).trans onWinnerChain.2.1

structure Generation (Voter Command : Type) where
  ledger : Ledger Voter Command
  rules : Rules ledger
  basis : List Command
  startsFromBasis : ∀ voter vote, ledger.voted voter vote → basis <+: vote.history
  installed : Voter → List Command → Prop

def InstalledOnQuorum (generation : Generation Voter Command) : Prop :=
  ∃ voters, Majority generation.ledger.members voters ∧
    ∀ voter ∈ generation.ledger.members, voters voter = true →
      generation.installed voter generation.basis

structure Handoff (before after : Generation Voter Command) : Prop where
  transfer : ∃ cut, Ranked before.ledger cut ∧ CoversEveryVote before.ledger cut ∧
    after.basis = Recovered before.basis cut
  installed : InstalledOnQuorum after

theorem handoff_preserves_previously_installed_basis {before after : Generation Voter Command}
    (handoff : Handoff before after) : before.basis <+: after.basis := by
  obtain ⟨cut, ranked, _, exactCut⟩ := handoff.transfer
  rw [exactCut]
  cases winning : cut.winner with
  | none =>
      have fallback : Recovered before.basis cut = before.basis := by
        simp [Recovered, winning, EmptyRecovery]
      rw [fallback]
      exact List.prefix_rfl
  | some best =>
      obtain ⟨voter, _, _, _, accepted⟩ := ranked.authenticated best winning
      simpa [Recovered, winning] using before.startsFromBasis voter best accepted

theorem handoff_inherits_every_prior_choice {before after : Generation Voter Command}
    (handoff : Handoff before after) {ballot : Nat} {history : List Command}
    (chosen : Chosen before.ledger ballot history) : history <+: after.basis := by
  obtain ⟨cut, ranked, covers, exactCut⟩ := handoff.transfer
  rw [exactCut]
  exact ranked_cut_covers_every_old_quorum_even_if_learned_late before.rules ranked covers before.basis chosen

inductive Changes : Generation Voter Command → Generation Voter Command → Prop
  | same (generation : Generation Voter Command) : Changes generation generation
  | next {first before after} : Changes first before → Handoff before after → Changes first after

theorem arbitrarily_many_changes_keep_installed_prefix {before after : Generation Voter Command}
    (changes : Changes before after) : before.basis <+: after.basis := by
  induction changes with
  | same => exact List.prefix_rfl
  | next _ handoff earlier => exact earlier.trans (handoff_preserves_previously_installed_basis handoff)

theorem earlier_choice_reaches_any_later_recovery_majority
    {before next current : Generation Voter Command}
    (firstChange : Handoff before next) (later : Changes next current)
    (installed : InstalledOnQuorum current) (available : Voter → Bool)
    (recovering : Majority current.ledger.members available) {ballot : Nat} {history : List Command}
    (chosen : Chosen before.ledger ballot history) :
    ∃ voter ∈ current.ledger.members, available voter = true ∧
      current.installed voter current.basis ∧ history <+: current.basis := by
  obtain ⟨holders, quorum, exactCopy⟩ := installed
  obtain ⟨voter, member, online, held⟩ :=
    majorities_overlap current.ledger.members available holders recovering quorum
  have bytes : current.installed voter current.basis := by
    exact exactCopy voter member held
  exact ⟨voter, member, online, bytes, (handoff_inherits_every_prior_choice firstChange chosen).trans
    (arbitrarily_many_changes_keep_installed_prefix later)⟩

theorem a_later_choice_agrees_with_every_prior_choice
    {before next current : Generation Voter Command}
    (firstChange : Handoff before next) (later : Changes next current)
    {earlierBallot laterBallot : Nat} {earlierHistory laterHistory : List Command}
    (earlier : Chosen before.ledger earlierBallot earlierHistory)
    (latest : Chosen current.ledger laterBallot laterHistory) :
    earlierHistory <+: laterHistory ∨ laterHistory <+: earlierHistory := by
  obtain ⟨holders, quorum, accepts⟩ := latest
  obtain ⟨voter, member, agreed, _⟩ := majorities_overlap current.ledger.members holders holders quorum quorum
  obtain ⟨vote, accepted, _, newPrefix⟩ := accepts voter member agreed
  have earlierPrefix := (handoff_inherits_every_prior_choice firstChange earlier).trans
    (arbitrarily_many_changes_keep_installed_prefix later)
  exact List.prefix_or_prefix_of_prefix (earlierPrefix.trans (current.startsFromBasis voter vote accepted))
    newPrefix

theorem a_fixed_fence_constituency_binds_at_most_one_successor (members : List Voter)
    (closedFor : Voter → Option Nat) (left right : Voter → Bool) (first second : Nat)
    (firstMajority : Majority members left) (secondMajority : Majority members right)
    (attestsFirst : ∀ voter ∈ members, left voter = true → closedFor voter = some first)
    (attestsSecond : ∀ voter ∈ members, right voter = true → closedFor voter = some second) :
    first = second := by
  obtain ⟨voter, member, votedFirst, votedSecond⟩ :=
    majorities_overlap members left right firstMajority secondMajority
  exact Option.some.inj ((attestsFirst voter member votedFirst).symm.trans
    (attestsSecond voter member votedSecond))

def BlocksJointWrites (old new : List Voter) (fenced : Voter → Bool) : Prop :=
  ∀ votes, Majority old votes → Majority new votes →
    ∃ voter, fenced voter = true ∧ votes voter = true

theorem closure_quorums_that_block_joint_writes_can_be_disjoint :
    ∃ left right : Nat → Bool, BlocksJointWrites [1, 2, 3] [2, 3, 4] left ∧
      BlocksJointWrites [1, 2, 3] [2, 3, 4] right ∧
      ∀ voter, left voter = true → right voter = false := by
  obtain ⟨left, right, fenceOld, fenceNew, disjoint⟩ :=
    overlapping_configurations_can_have_disjoint_majorities
  refine ⟨left, right, ?_, ?_, disjoint⟩
  · intro votes oldVotes _
    obtain ⟨voter, _, fenced, voted⟩ := majorities_overlap [1, 2, 3] left votes fenceOld oldVotes
    exact ⟨voter, fenced, voted⟩
  · intro votes _ newVotes
    obtain ⟨voter, _, fenced, voted⟩ := majorities_overlap [2, 3, 4] right votes fenceNew newVotes
    exact ⟨voter, fenced, voted⟩

#print axioms voter_trace_preserves_rank_evidence
#print axioms once_fenced_the_scoped_acceptor_is_immutable
#print axioms a_fenced_majority_excludes_all_fresh_old_votes
#print axioms durable_fenced_reports_cover_even_delayed_certificate_assembly
#print axioms ranked_cut_covers_every_old_quorum_even_if_learned_late
#print axioms handoff_preserves_previously_installed_basis
#print axioms handoff_inherits_every_prior_choice
#print axioms arbitrarily_many_changes_keep_installed_prefix
#print axioms earlier_choice_reaches_any_later_recovery_majority
#print axioms a_later_choice_agrees_with_every_prior_choice
#print axioms a_fixed_fence_constituency_binds_at_most_one_successor
#print axioms closure_quorums_that_block_joint_writes_can_be_disjoint

end ConfigurationClosure
