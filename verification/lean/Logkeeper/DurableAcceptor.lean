import Logkeeper.PrefixAgreement

namespace Logkeeper

set_option warningAsError true

namespace DurableAcceptor

open PrefixAgreement

structure State (Command : Type) where
  promised : Nat
  latest : Option (Vote Command)
  votes : Vote Command → Prop
  replies : Nat → Option (Option (Vote Command))

def initial : State Command :=
  ⟨0, none, fun _ => False, fun _ => none⟩

def acceptVote (state : State Command) (vote : Vote Command) : State Command :=
  { state with
      promised := vote.ballot
      latest := some vote
      votes := fun earlier => state.votes earlier ∨ earlier = vote }

def promise (state : State Command) (ballot : Nat) : State Command :=
  { state with
      promised := ballot
      replies := fun time => if time = ballot then some state.latest else state.replies time }

/-- A retry at the existing floor acknowledges the same promise. -/
def PrepareAdmitted (floor ballot : Nat) : Prop := floor ≤ ballot

/-- The native protocol requires its own prepare before accepting. -/
def AcceptAtPromise (floor ballot : Nat) : Prop := floor ≠ 0 ∧ floor = ballot

theorem promise_only_advances_above_floor {floor ballot : Nat}
    (admitted : PrepareAdmitted floor ballot) (changed : floor ≠ ballot) :
    floor < ballot :=
  Nat.lt_of_le_of_ne admitted changed

theorem accept_at_or_above_promise {floor ballot : Nat}
    (admitted : AcceptAtPromise floor ballot) : floor ≤ ballot :=
  Nat.le_of_eq admitted.2

instance (floor ballot : Nat) : Decidable (PrepareAdmitted floor ballot) :=
  inferInstanceAs (Decidable (floor ≤ ballot))

instance (floor ballot : Nat) : Decidable (AcceptAtPromise floor ballot) :=
  inferInstanceAs (Decidable (floor ≠ 0 ∧ floor = ballot))

#guard !(decide (PrepareAdmitted 3 2))
#guard !(decide (AcceptAtPromise 3 2))
#guard !(decide (AcceptAtPromise 3 4))
#guard decide (PrepareAdmitted 3 3)

inductive Step : State Command → State Command → Prop
  | accept {state} (vote : Vote Command) (abovePromise : state.promised ≤ vote.ballot)
      (keepsRank : ∀ old, state.latest = some old → RankLE old vote) :
      Step state (acceptVote state vote)
  | prepare {state} (ballot : Nat) (newer : state.promised < ballot) :
      Step state (promise state ballot)
  | restart {state} : Step state state

def prepareOrRetry (state : State Command) (ballot : Nat) : State Command :=
  if state.promised = ballot then state else promise state ballot

theorem prepare_or_retry_is_step {state : State Command} {ballot : Nat}
    (admitted : PrepareAdmitted state.promised ballot) :
    Step state (prepareOrRetry state ballot) := by
  by_cases same : state.promised = ballot
  · simpa [prepareOrRetry, same] using (Step.restart (state := state))
  · simpa [prepareOrRetry, same] using
      (Step.prepare (state := state) ballot (promise_only_advances_above_floor admitted same))

theorem accept_at_promise_is_step {state : State Command} (vote : Vote Command)
    (admitted : AcceptAtPromise state.promised vote.ballot)
    (keepsRank : ∀ old, state.latest = some old → RankLE old vote) :
    Step state (acceptVote state vote) :=
  .accept vote (accept_at_or_above_promise admitted) keepsRank

#print axioms promise_only_advances_above_floor
#print axioms accept_at_promise_is_step
#print axioms prepare_or_retry_is_step

inductive Reachable : State Command → Prop
  | initial : Reachable initial
  | extend {before after : State Command} : Reachable before → Step before after → Reachable after

def Covers (saved : Option (Vote Command)) (earlier : Vote Command) : Prop :=
  ∃ reported, saved = some reported ∧ RankLE earlier reported

structure Sound (state : State Command) : Prop where
  latestRecorded : ∀ reported, state.latest = some reported →
    state.votes reported ∧ reported.ballot ≤ state.promised
  dominates : ∀ vote, state.votes vote → Covers state.latest vote
  repliesSound : ∀ ballot saved, state.replies ballot = some saved →
    ballot ≤ state.promised ∧
    (∀ observed, saved = some observed → state.votes observed ∧ observed.ballot < ballot) ∧
    ∀ vote, state.votes vote → vote.ballot < ballot → Covers saved vote

theorem initial_sound : Sound (initial : State Command) := by
  constructor <;> simp [initial]

private theorem accept_preserves_soundness {state : State Command} (sound : Sound state)
    (vote : Vote Command) (floor : state.promised ≤ vote.ballot)
    (keepsRank : ∀ old, state.latest = some old → RankLE old vote) :
    Sound (acceptVote state vote) := by
  constructor
  · intro observed selected
    change some vote = some observed at selected
    have equal := Option.some.inj selected
    subst observed
    exact ⟨Or.inr rfl, Nat.le_refl _⟩
  · intro earlier hasVote
    rcases hasVote with old | rfl
    · obtain ⟨latest, selected, dominates⟩ := sound.dominates earlier old
      exact ⟨vote, rfl, rank_trans dominates (keepsRank latest selected)⟩
    · exact ⟨earlier, rfl, rank_refl earlier⟩
  · intro ballot saved recorded
    obtain ⟨promised, faithful, covers⟩ := sound.repliesSound ballot saved recorded
    refine ⟨Nat.le_trans promised floor, ?_, ?_⟩
    · intro observed selected
      obtain ⟨existed, earlier⟩ := faithful observed selected
      exact ⟨Or.inl existed, earlier⟩
    · intro earlier hasVote below
      rcases hasVote with accepted | rfl
      · exact covers earlier accepted below
      · exact False.elim (Nat.not_lt_of_ge (Nat.le_trans promised floor) below)

private theorem prepare_preserves_soundness {state : State Command} (sound : Sound state)
    (ballot : Nat) (newer : state.promised < ballot) : Sound (promise state ballot) := by
  constructor
  · intro observed selected
    obtain ⟨recorded, rank⟩ := sound.latestRecorded observed selected
    exact ⟨recorded, Nat.le_trans rank (Nat.le_of_lt newer)⟩
  · exact sound.dominates
  · intro requested saved recorded
    change (if requested = ballot then some state.latest else state.replies requested) = some saved at recorded
    by_cases same : requested = ballot
    · subst requested
      simp at recorded
      subst saved
      refine ⟨Nat.le_refl _, ?_, fun vote accepted _ => sound.dominates vote accepted⟩
      intro observed selected
      obtain ⟨hasVote, rank⟩ := sound.latestRecorded observed selected
      exact ⟨hasVote, Nat.lt_of_le_of_lt rank newer⟩
    · simp [same] at recorded
      obtain ⟨staysPromised, faithful, coverage⟩ := sound.repliesSound requested saved recorded
      exact ⟨Nat.le_trans staysPromised (Nat.le_of_lt newer), faithful, coverage⟩

theorem every_step_preserves_durable_replies {before after : State Command}
    (sound : Sound before) (step : Step before after) : Sound after := by
  cases step with
  | accept vote floor keepsRank => exact accept_preserves_soundness sound vote floor keepsRank
  | prepare term newer => exact prepare_preserves_soundness sound term newer
  | restart => exact sound

theorem reachable_replies_cover_every_lower_vote {state : State Command}
    (reached : Reachable state) : Sound state := by
  induction reached with
  | initial => exact initial_sound
  | extend _ step prior => exact every_step_preserves_durable_replies prior step

theorem durable_acceptor_traces_supply_quorum_reply_coverage {ledger : Ledger Voter Command}
    (replicas : Voter → State Command)
    (reached : ∀ voter ∈ ledger.members, Reachable (replicas voter))
    (accepts : ∀ voter ∈ ledger.members, ∀ vote, ledger.voted voter vote → (replicas voter).votes vote)
    (reports : ∀ voter ∈ ledger.members, ∀ ballot, ledger.prepared ballot voter = true →
      (replicas voter).replies ballot = some (ledger.report ballot voter)) : ReplyCoverage ledger := by
  intro ballot voter member prepared vote voted earlier
  have sound := reachable_replies_cover_every_lower_vote (reached voter member)
  obtain ⟨_, _, captures⟩ := sound.repliesSound ballot (ledger.report ballot voter)
    (reports voter member ballot prepared)
  exact captures vote (accepts voter member vote voted) earlier

theorem durable_replica_histories_agree {ledger : Ledger Voter Command}
    (ballots : BallotRules ledger) (replicas : Voter → State Command)
    (reached : ∀ voter ∈ ledger.members, Reachable (replicas voter))
    (accepts : ∀ voter ∈ ledger.members, ∀ vote, ledger.voted voter vote → (replicas voter).votes vote)
    (reports : ∀ voter ∈ ledger.members, ∀ ballot, ledger.prepared ballot voter = true →
      (replicas voter).replies ballot = some (ledger.report ballot voter))
    {first second : Nat} {left right : List Command}
    (oldChoice : Chosen ledger first left) (newChoice : Chosen ledger second right) :
    left <+: right ∨ right <+: left := by
  have coverage := durable_acceptor_traces_supply_quorum_reply_coverage replicas reached accepts reports
  exact every_chosen_prefix_agrees ⟨ballots, coverage⟩ oldChoice newChoice

#print axioms initial_sound
#print axioms every_step_preserves_durable_replies
#print axioms reachable_replies_cover_every_lower_vote
#print axioms durable_acceptor_traces_supply_quorum_reply_coverage
#print axioms durable_replica_histories_agree

end DurableAcceptor

end Logkeeper
