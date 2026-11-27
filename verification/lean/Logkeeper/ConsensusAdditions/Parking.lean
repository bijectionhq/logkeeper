import Logkeeper.JournalRefinement

/-!
Parking idle streams (design section D, `keeper/park.rs`).

A leader whose group is idle and settled asks each live follower to park.
A follower parks only when `decisions::accepts_park` holds: it follows under
the leader's vote, its last applied log id is the leader's, and it holds no
entry past it. A parked replica answers an empty heartbeat busy and a
repeated park without opening its group, and anything else reopens it.

Parking, the busy answer and reopening change only whether a group is open.
`parking_preserves_durable_state` shows every such step keeps each replica's
vote, log and applied index, so they are stutter steps of the Raft core and
preserve every property of it, among them the committed log
(`parking_preserves_the_committed_log`). `accept_requires_exact_log` and
`accepted_followers_hold_the_committed_log` show what a park round
establishes: under Raft's log matching, each parked follower holds exactly
the leader's applied log, and with it every committed entry.
-/

namespace Logkeeper.ConsensusAdditions.Parking

open JournalRefinement (Majority)

set_option warningAsError true

abbrev KeeperId := Nat

structure Entry where
  term : Nat
  payload : Nat
  deriving DecidableEq, Repr

abbrev Log := List Entry

structure Vote where
  term : Nat
  leader : KeeperId
  committed : Bool
  deriving DecidableEq, Repr

structure Replica where
  vote : Vote
  log : Log
  applied : Nat
  following : Bool
  idle : Bool
  parked : Bool

/-- What a restart or a reopened group recovers: the vote, the log and the
    applied state machine. -/
def Replica.durable (replica : Replica) : Vote × Log × Nat :=
  (replica.vote, replica.log, replica.applied)

/-- The term of the entry at a one-based log index; index zero is the empty
    log id. -/
def termAt (log : Log) (index : Nat) : Option Nat :=
  if index = 0 then none else (log[index - 1]?).map Entry.term

/-- `decisions::accepts_park`: a follower under the leader's vote whose last
    applied log id and last log index both equal the leader's applied log id. -/
def acceptsPark (replica : Replica) (vote : Vote) (lastIndex : Nat) (lastTerm : Option Nat) : Bool :=
  replica.following && replica.vote == vote && replica.applied == lastIndex &&
    termAt replica.log replica.applied == lastTerm && replica.log.length == lastIndex && replica.idle

/-- `decisions::leader_parks`: the leader applied its whole log, every live
    follower matched it, and it is idle. -/
def leaderParks (leader : Replica) (matched : Bool) : Bool :=
  !leader.following && leader.applied == leader.log.length && matched && leader.idle

/-- Raft's log matching between two replicas of one stream: equal log ids
    imply equal prefixes. Trusted from the Raft core. -/
def LogMatching (a b : Log) : Prop :=
  ∀ index, index ≤ a.length → index ≤ b.length → termAt a index = termAt b index →
    a.take index = b.take index

theorem accept_requires_exact_log {replica leader : Replica} {vote : Vote}
    (matching : LogMatching replica.log leader.log)
    (accepted : acceptsPark replica vote leader.applied (termAt leader.log leader.applied) = true)
    (applied : leader.applied ≤ leader.log.length) :
    replica.log = leader.log.take leader.applied := by
  simp only [acceptsPark, Bool.and_eq_true, beq_iff_eq] at accepted
  obtain ⟨⟨⟨⟨⟨_, _⟩, sameApplied⟩, sameTerm⟩, sameLength⟩, _⟩ := accepted
  have length : replica.log.length = leader.applied := sameLength
  rw [sameApplied] at sameTerm
  have prefixes := matching leader.applied (by omega) applied sameTerm
  rw [List.take_of_length_le (by omega)] at prefixes
  exact prefixes

theorem accept_requires_the_leaders_vote {replica : Replica} {vote : Vote} {index : Nat}
    {term : Option Nat} (accepted : acceptsPark replica vote index term = true) :
    replica.vote = vote ∧ replica.following = true := by
  simp only [acceptsPark, Bool.and_eq_true, beq_iff_eq] at accepted
  exact ⟨accepted.1.1.1.1.2, accepted.1.1.1.1.1⟩

/-- Every committed entry is applied on the leader before it parks, so a
    follower that accepted holds the committed log. -/
theorem accepted_followers_hold_the_committed_log {replica leader : Replica} {vote : Vote}
    {committed : Log} (matching : LogMatching replica.log leader.log)
    (accepted : acceptsPark replica vote leader.applied (termAt leader.log leader.applied) = true)
    (applied : leader.applied ≤ leader.log.length)
    (committedApplied : committed <+: leader.log.take leader.applied) :
    committed <+: replica.log := by
  rw [accept_requires_exact_log matching accepted applied]
  exact committedApplied

theorem leader_parks_only_settled {leader : Replica} {matched : Bool}
    (parks : leaderParks leader matched = true) :
    leader.following = false ∧ leader.applied = leader.log.length ∧ matched = true := by
  simp only [leaderParks, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at parks
  exact ⟨parks.1.1.1, parks.1.1.2, parks.1.2⟩

abbrev World := KeeperId → Replica

def World.set (w : World) (keeper : KeeperId) (replica : Replica) : World :=
  fun other => if other = keeper then replica else w other

/-- How a parked replica answers a peer request (`decisions::parked_answer`). -/
inductive Request where
  | heartbeat
  | park
  | work
  deriving DecidableEq

inductive Answer where
  | busy
  | parked
  | reopen
  deriving DecidableEq

def parkedAnswer (request : Request) (parkedFor window : Nat) : Answer :=
  match request with
  | .heartbeat => if parkedFor < window then .busy else .reopen
  | .park => .parked
  | .work => .reopen

theorem parked_answers_preserve_state (parkedFor window : Nat) :
    (parkedFor < window → parkedAnswer .heartbeat parkedFor window = .busy) ∧
      parkedAnswer .park parkedFor window = .parked ∧ parkedAnswer .work parkedFor window = .reopen := by
  refine ⟨fun early => ?_, rfl, rfl⟩
  simp [parkedAnswer, early]

/-- The keeper-layer steps parking adds. Raft steps run only on open groups
    and are the Raft core's own. -/
inductive Step : World → World → Prop
  /-- A follower accepts the leader's park request and closes its group. -/
  | accept (w : World) (keeper : KeeperId) (vote : Vote) (index : Nat) (term : Option Nat) :
      acceptsPark (w keeper) vote index term = true →
      Step w (w.set keeper { w keeper with parked := true })
  /-- The leader parks once every live follower accepted. -/
  | park (w : World) (leader : KeeperId) (matched : Bool) :
      leaderParks (w leader) matched = true →
      Step w (w.set leader { w leader with parked := true })
  /-- A parked replica answers a request without opening its group. -/
  | answer (w : World) (keeper : KeeperId) (request : Request) (parkedFor window : Nat) :
      (w keeper).parked = true → parkedAnswer request parkedFor window ≠ .reopen → Step w w
  /-- A request, a client or the wake sweep reopens the group from its
      retained state. -/
  | reopen (w : World) (keeper : KeeperId) :
      Step w (w.set keeper { w keeper with parked := false })

inductive Trace : World → World → Prop
  | refl (w : World) : Trace w w
  | step {w v u : World} : Step w v → Trace v u → Trace w u

theorem step_preserves_durable_state {w v : World} (step : Step w v) (keeper : KeeperId) :
    (v keeper).durable = (w keeper).durable := by
  cases step with
  | accept changed => by_cases same : keeper = changed <;> simp [World.set, same, Replica.durable]
  | park changed => by_cases same : keeper = changed <;> simp [World.set, same, Replica.durable]
  | answer => rfl
  | reopen changed => by_cases same : keeper = changed <;> simp [World.set, same, Replica.durable]

theorem parking_preserves_durable_state {w v : World} (trace : Trace w v) (keeper : KeeperId) :
    (v keeper).durable = (w keeper).durable := by
  induction trace with
  | refl => rfl
  | step step _ next => exact (next).trans (step_preserves_durable_state step keeper)

/-- A log a quorum of the configuration holds stays held by that quorum
    across any interleaving of parks, busy answers and reopens. -/
theorem parking_preserves_the_committed_log {w v : World} (trace : Trace w v)
    (members : List KeeperId) (committed : Log)
    (held : Majority members (fun keeper => decide (committed <+: (w keeper).log))) :
    Majority members (fun keeper => decide (committed <+: (v keeper).log)) := by
  have same : ∀ keeper, (v keeper).log = (w keeper).log := fun keeper =>
    congrArg (fun durable => durable.2.1) (parking_preserves_durable_state trace keeper)
  simp only [same]
  exact held

#print axioms accept_requires_exact_log
#print axioms accept_requires_the_leaders_vote
#print axioms accepted_followers_hold_the_committed_log
#print axioms leader_parks_only_settled
#print axioms parked_answers_preserve_state
#print axioms parking_preserves_durable_state
#print axioms parking_preserves_the_committed_log

end Logkeeper.ConsensusAdditions.Parking
