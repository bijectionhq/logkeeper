namespace Logkeeper.LeaderJournal.RestartRead

set_option warningAsError true

/-!
# Fresh reads after a keeper restart

The Rust keeper does not persist Raft's commit index. OpenRaft 0.9 restores a
keeper as leader at startup when its stored vote is committed and names
itself. A restored leader reuses the no-op it appended earlier in that term,
so its read floor `max noop knownCommit` can fall below writes that were
committed and acknowledged before the restart. A linearizable read would then
miss them.

The keeper's `read_vote` presents its own committed vote as uncommitted. The
stored vote is unchanged. This module checks three facts about that rule.

* The presented vote grants exactly the ballots the stored vote grants.
* Startup never restores leadership from a presented vote.
* Every leader after a restart is therefore elected. An elected leader appends
  its no-op after its whole log, so its read floor covers every acknowledged
  write.

Leader completeness is a premise. A leader elected under Raft's rules holds
every committed entry. The model does not re-prove it. Indices are log
positions, and a read is served once the leader has applied its read floor.
-/

/-- A persisted Raft vote. Keeper IDs are natural numbers. -/
structure Vote where
  term : Nat
  votedFor : Nat
  committed : Bool
  deriving DecidableEq, Repr

/-- The Raft ballot rule. A keeper grants a request for `term` from
    `candidate` when the term is newer, or when it is the same term and the
    same candidate. The committed flag never decides a ballot. -/
def grants (stored : Vote) (term candidate : Nat) : Bool :=
  decide (stored.term < term) || (decide (stored.term = term) && decide (stored.votedFor = candidate))

/-- OpenRaft 0.9 startup restores leadership from a committed self vote. -/
def restoresLeader (presented : Vote) (self : Nat) : Bool :=
  presented.committed && decide (presented.votedFor = self)

/-- The keeper's `read_vote`: its own committed vote is presented as
    uncommitted. Any other vote is presented unchanged. -/
def present (self : Nat) (stored : Vote) : Vote :=
  if stored.committed && decide (stored.votedFor = self) then
    { stored with committed := false }
  else
    stored

theorem present_keeps_term_and_ballot (self : Nat) (stored : Vote) :
    (present self stored).term = stored.term ∧
      (present self stored).votedFor = stored.votedFor := by
  unfold present
  split <;> simp

/-- The presented vote grants and refuses exactly the same requests. In
    particular the keeper still refuses another candidate in its own term. -/
theorem present_grants_the_same_ballots (self : Nat) (stored : Vote) (term candidate : Nat) :
    grants (present self stored) term candidate = grants stored term candidate := by
  obtain ⟨hterm, hfor⟩ := present_keeps_term_and_ballot self stored
  simp [grants, hterm, hfor]

theorem present_refuses_another_candidate_in_its_term
    (self candidate : Nat) (stored : Vote)
    (mine : stored.votedFor = self) (other : candidate ≠ self) :
    grants (present self stored) stored.term candidate = false := by
  rw [present_grants_the_same_ballots]
  simp [grants, mine, Ne.symm other]

theorem present_never_restores_leadership (self : Nat) (stored : Vote) :
    restoresLeader (present self stored) self = false := by
  unfold present restoresLeader
  split
  · simp
  · rename_i h
    simpa using h

/-- How a leader came to lead after a restart. -/
inductive Leadership where
  /-- Restored at startup in the stored term. Its no-op is the first entry it
      appended in that term before the restart. -/
  | restored (oldNoop : Nat)
  /-- Elected in a newer term while holding `last` log entries. Its no-op is
      appended at `last + 1`. -/
  | elected (last : Nat)
  deriving DecidableEq, Repr

def Leadership.noop : Leadership → Nat
  | .restored oldNoop => oldNoop
  | .elected last => last + 1

/-- OpenRaft's read floor: the larger of the leader's no-op and the commit
    index it knows. After a restart without a persisted commit index, the
    known commit can be as low as the restored snapshot. -/
def readFloor (leadership : Leadership) (knownCommit : Nat) : Nat :=
  max leadership.noop knownCommit

/-- The defect. A leader restored in its term with a no-op at 1, a snapshot at
    4 and an acknowledged write at 10 reads at floor 4. -/
theorem restored_leader_can_read_below_an_acknowledged_write :
    ∃ oldNoop knownCommit acknowledged,
      oldNoop ≤ acknowledged ∧ knownCommit ≤ acknowledged ∧
        readFloor (.restored oldNoop) knownCommit < acknowledged :=
  ⟨1, 4, 10, by decide, by decide, by decide⟩

/-- An elected leader's read floor covers every write its log holds. With
    leader completeness that includes every acknowledged write. -/
theorem elected_read_floor_covers_acknowledged
    (last knownCommit acknowledged : Nat)
    (complete : acknowledged ≤ last) :
    acknowledged < readFloor (.elected last) knownCommit := by
  show acknowledged < max (last + 1) knownCommit
  omega

/-- The restart rule end to end. Leadership after a restart is either
    restored, which startup allows only from a committed self vote, or
    elected. Under `present`, restoration never happens. Every leader is
    therefore elected, and with leader completeness its fresh reads include
    every write acknowledged before the restart. -/
theorem fresh_read_after_restart_includes_acknowledged
    (self : Nat) (stored : Vote) (leadership : Leadership)
    (knownCommit acknowledged : Nat)
    (origin : ∀ oldNoop, leadership = .restored oldNoop →
      restoresLeader (present self stored) self = true)
    (complete : ∀ last, leadership = .elected last → acknowledged ≤ last) :
    acknowledged < readFloor leadership knownCommit := by
  cases leadership with
  | restored oldNoop =>
    have := origin oldNoop rfl
    rw [present_never_restores_leadership] at this
    contradiction
  | elected last =>
    exact elected_read_floor_covers_acknowledged last knownCommit acknowledged (complete last rfl)

#print axioms present_grants_the_same_ballots
#print axioms present_refuses_another_candidate_in_its_term
#print axioms present_never_restores_leadership
#print axioms restored_leader_can_read_below_an_acknowledged_write
#print axioms elected_read_floor_covers_acknowledged
#print axioms fresh_read_after_restart_includes_acknowledged

end Logkeeper.LeaderJournal.RestartRead
