import Logkeeper.JournalRefinement

/-!
Operator recovery after losing two of three voters (design section R).

The survivor `s` of the configuration `[s, a, b]` writes, in one durable
round, a committed vote and the recovery entries at the term
`T' = max (vote term, log term) + 2^32`, and the recovered membership names
`s` and two replacements. The lost voters `a` and `b` keep the old
configuration and whatever suffix the survivor never saw.

The model keeps each keeper's term, log and whether it runs. Lost voters
campaign, append and replicate among themselves; recovered members do the
same among themselves; a lost voter that contacts the survivor is refused
without an answer by `decisions::excludes_sender`. Raft's leader completeness
for the recovered group (a leader of the recovered membership holds the
committed recovery entries) is a step guard, not a theorem here.

`recovered_replicas_never_mix` and `lost_replicas_stay_below_the_recovery_term`
hold for every replica on every trace. `barrier_reads_never_mix` shows that a
read or commit confirmed by a quorum of the serving replica's configuration
never observes the lost suffix while at most one lost voter runs. The two
residual risks are witnesses: `two_returning_voters_serve_the_lost_suffix`
(both lost voters return together and form the old quorum) and
`unconfirmed_local_read_serves_the_lost_suffix` (a single returning voter
answers a read from its own applied state without a barrier, which the TLA+
model found as CE-3).

The `contact` step refuses every message a lost voter sends the survivor.
So does the shipped keeper: every peer frame that carries the sender's
vote, including snapshot chunks, leadership hand-offs and parks, goes
through `excludes_sender` (the test
`the_survivor_refuses_a_lost_voters_snapshot_without_its_term`). Snapshot
chunks used to be answered with the survivor's vote, at the recovery term.
-/

namespace Logkeeper.ConsensusAdditions.RecoveryFence

open JournalRefinement (Majority)

set_option warningAsError true

abbrev KeeperId := Nat

structure Entry where
  term : Nat
  payload : Nat
  deriving DecidableEq, Repr

abbrev Log := List Entry

/-- `decisions::RECOVERY_TERM_GAP`. -/
def gap : Nat := 2 ^ 32

/-- `decisions::recovery_term`. -/
def recoveryTerm (voteTerm logTerm : Nat) : Nat := max voteTerm logTerm + gap

/-- `decisions::excludes_sender`: a configured replica refuses, without a Raft
    answer, a sender outside its membership whose term is below its own. -/
def excludes (configured known : Bool) (senderTerm ownTerm : Nat) : Bool :=
  configured && !known && decide (senderTerm < ownTerm)

/-- The recovery term is above every term the survivor saw, and above the
    term of a lost voter that ran fewer than `2^32` elections the survivor
    never saw. -/
theorem recovery_term_outranks {voteTerm logTerm lostTerm missed : Nat}
    (seen : lostTerm ≤ max voteTerm logTerm + missed) (budget : missed < gap) :
    voteTerm < recoveryTerm voteTerm logTerm ∧ logTerm < recoveryTerm voteTerm logTerm ∧
      lostTerm < recoveryTerm voteTerm logTerm := by
  unfold recoveryTerm gap at *
  omega

/-- The keepers of one recovery. `history` is the survivor's log through the
    recovery entries, and `term` is `T'`. -/
structure Setup where
  survivor : KeeperId
  lostA : KeeperId
  lostB : KeeperId
  recovered : List KeeperId
  term : Nat
  history : Log
  survivorRecovered : survivor ∈ recovered
  lostAOutside : lostA ∉ recovered
  lostBOutside : lostB ∉ recovered

def Setup.old (s : Setup) : List KeeperId := [s.survivor, s.lostA, s.lostB]

def Setup.Lost (s : Setup) (keeper : KeeperId) : Prop := keeper = s.lostA ∨ keeper = s.lostB

/-- The membership a replica holds: lost voters never learn the recovered one. -/
def Setup.membership (s : Setup) (keeper : KeeperId) : List KeeperId :=
  if keeper ∈ s.recovered then s.recovered else s.old

structure Replica where
  term : Nat
  log : Log
  online : Bool

abbrev World := KeeperId → Replica

def World.set (w : World) (keeper : KeeperId) (replica : Replica) : World :=
  fun other => if other = keeper then replica else w other

theorem World.set_same (w : World) (keeper : KeeperId) (replica : Replica) :
    w.set keeper replica keeper = replica := by
  simp [World.set]

theorem World.set_other (w : World) {keeper other : KeeperId} (replica : Replica)
    (distinct : other ≠ keeper) : w.set keeper replica other = w other := by
  simp [World.set, distinct]

/-- A log of the recovered world: a prefix of the recovered history, or that
    history followed by entries of the recovery term or later. -/
def NewWorld (s : Setup) (log : Log) : Prop :=
  log <+: s.history ∨ ∃ rest, log = s.history ++ rest ∧ ∀ entry ∈ rest, s.term ≤ entry.term

/-- A lost voter has not learned the recovery term. -/
def OldWorld (s : Setup) (replica : Replica) : Prop :=
  replica.term < s.term ∧ ∀ entry ∈ replica.log, entry.term < s.term

structure Clean (s : Setup) (w : World) : Prop where
  survivorTerm : s.term ≤ (w s.survivor).term
  recoveredLogs : ∀ keeper ∈ s.recovered, NewWorld s (w keeper).log
  lostA : OldWorld s (w s.lostA)
  lostB : OldWorld s (w s.lostB)

inductive Step (s : Setup) : World → World → Prop
  /-- A crash or restart keeps the durable term and log. -/
  | restart (w : World) (keeper : KeeperId) (online : Bool) :
      Step s w (w.set keeper { w keeper with online })
  /-- A lost voter campaigns. The guard is the election budget: lost voters run
      fewer elections than the gap the recovery term left them. -/
  | lostElect (w : World) (keeper : KeeperId) :
      s.Lost keeper → (w keeper).term + 1 < s.term →
      Step s w (w.set keeper { w keeper with term := (w keeper).term + 1 })
  | lostAppend (w : World) (keeper : KeeperId) (payload : Nat) :
      s.Lost keeper →
      Step s w (w.set keeper { w keeper with log := (w keeper).log ++ [⟨(w keeper).term, payload⟩] })
  | lostReplicate (w : World) (leader follower : KeeperId) (kept : Nat) :
      s.Lost leader → s.Lost follower → (w follower).term ≤ (w leader).term →
      Step s w (w.set follower
        { w follower with term := (w leader).term, log := (w leader).log.take kept })
  /-- A lost voter contacts the survivor, the only member of its configuration
      in the recovered membership. Unless the survivor refuses it, Raft's answer
      teaches it the survivor's term. -/
  | contact (w : World) (keeper : KeeperId) :
      s.Lost keeper →
      Step s w (if excludes true (s.recovered.contains keeper) (w keeper).term (w s.survivor).term
        then w
        else w.set keeper { w keeper with term := max (w keeper).term (w s.survivor).term })
  /-- A leader of the recovered membership appends at its term. -/
  | newAppend (w : World) (keeper : KeeperId) (payload : Nat) :
      keeper ∈ s.recovered → s.history <+: (w keeper).log → s.term ≤ (w keeper).term →
      Step s w (w.set keeper { w keeper with log := (w keeper).log ++ [⟨(w keeper).term, payload⟩] })
  | newReplicate (w : World) (leader follower : KeeperId) (kept : Nat) :
      leader ∈ s.recovered → follower ∈ s.recovered →
      Step s w (w.set follower
        { w follower with term := max (w leader).term (w follower).term,
                          log := (w leader).log.take kept })

inductive Trace (s : Setup) : World → World → Prop
  | refl (w : World) : Trace s w w
  | step {w v u : World} : Step s w v → Trace s v u → Trace s w u

private theorem lostA_ne_recovered (s : Setup) {keeper : KeeperId} (member : keeper ∈ s.recovered) :
    keeper ≠ s.lostA := fun same => s.lostAOutside (same ▸ member)

private theorem lostB_ne_recovered (s : Setup) {keeper : KeeperId} (member : keeper ∈ s.recovered) :
    keeper ≠ s.lostB := fun same => s.lostBOutside (same ▸ member)

private theorem lost_not_recovered (s : Setup) {keeper : KeeperId} (lost : s.Lost keeper) :
    keeper ∉ s.recovered := by
  rcases lost with same | same <;> subst same
  · exact s.lostAOutside
  · exact s.lostBOutside

private theorem lost_ne_survivor (s : Setup) {keeper : KeeperId} (lost : s.Lost keeper) :
    keeper ≠ s.survivor := fun same =>
  lost_not_recovered s lost (same ▸ s.survivorRecovered)

theorem newWorld_take {s : Setup} {log : Log} (clean : NewWorld s log) (kept : Nat) :
    NewWorld s (log.take kept) := by
  rcases clean with short | ⟨rest, rfl, later⟩
  · exact Or.inl ((List.take_prefix kept log).trans short)
  · rw [List.take_append]
    by_cases short : kept ≤ s.history.length
    · left
      have : kept - s.history.length = 0 := by omega
      rw [this, List.take_zero, List.append_nil]
      exact List.take_prefix kept s.history
    · right
      refine ⟨rest.take (kept - s.history.length), ?_, ?_⟩
      · rw [List.take_of_length_le (by omega)]
      · intro entry member
        exact later entry (List.mem_of_mem_take member)

theorem newWorld_append {s : Setup} {log : Log} (clean : NewWorld s log)
    (complete : s.history <+: log) {entry : Entry} (current : s.term ≤ entry.term) :
    NewWorld s (log ++ [entry]) := by
  obtain ⟨extra, extended⟩ := complete
  right
  refine ⟨extra ++ [entry], by rw [← extended, List.append_assoc], ?_⟩
  have later : ∀ e ∈ extra, s.term ≤ e.term := by
    rcases clean with short | ⟨rest, rfl, later⟩
    · have bound := short.length_le
      rw [← extended, List.length_append] at bound
      have empty : extra = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [empty]
    · rw [List.append_cancel_left extended]
      exact later
  intro e member
  rcases List.mem_append.mp member with old | added
  · exact later e old
  · rw [List.mem_singleton.mp added]
    exact current

theorem oldWorld_take {s : Setup} (replica : Replica) (term : Nat) (below : term < s.term) (log : Log) (kept : Nat)
    (logBelow : ∀ entry ∈ log, entry.term < s.term) :
    OldWorld s { replica with term, log := log.take kept } :=
  ⟨below, fun entry member => logBelow entry (List.mem_of_mem_take member)⟩

private theorem clean_lost {s : Setup} {w : World} (clean : Clean s w) {keeper : KeeperId}
    (lost : s.Lost keeper) : OldWorld s (w keeper) := by
  rcases lost with same | same <;> subst same
  · exact clean.lostA
  · exact clean.lostB

/-- The survivor refuses every lost voter: it is configured, does not know the
    lost voter, and holds a term the lost voter never reached. -/
theorem survivor_excludes_lost_voters {s : Setup} {w : World} (clean : Clean s w)
    {keeper : KeeperId} (lost : s.Lost keeper) :
    excludes true (s.recovered.contains keeper) (w keeper).term (w s.survivor).term = true := by
  have outside : s.recovered.contains keeper = false := by
    cases known : s.recovered.contains keeper
    · rfl
    · exact absurd (List.contains_iff_mem.mp known) (lost_not_recovered s lost)
  have below := (clean_lost clean lost).1
  have survivor := clean.survivorTerm
  unfold excludes
  rw [outside]
  simp only [Bool.true_and, Bool.not_false]
  exact decide_eq_true (by omega)

/-- Updating one lost voter with an old-world replica keeps the world clean. -/
private theorem clean_set_lost {s : Setup} {w : World} (clean : Clean s w) {keeper : KeeperId}
    (lost : s.Lost keeper) {replica : Replica} (old : OldWorld s replica) :
    Clean s (w.set keeper replica) := by
  have survivor := lost_ne_survivor s lost
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [World.set_other _ _ (Ne.symm survivor)]
    exact clean.survivorTerm
  · intro member recovered
    have : member ≠ keeper := fun same => lost_not_recovered s lost (same ▸ recovered)
    rw [World.set_other _ _ this]
    exact clean.recoveredLogs member recovered
  · by_cases same : s.lostA = keeper
    · subst same
      rw [World.set_same]
      exact old
    · rw [World.set_other _ _ same]
      exact clean.lostA
  · by_cases same : s.lostB = keeper
    · subst same
      rw [World.set_same]
      exact old
    · rw [World.set_other _ _ same]
      exact clean.lostB

/-- Updating one recovered member with a new-world log, and keeping the
    survivor at or above the recovery term, keeps the world clean. -/
private theorem clean_set_recovered {s : Setup} {w : World} (clean : Clean s w)
    {keeper : KeeperId} (recovered : keeper ∈ s.recovered) {replica : Replica}
    (log : NewWorld s replica.log) (term : keeper = s.survivor → s.term ≤ replica.term) :
    Clean s (w.set keeper replica) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases same : s.survivor = keeper
    · subst same
      rw [World.set_same]
      exact term rfl
    · rw [World.set_other _ _ same]
      exact clean.survivorTerm
  · intro member _
    by_cases same : member = keeper
    · subst same
      rw [World.set_same]
      exact log
    · rw [World.set_other _ _ same]
      exact clean.recoveredLogs member ‹_›
  · rw [World.set_other _ _ (Ne.symm (lostA_ne_recovered s recovered))]
    exact clean.lostA
  · rw [World.set_other _ _ (Ne.symm (lostB_ne_recovered s recovered))]
    exact clean.lostB

theorem step_preserves_clean {s : Setup} {w v : World} (clean : Clean s w) (step : Step s w v) :
    Clean s v := by
  cases step with
  | restart keeper online =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · by_cases same : s.survivor = keeper
        · subst same
          rw [World.set_same]
          exact clean.survivorTerm
        · rw [World.set_other _ _ same]
          exact clean.survivorTerm
      · intro member recovered
        by_cases same : member = keeper
        · subst same
          rw [World.set_same]
          exact clean.recoveredLogs member recovered
        · rw [World.set_other _ _ same]
          exact clean.recoveredLogs member recovered
      · by_cases same : s.lostA = keeper
        · subst same
          rw [World.set_same]
          exact clean.lostA
        · rw [World.set_other _ _ same]
          exact clean.lostA
      · by_cases same : s.lostB = keeper
        · subst same
          rw [World.set_same]
          exact clean.lostB
        · rw [World.set_other _ _ same]
          exact clean.lostB
  | lostElect keeper lost budget =>
      have old := clean_lost clean lost
      exact clean_set_lost clean lost ⟨by simp only; omega, old.2⟩
  | lostAppend keeper payload lost =>
      have old := clean_lost clean lost
      refine clean_set_lost clean lost ⟨old.1, fun entry member => ?_⟩
      rcases List.mem_append.mp member with prior | added
      · exact old.2 entry prior
      · rw [List.mem_singleton.mp added]
        exact old.1
  | lostReplicate leader follower kept leaderLost followerLost _ =>
      have old := clean_lost clean leaderLost
      exact clean_set_lost clean followerLost
        (oldWorld_take (w follower) _ old.1 _ kept old.2)
  | contact keeper lost =>
      rw [survivor_excludes_lost_voters clean lost]
      exact clean
  | newAppend keeper payload recovered complete current =>
      exact clean_set_recovered clean recovered
        (newWorld_append (clean.recoveredLogs keeper recovered) complete current)
        (fun same => by subst same; exact clean.survivorTerm)
  | newReplicate leader follower kept leaderRecovered followerRecovered =>
      refine clean_set_recovered clean followerRecovered
        (newWorld_take (clean.recoveredLogs leader leaderRecovered) kept) ?_
      intro same
      subst same
      have := clean.survivorTerm
      simp only
      omega

theorem trace_preserves_clean {s : Setup} {w v : World} (clean : Clean s w) (trace : Trace s w v) :
    Clean s v := by
  induction trace with
  | refl => exact clean
  | step step _ next => exact next (step_preserves_clean clean step)

/-- An observation at index `index` belongs to the recovered history: it is
    the recovered history's entry there, or a later entry of the recovery
    term or above. -/
def Recovered (s : Setup) (index : Nat) (entry : Entry) : Prop :=
  s.history[index]? = some entry ∨ (s.history.length ≤ index ∧ s.term ≤ entry.term)

/-- An entry of the lost suffix: from a lost voter's history, unknown to the
    recovered history at its index. It is never a recovered observation. -/
theorem lost_suffix_is_not_recovered {s : Setup} {index : Nat} {entry : Entry}
    (old : entry.term < s.term) (unknown : s.history[index]? ≠ some entry) :
    ¬ Recovered s index entry := by
  rintro (same | ⟨_, later⟩)
  · exact unknown same
  · omega

theorem newWorld_recovered {s : Setup} {log : Log} (clean : NewWorld s log) {index : Nat}
    {entry : Entry} (found : log[index]? = some entry) : Recovered s index entry := by
  have within : index < log.length := (List.getElem?_eq_some_iff.mp found).1
  rcases clean with ⟨extra, extended⟩ | ⟨rest, rfl, later⟩
  · left
    rw [← extended, List.getElem?_append_left within]
    exact found
  · by_cases early : index < s.history.length
    · left
      rw [List.getElem?_append_left early] at found
      exact found
    · right
      rw [List.getElem?_append_right (by omega)] at found
      exact ⟨by omega, later entry (List.mem_of_getElem? found)⟩

/-- No replica of the recovered membership ever holds a lost-suffix entry. -/
theorem recovered_replicas_never_mix {s : Setup} {w v : World} (start : Clean s w)
    (trace : Trace s w v) {keeper : KeeperId} (member : keeper ∈ s.recovered) {index : Nat}
    {entry : Entry} (found : (v keeper).log[index]? = some entry) : Recovered s index entry :=
  newWorld_recovered ((trace_preserves_clean start trace).recoveredLogs keeper member) found

/-- A lost voter never learns the recovery term and never holds an entry of it,
    because the survivor refuses it without an answer. -/
theorem lost_replicas_stay_below_the_recovery_term {s : Setup} {w v : World} (start : Clean s w)
    (trace : Trace s w v) {keeper : KeeperId} (lost : s.Lost keeper) :
    (v keeper).term < s.term ∧ ∀ entry ∈ (v keeper).log, entry.term < s.term :=
  clean_lost (trace_preserves_clean start trace) lost

/-- A keeper confirms a read barrier or acknowledges an append for `serving`
    when it runs and its term is no newer, under Raft's term rule. -/
def confirms (w : World) (serving keeper : KeeperId) : Bool :=
  (w keeper).online && (keeper == serving || decide ((w keeper).term ≤ (w serving).term))

/-- A lost voter cannot gather a quorum of its configuration while the other
    lost voter is down: the survivor's term is newer than its own. So it can
    neither commit nor pass a read barrier. -/
theorem one_lost_voter_has_no_quorum {s : Setup} {w : World} (clean : Clean s w)
    {serving : KeeperId} (lost : s.Lost serving)
    (alone : (w s.lostA).online = false ∨ (w s.lostB).online = false) :
    ¬ Majority s.old (confirms w serving) := by
  have survivorRefuses : confirms w serving s.survivor = false := by
    have below := (clean_lost clean lost).1
    have survivor := clean.survivorTerm
    have other : (s.survivor == serving) = false :=
      beq_false_of_ne (Ne.symm (lost_ne_survivor s lost))
    simp only [confirms, other, Bool.false_or]
    cases (w s.survivor).online <;> simp <;> omega
  intro quorum
  unfold Majority Setup.old at quorum
  simp only [List.length_cons, List.length_nil, List.countP_cons, List.countP_nil,
    survivorRefuses, Bool.false_eq_true, ↓reduceIte] at quorum
  rcases lost with same | same <;> subst same <;> rcases alone with down | down
  · have : confirms w s.lostA s.lostA = false := by simp [confirms, down]
    simp only [this, Bool.false_eq_true, ↓reduceIte] at quorum
    split at quorum <;> omega
  · have : confirms w s.lostA s.lostB = false := by simp [confirms, down]
    simp only [this, Bool.false_eq_true, ↓reduceIte] at quorum
    split at quorum <;> omega
  · have : confirms w s.lostB s.lostA = false := by simp [confirms, down]
    simp only [this, Bool.false_eq_true, ↓reduceIte] at quorum
    split at quorum <;> omega
  · have : confirms w s.lostB s.lostB = false := by simp [confirms, down]
    simp only [this, Bool.false_eq_true, ↓reduceIte] at quorum
    split at quorum <;> omega

/-- A read served after a barrier: a quorum of the serving replica's
    membership confirmed it, and each observation is an entry of its log. -/
structure BarrierRead (s : Setup) (w : World) (serving : KeeperId)
    (observed : List (Nat × Entry)) : Prop where
  voter : serving ∈ s.recovered ∨ s.Lost serving
  quorum : Majority (s.membership serving) (confirms w serving)
  entries : ∀ seen ∈ observed, (w serving).log[seen.1]? = some seen.2

/-- No mixed history after recovery: while at most one lost voter runs,
    every read confirmed by a quorum, before or after any interleaving of
    lost and recovered work, observes only the recovered history. -/
theorem barrier_reads_never_mix {s : Setup} {w v : World} (start : Clean s w)
    (trace : Trace s w v)
    (alone : (v s.lostA).online = false ∨ (v s.lostB).online = false)
    {serving : KeeperId} {observed : List (Nat × Entry)} (read : BarrierRead s v serving observed) :
    ∀ seen ∈ observed, Recovered s seen.1 seen.2 := by
  have clean := trace_preserves_clean start trace
  rcases read.voter with member | lost
  · intro seen present
    exact newWorld_recovered (clean.recoveredLogs serving member) (read.entries seen present)
  · have quorum := read.quorum
    simp only [Setup.membership, lost_not_recovered s lost, ↓reduceIte] at quorum
    exact absurd quorum (one_lost_voter_has_no_quorum clean lost alone)

/-- The documented residual risk: when both lost voters return with their
    data, they form a quorum of the old configuration and serve the lost
    suffix next to the survivor's recovered history. -/
def returning : Setup where
  survivor := 0
  lostA := 1
  lostB := 2
  recovered := [0, 3, 4]
  term := 10
  history := [⟨1, 1⟩, ⟨10, 0⟩]
  survivorRecovered := by decide
  lostAOutside := by decide
  lostBOutside := by decide

def returningWorld : World := fun keeper =>
  if keeper = 0 then ⟨10, [⟨1, 1⟩, ⟨10, 0⟩], true⟩
  else if keeper = 1 then ⟨2, [⟨1, 1⟩, ⟨2, 7⟩], true⟩
  else if keeper = 2 then ⟨2, [⟨1, 1⟩, ⟨2, 7⟩], true⟩
  else ⟨0, [], false⟩

theorem two_returning_voters_serve_the_lost_suffix :
    Clean returning returningWorld ∧
      BarrierRead returning returningWorld 1 [(1, ⟨2, 7⟩)] ∧
      ¬ Recovered returning 1 ⟨2, 7⟩ := by
  refine ⟨⟨by decide, ?_, ?_, ?_⟩, ⟨Or.inr (Or.inl rfl), by decide, ?_⟩, ?_⟩
  · intro keeper member
    simp only [returning, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> left <;> simp [returningWorld, returning]
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · intro seen present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    subst present
    decide
  · exact lost_suffix_is_not_recovered (by decide) (by decide)

/-- The second residual risk (TLA+ CE-3): one returning lost voter that
    answers a read from its own applied state, without a barrier, serves the
    lost suffix although it can never commit. -/
theorem unconfirmed_local_read_serves_the_lost_suffix :
    let alone : World := returningWorld.set 2 ⟨2, [⟨1, 1⟩, ⟨2, 7⟩], false⟩
    Clean returning alone ∧ ¬ Majority returning.old (confirms alone 1) ∧
      (alone 1).log[1]? = some ⟨2, 7⟩ ∧ ¬ Recovered returning 1 ⟨2, 7⟩ := by
  intro alone
  have clean : Clean returning alone := by
    refine ⟨by decide, ?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
    intro keeper member
    simp only [returning, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [alone, World.set, returningWorld, returning]
  exact ⟨clean, one_lost_voter_has_no_quorum clean (Or.inl rfl) (Or.inr (by decide)),
    by decide, lost_suffix_is_not_recovered (by decide) (by decide)⟩

/-- How the stream state machine decides a seal (`decisions::seal_step`);
    `bound` is `u64::MAX`. -/
inductive SealStep where
  | recovered
  | unavailable
  | install (epoch : Nat)
  | repeat (epoch : Nat)
  deriving DecidableEq, Repr

def sealStep (recovering : Bool) (current expected bound : Nat) : SealStep :=
  if recovering then .recovered
  else if expected = bound then .unavailable
  else if current = expected then .install (expected + 1)
  else .repeat (expected + 1)

/-- While the recovery fence stands every seal is refused with `Recovered`;
    after the acknowledgement, which keeps the fence's epoch, the first seal of
    that epoch installs a newer one, and the pre-recovery writer's seal of its
    older epoch only repeats a fence it no longer holds. -/
theorem fence_refuses_every_seal (current expected bound : Nat) :
    sealStep true current expected bound = .recovered ∧
      (current < bound → sealStep false current current bound = .install (current + 1)) ∧
      (expected ≠ current → expected ≠ bound →
        sealStep false current expected bound = .repeat (expected + 1)) := by
  refine ⟨rfl, fun below => ?_, fun stale room => ?_⟩
  · simp [sealStep, Nat.ne_of_lt below]
  · simp [sealStep, room, Ne.symm stale]

#print axioms recovery_term_outranks
#print axioms fence_refuses_every_seal
#print axioms survivor_excludes_lost_voters
#print axioms step_preserves_clean
#print axioms recovered_replicas_never_mix
#print axioms lost_replicas_stay_below_the_recovery_term
#print axioms one_lost_voter_has_no_quorum
#print axioms barrier_reads_never_mix
#print axioms two_returning_voters_serve_the_lost_suffix
#print axioms unconfirmed_local_read_serves_the_lost_suffix

end Logkeeper.ConsensusAdditions.RecoveryFence
