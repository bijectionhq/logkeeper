/-!
Operator recovery under the endgame's epoch leases (design section "Endgame: a
configuration authority with epoch leases", approved 2026-11-27).

`RecoveryFence` proves that no reader mixes histories after a recovery under
two assumptions: the lost voters ran fewer than `2^32` elections the survivor
never saw, and for barrier reads, at most one lost voter runs. This module
drops both. Both lost voters keep running, at any term, and nothing trusts
the operator: whatever `--lost` names, the recovery's catalog transaction
adds the stream to the `fenced_streams` of every old voter outside the new
membership. What it assumes instead is the lease model:

* every keeper's monotonic clock drifts from real time by at most `D` over
  any interval no longer than the horizon `H` (`Clock`; `rate_bounds_error`
  derives this from a clock-rate bound `ρ = p / q` with `p * H ≤ q * D`);
* a keeper campaigns, leads, appends, replicates or serves a read only while
  it holds a lease the catalog did not fence, measured on its own clock from
  the grant, for less than `L - M`;
* every member of the recovered membership waits `L + M` on its own clock
  from when it learned of the recovery commit, which is after the commit,
  before it does any of those;
* `D ≤ M` and `L + M + D ≤ H`.

`lease_precedes_wait` turns that into `Gates.Separated`: every gated action of
a lost voter happens strictly before every gated action of a recovered
member. `no_mixed_history` then shows, for every interleaving of lost and
recovered work, including a lost leader at a term above the recovery term
overwriting the survivor before the wait-out ends, that no read observes a
history the recovery did not keep after a read of the recovered history.

Negative controls: `no_wait_out_mixes` (a recovered member that serves without
the wait-out lets a reader mix histories), `drift_beyond_margin_overlaps`
(`M < D` lets a lost voter's lease outlast the wait-out), and
`named_only_fence_leaks` (fencing only the keepers `--lost` names lets an
unnamed lost voter renew after the commit).
-/

namespace Logkeeper.ConsensusAdditions.EpochLease

set_option warningAsError true

abbrev KeeperId := Nat

/-! ## Clocks and leases -/

/-- A keeper's monotonic clock: over any interval of real time no longer
    than `H` it gains or loses at most `D`. -/
structure Clock (D H : Nat) where
  read : Nat → Nat
  monotone : ∀ {t u : Nat}, t ≤ u → read t ≤ read u
  slow : ∀ {t u : Nat}, t ≤ u → u ≤ t + H → u - t ≤ read u - read t + D
  fast : ∀ {t u : Nat}, t ≤ u → u ≤ t + H → read u - read t ≤ u - t + D

/-- A clock-rate bound `ρ = p / q` (`(1 - ρ) Δ ≤ local ≤ (1 + ρ) Δ`) gives
    the `Clock` error bound over intervals up to `H` when `ρ H ≤ D`. -/
theorem rate_bounds_error {p q D H elapsed measured : Nat} (positive : 0 < q)
    (slowRate : (q - p) * elapsed ≤ q * measured)
    (fastRate : q * measured ≤ (q + p) * elapsed)
    (short : elapsed ≤ H) (horizon : p * H ≤ q * D) :
    elapsed ≤ measured + D ∧ measured ≤ elapsed + D := by
  have within : p * elapsed ≤ p * H := Nat.mul_le_mul_left p short
  have lower : q * elapsed ≤ q * (measured + D) := by
    rw [Nat.sub_mul] at slowRate
    rw [Nat.mul_add]
    have : p * elapsed ≤ q * elapsed ∨ q * elapsed < p * elapsed := by omega
    rcases this with _ | _ <;> omega
  have upper : q * measured ≤ q * (elapsed + D) := by
    rw [Nat.add_mul] at fastRate
    rw [Nat.mul_add]
    omega
  exact ⟨Nat.le_of_mul_le_mul_left lower positive, Nat.le_of_mul_le_mul_left upper positive⟩

/-- The holder of a lease granted at `grant` treats it as valid at `t` while
    its clock measured less than `L - M` since the grant. -/
def Holds {D H : Nat} (clock : Clock D H) (L M grant t : Nat) : Prop :=
  grant ≤ t ∧ clock.read t - clock.read grant + M < L

/-- A recovered member that learned of the recovery at `learned` serves at
    `u` once its clock measured `L + M` since. -/
def Waited {D H : Nat} (clock : Clock D H) (L M learned u : Nat) : Prop :=
  learned ≤ u ∧ L + M ≤ clock.read u - clock.read learned

/-- A holder's lease ends, in real time, before `L - M + D` from its grant. -/
theorem holds_window {D H L M grant t : Nat} {clock : Clock D H}
    (horizon : L + M + D ≤ H) (valid : Holds clock L M grant t) :
    t - grant + M < L + D := by
  obtain ⟨after, measured⟩ := valid
  by_cases short : t ≤ grant + H
  · have := clock.slow after short
    omega
  · have late := clock.slow (Nat.le_add_right grant H) (Nat.le_refl _)
    have more := clock.monotone (show grant + H ≤ t by omega)
    omega

/-- A waiter serves no earlier, in real time, than `L + M - D` after it
    learned of the recovery. -/
theorem waited_window {D H L M learned u : Nat} {clock : Clock D H}
    (horizon : L + M + D ≤ H) (waited : Waited clock L M learned u) :
    L + M ≤ u - learned + D := by
  obtain ⟨after, measured⟩ := waited
  by_cases short : u ≤ learned + H
  · have := clock.fast after short
    omega
  · omega

/-- The lease theorem: with `D ≤ M`, a lease granted no later than the
    recovery commit ends before a member that learned of the commit no
    earlier than the commit finishes its wait-out. -/
theorem lease_precedes_wait {D H L M commit grant learned t u : Nat}
    {holder waiter : Clock D H} (margin : D ≤ M) (horizon : L + M + D ≤ H)
    (granted : grant ≤ commit) (learnt : commit ≤ learned)
    (valid : Holds holder L M grant t) (waited : Waited waiter L M learned u) : t < u := by
  have lease := holds_window horizon valid
  have wait := waited_window horizon waited
  have := valid.1
  have := waited.1
  omega -- the lease ends before the wait-out

/-! ## The recovery's catalog transaction -/

/-- The keepers of one recovery: the survivor `s` of `[s, a, b]`, the lost
    voters `a` and `b`, and the recovered membership. `history` is the
    survivor's log through the recovery entries, `rec` is the recovery entry
    (`Command::Recover`, written only by the recovery round), and `term` is
    the recovery term, which needs no gap here. -/
structure Setup where
  survivor : KeeperId
  lostA : KeeperId
  lostB : KeeperId
  recovered : List KeeperId
  term : Nat
  history : List (Nat × Nat)
  recovery : Nat × Nat
  recInHistory : recovery ∈ history
  survivorRecovered : survivor ∈ recovered
  lostAOutside : lostA ∉ recovered
  lostBOutside : lostB ∉ recovered

def Setup.Lost (s : Setup) (keeper : KeeperId) : Prop := keeper = s.lostA ∨ keeper = s.lostB

/-- Which keepers the commit adds the stream's `fenced_streams` to. `allOld`
    fences every old voter outside the new membership whatever `--lost`
    names; `namedOnly` is the spec's wording, where `--lost` narrows the
    fence to the keepers it names. -/
inductive FenceRule where
  | allOld
  | namedOnly

def fences (rule : FenceRule) (s : Setup) (named : List KeeperId) (keeper : KeeperId) : Prop :=
  match rule with
  | .allOld => s.Lost keeper
  | .namedOnly => if named = [] then s.Lost keeper else keeper ∈ named

/-- The recovery's lease world: the keepers' clocks, the commit time, and
    when each recovered member learned of the commit. A grant made after the
    commit to a fenced keeper carries the fence and gates nothing. -/
structure LeaseWorld (D H : Nat) where
  L : Nat
  M : Nat
  commit : Nat
  clock : KeeperId → Clock D H
  learned : KeeperId → Nat
  learnedAfter : ∀ keeper, commit ≤ learned keeper

/-- What gates a step: a lost voter acts under an unfenced lease, a
    recovered member after its wait-out. -/
structure Gates where
  lostActs : KeeperId → Nat → Prop
  newActs : KeeperId → Nat → Prop

def Gates.Separated (g : Gates) : Prop :=
  ∀ lost member t u, g.lostActs lost t → g.newActs member u → t < u

def LeaseWorld.gates {D H : Nat} (w : LeaseWorld D H) (rule : FenceRule) (s : Setup)
    (named : List KeeperId) : Gates where
  lostActs keeper t := ∃ grant, ¬ (fences rule s named keeper ∧ w.commit < grant) ∧
    Holds (w.clock keeper) w.L w.M grant t
  newActs keeper u := Waited (w.clock keeper) w.L w.M (w.learned keeper) u

/-- With every lost voter fenced, which `allOld` does whatever `--lost` says,
    every lost voter's gated action precedes every recovered member's. -/
theorem LeaseWorld.separated {D H : Nat} (w : LeaseWorld D H) (s : Setup)
    (named : List KeeperId) (margin : D ≤ w.M) (horizon : w.L + w.M + D ≤ H) :
    ∀ lost member t u, s.Lost lost → (w.gates .allOld s named).lostActs lost t →
      (w.gates .allOld s named).newActs member u → t < u := by
  intro lost member t u isLost ⟨grant, unfenced, valid⟩ waited
  have granted : grant ≤ w.commit :=
    Nat.le_of_not_lt (fun later => unfenced ⟨isLost, later⟩)
  exact lease_precedes_wait (by omega) horizon granted (w.learnedAfter member) valid waited

/-! ## Histories -/

abbrev Entry := Nat × Nat
abbrev Log := List Entry

structure Replica where
  term : Nat
  log : Log
  online : Bool

abbrev World := KeeperId → Replica

def World.set (w : World) (keeper : KeeperId) (replica : Replica) : World :=
  fun other => if other = keeper then replica else w other

/-- A log of the recovered world: comparable with the recovered history. -/
def NewWorld (s : Setup) (log : Log) : Prop := log <+: s.history ∨ s.history <+: log

instance (s : Setup) (log : Log) : Decidable (NewWorld s log) := by
  unfold NewWorld; infer_instance

/-- A read of a history the recovery did not keep. -/
def Conflicts (s : Setup) (log : Log) : Prop := ¬ NewWorld s log

instance (s : Setup) (log : Log) : Decidable (Conflicts s log) := by
  unfold Conflicts; infer_instance

/-- The ghost state: real time, the world, the first gated action of a
    recovered member, whether a reader saw the recovered history, and
    whether a reader then saw a history the recovery did not keep. -/
structure State where
  time : Nat
  world : World
  served : Option (KeeperId × Nat)
  seenNew : Bool
  mixed : Bool

/-- Replace one keeper's replica. -/
def State.put (st : State) (keeper : KeeperId) (replica : Replica) : State :=
  { st with world := st.world.set keeper replica }

/-- Record the first gated action of a recovered member. -/
def State.serve (st : State) (keeper : KeeperId) : State :=
  { st with served := match st.served with
                      | some first => some first
                      | none => some (keeper, st.time) }


def observe (s : Setup) (st : State) (obs : Log) : State :=
  { st with
    seenNew := st.seenNew || decide (s.history <+: obs)
    mixed := st.mixed || (st.seenNew && decide (Conflicts s obs)) }

/-- `decisions::excludes_sender`. The proof never relies on it. -/
def excludes (configured known : Bool) (senderTerm ownTerm : Nat) : Bool :=
  configured && !known && decide (senderTerm < ownTerm)

inductive Step (s : Setup) (g : Gates) : State → State → Prop
  | tick (st : State) : Step s g st { st with time := st.time + 1 }
  | restart (st : State) (keeper : KeeperId) (online : Bool) :
      Step s g st (st.put keeper { st.world keeper with online := online })
  /-- A lost voter campaigns, at any term: there is no election budget. -/
  | lostElect (st : State) (keeper : KeeperId) :
      s.Lost keeper → g.lostActs keeper st.time →
      Step s g st (st.put keeper
        { st.world keeper with term := (st.world keeper).term + 1 })
  | lostAppend (st : State) (keeper : KeeperId) (entry : Entry) :
      s.Lost keeper → g.lostActs keeper st.time → entry ≠ s.recovery →
      Step s g st (st.put keeper
        { st.world keeper with log := (st.world keeper).log ++ [entry] })
  | lostReplicate (st : State) (leader follower : KeeperId) (kept : Nat) :
      s.Lost leader → s.Lost follower → g.lostActs leader st.time →
      Step s g st (st.put follower
        { st.world follower with term := (st.world leader).term,
                                 log := (st.world leader).log.take kept })
  | lostRead (st : State) (keeper : KeeperId) (kept : Nat) :
      s.Lost keeper → g.lostActs keeper st.time →
      Step s g st (observe s st ((st.world keeper).log.take kept))
  /-- A lost leader whose term the survivor does not exclude overwrites the
      survivor's log, recovery entries included. -/
  | contactRevert (st : State) (keeper : KeeperId) :
      s.Lost keeper → g.lostActs keeper st.time →
      excludes true false (st.world keeper).term (st.world s.survivor).term = false →
      (st.world s.survivor).term < (st.world keeper).term →
      Step s g st (st.put s.survivor
        { st.world s.survivor with term := (st.world keeper).term, log := (st.world keeper).log })
  /-- The survivor grants a lost candidate's vote: it learns its term. -/
  | contactVote (st : State) (keeper : KeeperId) :
      s.Lost keeper → g.lostActs keeper st.time →
      Step s g st (st.put s.survivor
        { st.world s.survivor with
          term := max (st.world s.survivor).term (st.world keeper).term })
  /-- A leader of the recovered membership appends at its term; it holds the
      recovered history (Raft's leader completeness, a guard here). -/
  | newAppend (st : State) (keeper : KeeperId) (entry : Entry) :
      keeper ∈ s.recovered → g.newActs keeper st.time →
      s.history <+: (st.world keeper).log → entry ≠ s.recovery →
      Step s g st ((st.put keeper
        { st.world keeper with log := (st.world keeper).log ++ [entry] }).serve keeper)
  /-- A survivor whose log a lost leader overwrote leads the old
      configuration and appends to that history. -/
  | oldAppend (st : State) (entry : Entry) :
      g.newActs s.survivor st.time → ¬ NewWorld s (st.world s.survivor).log →
      entry ≠ s.recovery →
      Step s g st ((st.put s.survivor
        { st.world s.survivor with log := (st.world s.survivor).log ++ [entry] }).serve
          s.survivor)
  | newReplicate (st : State) (leader follower : KeeperId) (kept : Nat) :
      leader ∈ s.recovered → follower ∈ s.recovered → g.newActs leader st.time →
      Step s g st ((st.put follower
        { st.world follower with
          term := max (st.world leader).term (st.world follower).term,
          log := (st.world leader).log.take kept }).serve leader)
  | newRead (st : State) (keeper : KeeperId) (kept : Nat) :
      keeper ∈ s.recovered → g.newActs keeper st.time →
      Step s g st ((observe s st ((st.world keeper).log.take kept)).serve keeper)

inductive Trace (s : Setup) (g : Gates) : State → State → Prop
  | refl (st : State) : Trace s g st st
  | step {st mid last : State} : Step s g st mid → Trace s g mid last → Trace s g st last

/-! ## The invariant -/

/-- Every keeper's log. -/
def logs (w : World) : KeeperId → Log := fun keeper => (w keeper).log

def update (ℓ : KeeperId → Log) (key : KeeperId) (log : Log) : KeeperId → Log :=
  fun keeper => if keeper = key then log else ℓ keeper

theorem logs_set (w : World) (key : KeeperId) (replica : Replica) :
    logs (w.set key replica) = update (logs w) key replica.log := by
  funext keeper
  unfold logs update World.set
  split <;> rfl

theorem update_same (ℓ : KeeperId → Log) (key : KeeperId) : update ℓ key (ℓ key) = ℓ := by
  funext keeper
  unfold update
  split
  · next same => rw [same]
  · rfl

/-- Before any recovered member acts: lost logs and, if a lost leader
    overwrote it, the survivor's log never hold the recovery entry, and the
    replacements are still empty. -/
structure Untouched (s : Setup) (ℓ : KeeperId → Log) : Prop where
  lostA : s.recovery ∉ ℓ s.lostA
  lostB : s.recovery ∉ ℓ s.lostB
  survivor : NewWorld s (ℓ s.survivor) ∨ s.recovery ∉ ℓ s.survivor
  fresh : ∀ keeper ∈ s.recovered, keeper ≠ s.survivor → ℓ keeper = []

def AllNew (s : Setup) (ℓ : KeeperId → Log) : Prop :=
  ∀ keeper ∈ s.recovered, NewWorld s (ℓ keeper)

def AllFree (s : Setup) (ℓ : KeeperId → Log) : Prop :=
  ∀ keeper ∈ s.recovered, s.recovery ∉ ℓ keeper

def Before (s : Setup) (st : State) : Prop :=
  Untouched s (logs st.world) ∧ st.seenNew = false ∧ st.mixed = false

/-- After: every recovered member's log is of the recovered world, or none
    holds the recovery entry; a reader saw the recovered history only in the
    first case, and no reader mixed histories. -/
def After (s : Setup) (st : State) : Prop :=
  (AllNew s (logs st.world) ∨ AllFree s (logs st.world)) ∧
    (st.seenNew = true → AllNew s (logs st.world)) ∧ st.mixed = false

def Inv (s : Setup) (g : Gates) (st : State) : Prop :=
  match st.served with
  | none => Before s st
  | some (keeper, u) => g.newActs keeper u ∧ u ≤ st.time ∧ After s st

theorem newWorld_nil (s : Setup) : NewWorld s [] := Or.inl List.nil_prefix

theorem newWorld_take {s : Setup} {log : Log} (clean : NewWorld s log) (kept : Nat) :
    NewWorld s (log.take kept) := by
  rcases clean with short | ⟨rest, rfl⟩
  · exact Or.inl ((List.take_prefix kept log).trans short)
  · rw [List.take_append]
    by_cases early : kept ≤ s.history.length
    · left
      have : kept - s.history.length = 0 := by omega
      rw [this, List.take_zero, List.append_nil]
      exact List.take_prefix kept s.history
    · right
      rw [List.take_of_length_le (by omega)]
      exact List.prefix_append _ _

theorem newWorld_append {s : Setup} {log : Log} (complete : s.history <+: log) (entry : Entry) :
    NewWorld s (log ++ [entry]) :=
  Or.inr (complete.trans (List.prefix_append log [entry]))

theorem recFree_take {s : Setup} {log : Log} (free : s.recovery ∉ log) (kept : Nat) :
    s.recovery ∉ log.take kept := fun found => free (List.mem_of_mem_take found)

theorem recFree_append {s : Setup} {log : Log} (free : s.recovery ∉ log) {entry : Entry}
    (other : entry ≠ s.recovery) : s.recovery ∉ log ++ [entry] := by
  intro found
  rcases List.mem_append.mp found with old | added
  · exact free old
  · exact other (List.mem_singleton.mp added).symm

theorem not_shows_of_recFree {s : Setup} {log : Log} (free : s.recovery ∉ log) :
    ¬ s.history <+: log := fun shown => free (shown.mem s.recInHistory)

theorem lost_ne_recovered {s : Setup} {keeper member : KeeperId} (lost : s.Lost keeper)
    (inside : member ∈ s.recovered) : member ≠ keeper := by
  rintro rfl
  rcases lost with rfl | rfl
  · exact s.lostAOutside inside
  · exact s.lostBOutside inside

theorem lost_ne_survivor {s : Setup} {keeper : KeeperId} (lost : s.Lost keeper) :
    s.survivor ≠ keeper := lost_ne_recovered lost s.survivorRecovered

theorem untouched_lost {s : Setup} {ℓ : KeeperId → Log} (before : Untouched s ℓ)
    {keeper : KeeperId} (lost : s.Lost keeper) : s.recovery ∉ ℓ keeper := by
  rcases lost with rfl | rfl
  · exact before.lostA
  · exact before.lostB

theorem untouched_update {s : Setup} {ℓ : KeeperId → Log} (before : Untouched s ℓ)
    (key : KeeperId) (log : Log)
    (lostA : key = s.lostA → s.recovery ∉ log) (lostB : key = s.lostB → s.recovery ∉ log)
    (survivor : key = s.survivor → NewWorld s log ∨ s.recovery ∉ log)
    (fresh : key ∈ s.recovered → key ≠ s.survivor → log = []) :
    Untouched s (update ℓ key log) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold update; split
    · next same => exact lostA same.symm
    · exact before.lostA
  · unfold update; split
    · next same => exact lostB same.symm
    · exact before.lostB
  · unfold update; split
    · next same => exact survivor same.symm
    · exact before.survivor
  · intro k inside other
    unfold update; split
    · next same => subst same; exact fresh inside other
    · exact before.fresh k inside other

/-- When the first recovered member acts, the recovered members are all of
    the recovered world or all free of the recovery entry. -/
theorem untouched_split {s : Setup} {ℓ : KeeperId → Log} (before : Untouched s ℓ) :
    AllNew s ℓ ∨ AllFree s ℓ := by
  rcases before.survivor with world | free
  · left
    intro keeper member
    by_cases same : keeper = s.survivor
    · rw [same]; exact world
    · rw [before.fresh keeper member same]; exact newWorld_nil s
  · right
    intro keeper member
    by_cases same : keeper = s.survivor
    · rw [same]; exact free
    · rw [before.fresh keeper member same]; simp

theorem allNew_update {s : Setup} {ℓ : KeeperId → Log} (all : AllNew s ℓ) {key : KeeperId}
    {log : Log} (world : NewWorld s log) : AllNew s (update ℓ key log) := by
  intro k inside
  unfold update; split
  · exact world
  · exact all k inside

theorem allFree_update {s : Setup} {ℓ : KeeperId → Log} (all : AllFree s ℓ) {key : KeeperId}
    {log : Log} (free : s.recovery ∉ log) : AllFree s (update ℓ key log) := by
  intro k inside
  unfold update; split
  · exact free
  · exact all k inside

/-- Updating one recovered member's log keeps `After` when the new log is
    of the world the members were in. -/
theorem after_update {s : Setup} {ℓ : KeeperId → Log} {seen : Bool}
    (split : AllNew s ℓ ∨ AllFree s ℓ) (seenNew : seen = true → AllNew s ℓ)
    {key : KeeperId} {log : Log}
    (world : AllNew s ℓ → NewWorld s log) (free : AllFree s ℓ → s.recovery ∉ log) :
    (AllNew s (update ℓ key log) ∨ AllFree s (update ℓ key log)) ∧
      (seen = true → AllNew s (update ℓ key log)) := by
  refine ⟨?_, fun yes => allNew_update (seenNew yes) (world (seenNew yes))⟩
  rcases split with all | all
  · exact Or.inl (allNew_update all (world all))
  · exact Or.inr (allFree_update all (free all))

@[simp] theorem put_world (st : State) (k : KeeperId) (r : Replica) :
    (st.put k r).world = st.world.set k r := rfl
@[simp] theorem put_time (st : State) (k : KeeperId) (r : Replica) :
    (st.put k r).time = st.time := rfl
@[simp] theorem put_served (st : State) (k : KeeperId) (r : Replica) :
    (st.put k r).served = st.served := rfl
@[simp] theorem put_seenNew (st : State) (k : KeeperId) (r : Replica) :
    (st.put k r).seenNew = st.seenNew := rfl
@[simp] theorem put_mixed (st : State) (k : KeeperId) (r : Replica) :
    (st.put k r).mixed = st.mixed := rfl
@[simp] theorem serve_world (st : State) (k : KeeperId) : (st.serve k).world = st.world := rfl
@[simp] theorem serve_time (st : State) (k : KeeperId) : (st.serve k).time = st.time := rfl
@[simp] theorem serve_seenNew (st : State) (k : KeeperId) :
    (st.serve k).seenNew = st.seenNew := rfl
@[simp] theorem serve_mixed (st : State) (k : KeeperId) : (st.serve k).mixed = st.mixed := rfl
@[simp] theorem observe_world (s : Setup) (st : State) (obs : Log) :
    (observe s st obs).world = st.world := rfl
@[simp] theorem observe_time (s : Setup) (st : State) (obs : Log) :
    (observe s st obs).time = st.time := rfl
@[simp] theorem observe_served (s : Setup) (st : State) (obs : Log) :
    (observe s st obs).served = st.served := rfl

theorem serve_served_some {st : State} {first : KeeperId × Nat} (served : st.served = some first)
    (k : KeeperId) : (st.serve k).served = some first := by
  simp [State.serve, served]

theorem serve_served_none {st : State} (served : st.served = none) (k : KeeperId) :
    (st.serve k).served = some (k, st.time) := by
  simp [State.serve, served]

/-- After the first recovered action no lost voter is gated in. -/
theorem lost_closed {g : Gates} (separated : g.Separated) {st : State}
    {first : KeeperId} {u : Nat} (served : g.newActs first u) (past : u ≤ st.time)
    {keeper : KeeperId} (acts : g.lostActs keeper st.time) : False := by
  have before := separated keeper first st.time u acts served
  exact Nat.lt_irrefl u (Nat.lt_of_le_of_lt past before)

/-- The recovered steps keep `After`; lost steps cannot happen. -/
theorem after_step {s : Setup} {g : Gates} {st next : State} (after : After s st)
    (step : Step s g st next) (closed : ∀ keeper, ¬ (s.Lost keeper ∧ g.lostActs keeper st.time)) :
    After s next := by
  obtain ⟨split, seen, clean⟩ := after
  cases step with
  | tick => exact ⟨split, seen, clean⟩
  | restart keeper online =>
      have same : logs (st.world.set keeper { st.world keeper with online := online }) =
          logs st.world := by rw [logs_set]; exact update_same _ _
      simp only [After, put_world, put_seenNew, put_mixed, same]
      exact ⟨split, seen, clean⟩
  | lostElect keeper lost acts => exact absurd ⟨lost, acts⟩ (closed keeper)
  | lostAppend keeper _ lost acts => exact absurd ⟨lost, acts⟩ (closed keeper)
  | lostReplicate leader _ _ lost _ acts => exact absurd ⟨lost, acts⟩ (closed leader)
  | lostRead keeper _ lost acts => exact absurd ⟨lost, acts⟩ (closed keeper)
  | contactRevert keeper lost acts => exact absurd ⟨lost, acts⟩ (closed keeper)
  | contactVote keeper lost acts => exact absurd ⟨lost, acts⟩ (closed keeper)
  | newAppend keeper entry member _ complete _ =>
      simp only [After, serve_world, put_world, serve_seenNew, put_seenNew, serve_mixed,
        put_mixed, logs_set]
      exact ⟨(after_update split seen (fun _ => newWorld_append complete entry)
        (fun all => absurd complete (not_shows_of_recFree (all keeper member)))).1,
        (after_update split seen (fun _ => newWorld_append complete entry)
        (fun all => absurd complete (not_shows_of_recFree (all keeper member)))).2, clean⟩
  | oldAppend entry _ diverged other =>
      have mem := s.survivorRecovered
      simp only [After, serve_world, put_world, serve_seenNew, put_seenNew, serve_mixed,
        put_mixed, logs_set]
      have := after_update (key := s.survivor) split seen
        (fun all => absurd (all s.survivor mem) diverged)
        (fun all => recFree_append (all s.survivor mem) other)
      exact ⟨this.1, this.2, clean⟩
  | newReplicate leader follower kept leaderIn _ _ =>
      simp only [After, serve_world, put_world, serve_seenNew, put_seenNew, serve_mixed,
        put_mixed, logs_set]
      have := after_update (key := follower) split seen
        (fun all => newWorld_take (all leader leaderIn) kept)
        (fun all => recFree_take (all leader leaderIn) kept)
      exact ⟨this.1, this.2, clean⟩
  | newRead keeper kept member _ =>
      simp only [After, serve_world, serve_seenNew, serve_mixed, observe]
      by_cases seenNow : st.seenNew = true
      · have all := seen seenNow
        have world : NewWorld s ((st.world keeper).log.take kept) := newWorld_take (all keeper member) kept
        refine ⟨Or.inl all, fun _ => all, ?_⟩
        simp [clean, Conflicts, world]
      · have unseen : st.seenNew = false := by simpa using seenNow
        rcases split with all | all
        · refine ⟨Or.inl all, fun _ => all, ?_⟩
          simp [clean, unseen]
        · have hidden := not_shows_of_recFree (recFree_take (all keeper member) kept)
          refine ⟨Or.inr all, fun yes => ?_, ?_⟩
          · rw [unseen, Bool.false_or, decide_eq_true_eq] at yes
            exact absurd yes hidden
          · simp [clean, unseen]

/-- Steps never move time back and never forget the first recovered action. -/
theorem step_time {s : Setup} {g : Gates} {st next : State} (step : Step s g st next) :
    st.time ≤ next.time := by
  cases step <;> simp [State.put, State.serve, observe]

theorem step_served {s : Setup} {g : Gates} {st next : State} {first : KeeperId × Nat}
    (served : st.served = some first) (step : Step s g st next) : next.served = some first := by
  cases step <;> simp [State.put, State.serve, observe, served]

theorem inv_some {s : Setup} {g : Gates} {st : State} {keeper : KeeperId} {u : Nat}
    (served : st.served = some (keeper, u)) :
    Inv s g st ↔ g.newActs keeper u ∧ u ≤ st.time ∧ After s st := by
  simp [Inv, served]

theorem inv_none {s : Setup} {g : Gates} {st : State} (served : st.served = none) :
    Inv s g st ↔ Before s st := by
  simp [Inv, served]

theorem step_preserves {s : Setup} {g : Gates} (separated : g.Separated) {st next : State}
    (inv : Inv s g st) (step : Step s g st next) : Inv s g next := by
  rcases served : st.served with _ | ⟨first, u⟩
  · obtain ⟨before, unseen, clean⟩ := (inv_none served).1 inv
    have startNew : ∀ keeper, g.newActs keeper st.time → next.served = some (keeper, st.time) →
        next.time = st.time → Inv s g next := by
      intro keeper acts nextServed now
      have closed : ∀ k, ¬ (s.Lost k ∧ g.lostActs k st.time) :=
        fun _ ⟨_, lostActs⟩ => lost_closed separated acts (Nat.le_refl _) lostActs
      have opened : After s st := ⟨untouched_split before, fun yes => by
        rw [unseen] at yes; contradiction, clean⟩
      exact (inv_some nextServed).2 ⟨acts, by omega, after_step opened step closed⟩
    have stay : ∀ (key : KeeperId) (replica : Replica), Untouched s (update (logs st.world) key replica.log) →
        Inv s g (st.put key replica) := by
      intro key replica untouched
      refine (inv_none (by simpa using served)).2 ⟨?_, unseen, clean⟩
      simp only [put_world, logs_set]
      exact untouched
    cases step with
    | tick =>
        refine (inv_none ?_).2 ⟨before, unseen, clean⟩
        exact served
    | restart keeper online =>
        apply stay
        have same : ({ st.world keeper with online := online } : Replica).log =
            logs st.world keeper := rfl
        rw [same, update_same]
        exact before
    | lostElect keeper lost _ =>
        apply stay
        exact untouched_update before keeper _
          (fun same => same ▸ before.lostA) (fun same => same ▸ before.lostB)
          (fun same => absurd same.symm (lost_ne_survivor lost))
          (fun inside => absurd rfl (lost_ne_recovered lost inside))
    | lostAppend keeper entry lost _ distinct =>
        apply stay
        have grown := recFree_append (untouched_lost before lost) distinct
        exact untouched_update before keeper _ (fun _ => grown) (fun _ => grown)
          (fun same => absurd same.symm (lost_ne_survivor lost))
          (fun inside => absurd rfl (lost_ne_recovered lost inside))
    | lostReplicate leader follower kept leaderLost followerLost _ =>
        apply stay
        have copied := recFree_take (untouched_lost before leaderLost) kept
        exact untouched_update before follower _ (fun _ => copied) (fun _ => copied)
          (fun same => absurd same.symm (lost_ne_survivor followerLost))
          (fun inside => absurd rfl (lost_ne_recovered followerLost inside))
    | lostRead keeper kept lost _ =>
        have hidden := not_shows_of_recFree (recFree_take (untouched_lost before lost) kept)
        refine (inv_none (by simpa using served)).2 ⟨?_, ?_, ?_⟩
        · simpa using before
        · show (st.seenNew || decide _) = false
          rw [unseen, Bool.false_or]
          exact decide_eq_false hidden
        · simp [observe, clean, unseen]
    | contactRevert keeper lost _ _ _ =>
        apply stay
        have free := untouched_lost before lost
        exact untouched_update before s.survivor _
          (fun same => absurd same (lost_ne_survivor (Or.inl rfl)))
          (fun same => absurd same (lost_ne_survivor (Or.inr rfl)))
          (fun _ => Or.inr free) (fun _ other => absurd rfl other)
    | contactVote keeper _ _ =>
        apply stay
        exact untouched_update before s.survivor _
          (fun same => absurd same (lost_ne_survivor (Or.inl rfl)))
          (fun same => absurd same (lost_ne_survivor (Or.inr rfl)))
          (fun _ => before.survivor) (fun _ other => absurd rfl other)
    | newAppend keeper _ _ acts =>
        exact startNew keeper acts (serve_served_none (by simpa using served) _) rfl
    | oldAppend _ acts =>
        exact startNew s.survivor acts (serve_served_none (by simpa using served) _) rfl
    | newReplicate leader _ _ _ _ acts =>
        exact startNew leader acts (serve_served_none (by simpa using served) _) rfl
    | newRead keeper _ _ acts =>
        exact startNew keeper acts (serve_served_none (by simpa using served) _) rfl
  · obtain ⟨acts, past, after⟩ := (inv_some served).1 inv
    have closed : ∀ k, ¬ (s.Lost k ∧ g.lostActs k st.time) :=
      fun _ ⟨_, lostActs⟩ => lost_closed separated acts past lostActs
    exact (inv_some (step_served served step)).2
      ⟨acts, Nat.le_trans past (step_time step), after_step after step closed⟩

theorem trace_preserves {s : Setup} {g : Gates} (separated : g.Separated) {st last : State}
    (inv : Inv s g st) (trace : Trace s g st last) : Inv s g last := by
  induction trace with
  | refl => exact inv
  | step step _ next => exact next (step_preserves separated inv step)

theorem inv_clean {s : Setup} {g : Gates} {st : State} (inv : Inv s g st) : st.mixed = false := by
  rcases served : st.served with _ | ⟨first, u⟩
  · exact ((inv_none served).1 inv).2.2
  · exact ((inv_some served).1 inv).2.2.2.2

/-- No mixed history after recovery, with no election budget, both lost
    voters running and no trust in `--lost`: on every trace whose gates are
    separated, no reader observes a history the recovery did not keep after
    a reader observed the recovered history. -/
theorem no_mixed_history {s : Setup} {g : Gates} (separated : g.Separated) {st last : State}
    (start : Before s st) (fresh : st.served = none) (trace : Trace s g st last) :
    last.mixed = false :=
  inv_clean (trace_preserves separated ((inv_none fresh).2 start) trace)

/-- After the first action of a recovered member, no lost voter campaigns,
    leads, replicates or serves a read again: CE-4 closed for lost voters
    that never stopped. -/
theorem lost_voters_deposed {s : Setup} {g : Gates} (separated : g.Separated) {st last : State}
    (start : Before s st) (fresh : st.served = none) (trace : Trace s g st last)
    {first : KeeperId} {u : Nat} (served : last.served = some (first, u)) {keeper : KeeperId} :
    ¬ g.lostActs keeper last.time := by
  have inv := trace_preserves separated ((inv_none fresh).2 start) trace
  obtain ⟨acts, past, _⟩ := (inv_some served).1 inv
  exact fun lostActs => lost_closed separated acts past lostActs

/-- The gates of the lease model under the `allOld` fence. -/
def LeaseWorld.lostGates {D H : Nat} (w : LeaseWorld D H) (s : Setup) (named : List KeeperId) :
    Gates where
  lostActs keeper t := s.Lost keeper ∧ (w.gates .allOld s named).lostActs keeper t
  newActs := (w.gates .allOld s named).newActs

theorem LeaseWorld.lostGates_separated {D H : Nat} (w : LeaseWorld D H) (s : Setup)
    (named : List KeeperId) (margin : D ≤ w.M) (horizon : w.L + w.M + D ≤ H) :
    (w.lostGates s named).Separated :=
  fun lost member t u acts waited => by
    have := w.separated s named margin horizon lost member t u acts.1 acts.2 waited
    omega

/-- The same under the lease model: with `D ≤ M`, `L + M + D ≤ H` and the
    `allOld` fence, which ignores `--lost`, no reader mixes histories. -/
theorem no_mixed_history_under_leases {D H : Nat} (w : LeaseWorld D H) (s : Setup)
    (named : List KeeperId) (margin : D ≤ w.M) (horizon : w.L + w.M + D ≤ H)
    {st last : State} (start : Before s st) (fresh : st.served = none)
    (trace : Trace s (w.lostGates s named) st last) : last.mixed = false :=
  no_mixed_history (w.lostGates_separated s named margin horizon) start fresh trace

/-! ## Negative controls -/

/-- A recovery: survivor `0`, lost voters `1` and `2`, replacements `3` and
    `4`, and a lost suffix `(2, 7)` the survivor never saw. -/
def sample : Setup where
  survivor := 0
  lostA := 1
  lostB := 2
  recovered := [0, 3, 4]
  term := 2
  history := [(1, 1), (2, 0)]
  recovery := (2, 0)
  recInHistory := by decide
  survivorRecovered := by decide
  lostAOutside := by decide
  lostBOutside := by decide

def sampleWorld : World := fun keeper =>
  if keeper = 0 then ⟨2, [(1, 1), (2, 0)], true⟩
  else if keeper = 1 ∨ keeper = 2 then ⟨2, [(1, 1), (2, 7)], true⟩
  else ⟨0, [], true⟩

def sampleStart : State := ⟨0, sampleWorld, none, false, false⟩

theorem sample_before : Before sample sampleStart := by
  refine ⟨⟨by decide, by decide, by decide, ?_⟩, rfl, rfl⟩
  intro keeper inside other
  simp only [sample, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl
  · exact absurd rfl other
  · rfl
  · rfl

/-- Without the wait-out, the survivor serves the recovered history while a
    lost voter's lease still lets it serve the lost suffix: a mixed history. -/
theorem no_wait_out_mixes :
    let gates : Gates := ⟨fun _ _ => True, fun _ _ => True⟩
    ∃ last, Trace sample gates sampleStart last ∧ last.mixed = true := by
  intro gates
  let afterNew : State :=
    (observe sample sampleStart ((sampleStart.world 0).log.take 2)).serve 0
  refine ⟨observe sample afterNew ((afterNew.world 1).log.take 2), ?_, ?_⟩
  · exact Trace.step (Step.newRead sampleStart 0 2 (by decide) trivial)
      (Trace.step (Step.lostRead afterNew 1 2 (Or.inl rfl) trivial) (Trace.refl _))
  · decide

/-- A slow holder: its clock stands still for two ticks after real time 0. -/
def slowClock : Clock 2 6 where
  read t := if t ≤ 2 then 0 else t - 2
  monotone := by intro t u _; split <;> split <;> omega
  slow := by intro t u _ _; split <;> split <;> omega
  fast := by intro t u _ _; split <;> split <;> omega

/-- A fast waiter: its clock jumps two ticks ahead after real time 0. -/
def fastClock : Clock 2 6 where
  read u := if u = 0 then 0 else u + 2
  monotone := by intro t u _; split <;> split <;> omega
  slow := by intro t u _ _; split <;> split <;> omega
  fast := by intro t u _ _; split <;> split <;> omega

/-- With `M = 1 < D = 2`, a lease granted at the commit (real time 0) is
    still valid at real time 3, after a waiter that learned at the commit
    finished its wait-out at real time 2. -/
theorem drift_beyond_margin_overlaps :
    Holds slowClock 3 1 0 3 ∧ Waited fastClock 3 1 0 2 ∧ ¬ (3 < 2) := by
  refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, by omega⟩
  · show (if 3 ≤ 2 then 0 else 3 - 2) - (if 0 ≤ 2 then 0 else 0 - 2) + 1 < 3
    decide
  · show 3 + 1 ≤ (if 2 = 0 then 0 else 2 + 2) - (if 0 = 0 then 0 else 0 + 2)
    decide

/-- An exact clock. -/
def exactClock : Clock 0 6 where
  read t := t
  monotone := fun le => le
  slow := by intro t u _ _; omega
  fast := by intro t u _ _; omega

/-- Fencing only the keepers `--lost` names: with `--lost 1`, lost voter `2`
    renews unfenced after the commit and acts after the wait-out. -/
theorem named_only_fence_leaks :
    let w : LeaseWorld 0 6 := ⟨3, 1, 0, fun _ => exactClock, fun _ => 0, fun _ => Nat.le_refl 0⟩
    (w.gates .namedOnly sample [1]).lostActs 2 5 ∧ (w.gates .namedOnly sample [1]).newActs 0 4 ∧
      ¬ (5 < 4) := by
  intro w
  refine ⟨⟨5, ?_, ⟨Nat.le_refl 5, ?_⟩⟩, ⟨by decide, ?_⟩, by omega⟩
  · simp [fences]
  · show 5 - 5 + 1 < 3
    decide
  · show 3 + 1 ≤ 4 - 0
    decide

#print axioms rate_bounds_error
#print axioms lease_precedes_wait
#print axioms LeaseWorld.separated
#print axioms step_preserves
#print axioms no_mixed_history
#print axioms lost_voters_deposed
#print axioms no_mixed_history_under_leases
#print axioms no_wait_out_mixes
#print axioms drift_beyond_margin_overlaps
#print axioms named_only_fence_leaks

end Logkeeper.ConsensusAdditions.EpochLease
