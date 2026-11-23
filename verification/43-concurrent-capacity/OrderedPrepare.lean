import Std

set_option warningAsError true

namespace OrderedPrepare

variable {Intent Pool : Type}

structure Snapshot (Intent Pool : Type) where
  held : Intent → Pool → Prop
  waiting : Intent → Option Pool
  rank : Pool → Nat

def KeepsOrder (state : Snapshot Intent Pool) : Prop :=
  ∀ intent owned requested, state.held intent owned → state.waiting intent = some requested →
    state.rank owned < state.rank requested

def WaitsFor (state : Snapshot Intent Pool) (waiter holder : Intent) : Prop :=
  ∃ pool, state.waiting waiter = some pool ∧ state.held holder pool

inductive WaitPath (state : Snapshot Intent Pool) : Intent → Intent → Prop
  | one {waiter holder} : WaitsFor state waiter holder → WaitPath state waiter holder
  | more {first middle last} : WaitPath state first middle → WaitsFor state middle last →
      WaitPath state first last

theorem a_wait_path_increases_requested_rank
    {state : Snapshot Intent Pool} {first last : Intent}
    (order : KeepsOrder state) (path : WaitPath state first last) :
    ∀ initial target, state.waiting first = some initial → state.waiting last = some target →
      state.rank initial < state.rank target := by
  induction path with
  | one edge =>
      intro initial target fromWait toWait
      obtain ⟨pending, waits, held⟩ := edge
      have equal := Option.some.inj (waits.symm.trans fromWait)
      exact equal ▸ order _ _ _ held toWait
  | more _ edge prior =>
      intro initial target fromWait toWait
      obtain ⟨middle, waiting, held⟩ := edge
      exact Nat.lt_trans (prior initial middle fromWait waiting) (order _ _ _ held toWait)

theorem ordered_reservations_have_no_cycle
    {state : Snapshot Intent Pool} (order : KeepsOrder state) (intent : Intent) :
    ¬ WaitPath state intent intent := by
  intro cycle
  have hasFirst {first last} (path : WaitPath state first last) :
      ∃ requested, state.waiting first = some requested := by
    induction path with
    | one edge =>
        obtain ⟨requested, waiting, _⟩ := edge
        exact ⟨requested, waiting⟩
    | more _ _ prior => exact prior
  obtain ⟨requested, waiting⟩ := hasFirst cycle
  exact Nat.lt_irrefl _ (a_wait_path_increases_requested_rank order cycle requested requested waiting waiting)

def oppositeOrder : Snapshot Bool Bool :=
  ⟨fun intent pool => pool = intent, fun intent => some (!intent), fun pool => if pool then 1 else 0⟩

theorem arbitrary_acquisition_has_a_two_intent_cycle : WaitPath oppositeOrder false false :=
  .more (.one ⟨true, rfl, rfl⟩) ⟨false, rfl, rfl⟩

inductive Decision where
  | preparing
  | boundToSeal
  | canceled
  deriving DecidableEq

def CoversVector (needs : Pool → Nat) (held : Pool → Nat) : Prop :=
  ∀ pool, needs pool ≤ held pool

inductive Decide (needs : Pool → Nat) : Decision → Decision → Prop
  | seal (held : Pool → Nat) (complete : CoversVector needs held) :
      Decide needs .preparing .boundToSeal
  | cancel : Decide needs .preparing .canceled
  | replay (decision : Decision) : Decide needs decision decision

inductive Decisions (needs : Pool → Nat) : Decision → Decision → Prop
  | same (decision) : Decisions needs decision decision
  | next {first before after} : Decisions needs first before → Decide needs before after → Decisions needs first after

theorem a_bound_seal_cannot_later_produce_an_abort
    {needs : Pool → Nat} {after : Decision} (trace : Decisions needs .boundToSeal after) :
    after = .boundToSeal := by
  induction trace with
  | same => rfl
  | next _ step same =>
      cases step <;> simp_all

theorem an_abort_cannot_later_authorize_seal
    {needs : Pool → Nat} {after : Decision} (trace : Decisions needs .canceled after) :
    after = .canceled := by
  induction trace with
  | same => rfl
  | next _ step same =>
      cases step <;> simp_all

theorem seal_requires_full_vector {needs held : Pool → Nat} (complete : CoversVector needs held) :
    ∀ pool, needs pool ≤ held pool := by
  exact complete

structure Partial (Pool : Type) where
  decision : Decision
  held : Pool → Nat
  fenced : Pool → Prop

def AcceptsDelayedPrepare (state : Partial Pool) (pool : Pool) : Prop :=
  ¬ state.fenced pool

theorem eligible_pool_is_open {state : Partial Pool} {pool : Pool}
    (eligible : AcceptsDelayedPrepare state pool) : ¬ state.fenced pool := by
  exact eligible

inductive LocalStep [DecidableEq Pool] (needs : Pool → Nat) : Partial Pool → Partial Pool → Prop
  | accept {state} (pool : Pool) (eligible : AcceptsDelayedPrepare state pool) :
      LocalStep needs state {state with held := fun query => if query = pool then needs pool else state.held query}
  | authorizeSeal {state} (preparing : state.decision = .preparing) (complete : CoversVector needs state.held) :
      LocalStep needs state {state with decision := .boundToSeal}
  | abort {state} (preparing : state.decision = .preparing) :
      LocalStep needs state {state with decision := .canceled}
  | closePool {state} (pool : Pool) (durableAbort : state.decision = .canceled) :
      LocalStep needs state
        {state with
          held := fun query => if query = pool then 0 else state.held query
          fenced := fun query => query = pool ∨ state.fenced query}
  | restart {state} : LocalStep needs state state

inductive LocalTrace [DecidableEq Pool] (needs : Pool → Nat) : Partial Pool → Partial Pool → Prop
  | same (state) : LocalTrace needs state state
  | next {first before after} : LocalTrace needs first before → LocalStep needs before after →
      LocalTrace needs first after

theorem closed_pool_keeps_refusing_delayed_prepares
    [DecidableEq Pool] {needs : Pool → Nat} {first last : Partial Pool} {pool : Pool}
    (closed : first.fenced pool) (empty : first.held pool = 0) (trace : LocalTrace needs first last) :
    last.fenced pool ∧ last.held pool = 0 := by
  induction trace with
  | same => exact ⟨closed, empty⟩
  | next _ step prior =>
      cases step with
      | accept requested eligible =>
          have different : pool ≠ requested := by
            intro alias
            subst requested
            exact eligible_pool_is_open eligible prior.1
          exact ⟨prior.1, by simpa [different] using prior.2⟩
      | closePool closedAt _ =>
          by_cases same : pool = closedAt
          · subst closedAt
            exact ⟨.inl rfl, by simp⟩
          · exact ⟨.inr prior.1, by simpa [same] using prior.2⟩
      | _ => exact prior

theorem complete_capacity_stays_committed_before_install
    [DecidableEq Pool] {needs : Pool → Nat} {first last : Partial Pool}
    (committed : first.decision = .boundToSeal) (complete : CoversVector needs first.held)
    (trace : LocalTrace needs first last) :
    last.decision = .boundToSeal ∧ CoversVector needs last.held := by
  induction trace with
  | same => exact ⟨committed, complete⟩
  | next _ step prior =>
      cases step with
      | accept requested _ =>
          refine ⟨prior.1, ?_⟩
          intro pool
          by_cases same : pool = requested
          · simp [same]
          · simpa [same] using prior.2 pool
      | authorizeSeal preparing _ => rw [prior.1] at preparing; cases preparing
      | abort preparing => rw [prior.1] at preparing; cases preparing
      | closePool _ canceled => rw [prior.1] at canceled; cases canceled
      | restart => exact prior

#print axioms a_wait_path_increases_requested_rank
#print axioms ordered_reservations_have_no_cycle
#print axioms arbitrary_acquisition_has_a_two_intent_cycle
#print axioms a_bound_seal_cannot_later_produce_an_abort
#print axioms an_abort_cannot_later_authorize_seal
#print axioms seal_requires_full_vector
#print axioms closed_pool_keeps_refusing_delayed_prepares
#print axioms complete_capacity_stays_committed_before_install

end OrderedPrepare
