import RegionalRetirement

set_option warningAsError true

namespace StagedVotes

open PrefixAgreement (Vote RankLE)
open SnapshotAdmission (setSlot)

variable {slots : Nat} {Command Ticket : Type}

structure Copy (Command : Type) where
  vote : Vote Command
  bytes : Bool := false
  named : Bool := false

structure State (Command Ticket : Type) where
  pool : PoolIncarnations.State Ticket
  voter : DurableAcceptor.State Command
  copies : Nat → Option (Copy Command)
  current : Option Nat
  pinned : Nat → Bool
  issued : Nat

structure Rules (slots : Nat) (Command Ticket : Type) where
  regional : RegionalRetirement.Rules slots Command Ticket
  cost : Vote Command → Nat
  releasePin : Nat → Prop

def Backed (pool : PoolIncarnations.State Ticket) (version : Nat) : Prop :=
  version ∈ pool.ledger.debits ∧ (pool.ledger.provider version).present = true

def Exact (state : State Command Ticket) (version : Nat) (vote : Vote Command) : Prop :=
  state.copies version = some ⟨vote, true, true⟩

def CanAccept (state : State Command Ticket) (version : Nat) (vote : Vote Command) : Prop :=
  ∃ copy, state.copies version = some copy ∧ copy.vote = vote ∧ copy.bytes = true ∧ copy.named = true

private theorem exact_acceptance {state : State Command Ticket} {version : Nat} {vote : Vote Command}
    (ready : CanAccept state version vote) : Exact state version vote := by
  obtain ⟨copy, held, matchesVote, bytes, path⟩ := ready
  have durableBytes : copy.bytes = true := bytes
  have durablePath : copy.named = true := path
  cases copy
  simp_all [Exact]

def recover (state : State Command Ticket) : Option (Vote Command) := do
  let version ← state.current
  let copy ← state.copies version
  if copy.bytes && copy.named then some copy.vote else none

def update (state : State Command Ticket) (version : Nat) (copy : Option (Copy Command)) :
    State Command Ticket :=
  {state with copies := setSlot state.copies version copy}

def install (state : State Command Ticket) (version : Nat) (vote : Vote Command) :
    State Command Ticket :=
  {state with voter := DurableAcceptor.acceptVote state.voter vote, current := some version}

def Enough (rules : Rules slots Command Ticket) (version : Nat) (vote : Vote Command) : Prop :=
  rules.cost vote ≤ rules.regional.layout.bytes version

structure Sound (rules : Rules slots Command Ticket) (state : State Command Ticket) : Prop where
  voter : DurableAcceptor.Reachable state.voter
  pool : PoolIncarnations.Sound rules.regional.poolLimit rules.regional.layout rules.regional.needs state.pool
  charged : ∀ version copy, state.copies version = some copy →
    version ≤ state.issued ∧ Backed state.pool version ∧ Enough rules version copy.vote
  bound : (state.current = none ∧ state.voter.latest = none) ∨
    ∃ version vote, state.current = some version ∧ state.voter.latest = some vote ∧ Exact state version vote
  pinned : ∀ version, state.pinned version = true → ∃ vote, Exact state version vote

variable [DecidableEq Ticket]

inductive Step (rules : Rules slots Command Ticket) :
    State Command Ticket → State Command Ticket → Prop
  | pool {state next} {event : PoolIncarnations.Event}
      (change : RegionalRetirement.PoolStep rules.regional state.pool event next)
      (keeps : ∀ version copy, state.copies version = some copy → Backed next version) :
      Step rules state {state with pool := next}
  | stage {state} (version : Nat) (vote : Vote Command)
      (fresh : state.issued < version)
      (physical : Backed state.pool version)
      (eligible : PoolIncarnations.Eligible state.pool (rules.regional.layout.pool version))
      (enough : Enough rules version vote) :
      Step rules state {update state version (some ⟨vote, false, false⟩) with issued := version}
  | syncBytes {state} (version : Nat) (vote : Vote Command) (named : Bool)
      (ticket : state.copies version = some ⟨vote, false, named⟩) :
      Step rules state (update state version (some ⟨vote, true, named⟩))
  | syncPath {state} (version : Nat) (vote : Vote Command) (bytes : Bool)
      (ticket : state.copies version = some ⟨vote, bytes, false⟩) :
      Step rules state (update state version (some ⟨vote, bytes, true⟩))
  | accept {state} (version : Nat) (vote : Vote Command) (ready : CanAccept state version vote)
      (promise : state.voter.promised ≤ vote.ballot)
      (ranked : ∀ old, state.voter.latest = some old → RankLE old vote) :
      Step rules state (install state version vote)
  | prepare {state} (ballot : Nat) (higher : state.voter.promised < ballot) :
      Step rules state {state with voter := DurableAcceptor.promise state.voter ballot}
  | pin {state} (version : Nat) (vote : Vote Command) (ready : Exact state version vote) :
      Step rules state {state with pinned := setSlot state.pinned version true}
  | unpin {state} (version : Nat) (release : rules.releasePin version) :
      Step rules state {state with pinned := setSlot state.pinned version false}
  | discard {state} (version : Nat) (notCurrent : state.current ≠ some version)
      (free : state.pinned version = false) :
      Step rules state (update state version none)
  | restart {state} : Step rules state state

inductive Trace (rules : Rules slots Command Ticket) :
    State Command Ticket → State Command Ticket → Prop
  | same (state : State Command Ticket) : Trace rules state state
  | next {first current next} : Trace rules first current → Step rules current next → Trace rules first next

omit [DecidableEq Ticket] in
private theorem exactVersion {state : State Command Ticket} {version : Nat} {left right : Vote Command}
    (first : Exact state version left) (second : Exact state version right) : left = right := by
  have equal := Option.some.inj (first.symm.trans second)
  exact congrArg Copy.vote equal

omit [DecidableEq Ticket] in
theorem exact_reopen_returns_the_last_durable_vote
    {rules : Rules slots Command Ticket} {state : State Command Ticket} (safe : Sound rules state) :
    recover state = state.voter.latest := by
  rcases safe.bound with ⟨none, noVote⟩ | ⟨version, vote, selected, recorded, exactCopy⟩
  · simp [recover, none, noVote]
  · simp [recover, selected, recorded, Exact] at exactCopy ⊢
    rw [exactCopy]
    rfl

private theorem acceptor_projection {rules : Rules slots Command Ticket} {state next : State Command Ticket}
    (step : Step rules state next) : DurableAcceptor.Step state.voter next.voter := by
  cases step with
  | accept _ vote _ promise ranked => exact .accept vote promise ranked
  | prepare ballot higher => exact .prepare ballot higher
  | _ => exact .restart

omit [DecidableEq Ticket] in
private theorem no_effect_on_other_exact_roles {state : State Command Ticket} {updated : Nat}
    {replacement : Option (Copy Command)} {version : Nat} {vote : Vote Command}
    (other : version ≠ updated) (before : Exact state version vote) :
    Exact (update state updated replacement) version vote := by
  simpa [Exact, update, setSlot, other] using before

private theorem preserves_roles {rules : Rules slots Command Ticket} {state next : State Command Ticket}
    (safe : Sound rules state) (step : Step rules state next) :
    (∀ version vote, Exact state version vote →
      (state.current = some version ∨ next.pinned version = true ∧ state.pinned version = true) →
      Exact next version vote) := by
  intro version vote before mustKeep
  cases step with
  | stage updated _ fresh _ _ _ =>
      have known := (safe.charged version ⟨vote, true, true⟩ before).1
      exact no_effect_on_other_exact_roles (by omega) before
  | syncBytes updated _ _ ticket =>
      have other : version ≠ updated := by
        intro equal
        subst updated
        rw [Exact, ticket] at before
        cases before
      exact no_effect_on_other_exact_roles other before
  | syncPath updated _ _ ticket =>
      have other : version ≠ updated := by
        intro equal
        subst updated
        rw [Exact, ticket] at before
        cases before
      exact no_effect_on_other_exact_roles other before
  | discard updated notCurrent free =>
      have other : version ≠ updated := by
        intro equal
        subst updated
        rcases mustKeep with current | pinned
        · exact notCurrent current
        · rw [free] at pinned
          exact Bool.false_ne_true pinned.2
      exact no_effect_on_other_exact_roles other before
  | _ => exact before

private theorem charge_preserved {rules : Rules slots Command Ticket}
    {state next : State Command Ticket} (safe : Sound rules state) (step : Step rules state next) :
    ∀ version copy, next.copies version = some copy →
      version ≤ next.issued ∧ Backed next.pool version ∧ Enough rules version copy.vote := by
  intro version copy live
  cases step with
  | pool change keeps =>
      obtain ⟨known, _, fits⟩ := safe.charged version copy live
      exact ⟨known, keeps version copy live, fits⟩
  | stage fresh vote newer charged eligible fits =>
      by_cases same : version = fresh
      · subst version
        simp [update, setSlot] at live
        subst copy
        exact ⟨Nat.le_refl _, charged, fits⟩
      · have earlier : state.copies version = some copy := by simpa [update, setSlot, same] using live
        obtain ⟨known, paid, bounded⟩ := safe.charged version copy earlier
        exact ⟨Nat.le_trans known (Nat.le_of_lt newer), paid, bounded⟩
  | syncBytes updated vote named ticket =>
      by_cases same : version = updated
      · subst version
        simp [update, setSlot] at live
        subst copy
        exact safe.charged updated ⟨vote, false, named⟩ ticket
      · exact safe.charged version copy (by simpa [update, setSlot, same] using live)
  | syncPath updated vote bytes ticket =>
      by_cases same : version = updated
      · subst version
        simp [update, setSlot] at live
        subst copy
        exact safe.charged updated ⟨vote, bytes, false⟩ ticket
      · exact safe.charged version copy (by simpa [update, setSlot, same] using live)
  | discard removed =>
      by_cases same : version = removed
      · simp [update, setSlot, same] at live
      · exact safe.charged version copy (by simpa [update, setSlot, same] using live)
  | _ => exact safe.charged version copy live

private theorem bound_preserved {rules : Rules slots Command Ticket} {state next : State Command Ticket}
    (safe : Sound rules state) (step : Step rules state next)
    (stable : next.current = state.current ∨ ∃ version vote,
      next.current = some version ∧ next.voter.latest = some vote ∧ Exact next version vote) :
    (next.current = none ∧ next.voter.latest = none) ∨
      ∃ version vote, next.current = some version ∧ next.voter.latest = some vote ∧ Exact next version vote := by
  rcases stable with same | changed
  · have sameVote : next.voter.latest = state.voter.latest := by
      cases step with
      | accept version vote ready _ _ =>
          rcases safe.bound with ⟨empty, _⟩ | ⟨oldVersion, oldVote, selected, ranked, oldCopy⟩
          · rw [empty] at same
            cases same
          · simp only [install, selected, Option.some.injEq] at same
            subst oldVersion
            rw [← exactVersion oldCopy (exact_acceptance ready), ranked]
            rfl
      | _ => rfl
    rcases safe.bound with ⟨none, noVote⟩ | ⟨version, vote, selected, known, exactCopy⟩
    · exact .inl ⟨same.trans none, sameVote.trans noVote⟩
    · exact .inr ⟨version, vote, same.trans selected, sameVote.trans known,
        preserves_roles safe step version vote exactCopy (.inl selected)⟩
  · exact .inr changed

theorem staged_steps_preserve_exact_discoverable_and_paid_votes
    {rules : Rules slots Command Ticket} {state next : State Command Ticket}
    (safe : Sound rules state) (step : Step rules state next) : Sound rules next := by
  refine ⟨.extend safe.voter (acceptor_projection step), ?_, charge_preserved safe step,
    bound_preserved safe step ?_, ?_⟩
  · cases step with
    | pool change _ => exact PoolIncarnations.every_step_preserves_bounded_scoped_custody safe.pool change
    | _ => exact safe.pool
  · cases step with
    | accept version vote ready _ _ => exact .inr ⟨version, vote, rfl, rfl, exact_acceptance ready⟩
    | _ => exact .inl rfl
  · intro version held
    cases step with
    | stage fresh vote newer physical eligible enough =>
        obtain ⟨old, exactCopy⟩ := safe.pinned version held
        have event : Step rules state _ := .stage fresh vote newer physical eligible enough
        exact ⟨old, preserves_roles safe event version old exactCopy (.inr ⟨held, held⟩)⟩
    | syncBytes updated vote named ticket =>
        obtain ⟨old, exactCopy⟩ := safe.pinned version held
        have event : Step rules state _ := .syncBytes updated vote named ticket
        exact ⟨old, preserves_roles safe event version old exactCopy (.inr ⟨held, held⟩)⟩
    | syncPath updated vote bytes ticket =>
        obtain ⟨old, exactCopy⟩ := safe.pinned version held
        have event : Step rules state _ := .syncPath updated vote bytes ticket
        exact ⟨old, preserves_roles safe event version old exactCopy (.inr ⟨held, held⟩)⟩
    | discard removed current free =>
        obtain ⟨old, exactCopy⟩ := safe.pinned version held
        have event : Step rules state _ := .discard removed current free
        exact ⟨old, preserves_roles safe event version old exactCopy (.inr ⟨held, held⟩)⟩
    | pin pinned vote ready =>
        by_cases same : version = pinned
        · subst version
          exact ⟨vote, ready⟩
        · exact safe.pinned version (by simpa [setSlot, same] using held)
    | unpin dropped =>
        by_cases same : version = dropped
        · simp [setSlot, same] at held
        · exact safe.pinned version (by simpa [setSlot, same] using held)
    | _ => exact safe.pinned version held

theorem arbitrary_staged_traces_keep_pool_and_vote_invariants
    {rules : Rules slots Command Ticket} {first next : State Command Ticket}
    (safe : Sound rules first) (trace : Trace rules first next) : Sound rules next := by
  induction trace with
  | same => exact safe
  | next _ step prior => exact staged_steps_preserve_exact_discoverable_and_paid_votes prior step

omit [DecidableEq Ticket] in
theorem two_distinct_exact_values_need_independent_charges
    {rules : Rules slots Command Ticket} {state : State Command Ticket} (safe : Sound rules state)
    {left right : Vote Command} {a b : Nat} (different : left ≠ right)
    (current : Exact state a left) (candidate : Exact state b right) :
    a ≠ b ∧ Backed state.pool a ∧ Backed state.pool b := by
  refine ⟨?_, (safe.charged a _ current).2.1, (safe.charged b _ candidate).2.1⟩
  intro same
  subst b
  exact different (exactVersion current candidate)

omit [DecidableEq Ticket] in
theorem installed_vote_matches_the_exact_physical_copy
    {state : State Command Ticket} {version : Nat} {vote : Vote Command}
    (ready : CanAccept state version vote) :
    recover (install state version vote) = some vote := by
  have staged : state.copies version = some ⟨vote, true, true⟩ := exact_acceptance ready
  simp [recover, install, staged]

theorem sum_of_required_charges_le_total (cost : Nat → Nat)
    {required paid : List Nat} (distinct : required.Nodup) (coverage : required ⊆ paid) :
    (required.map cost).sum ≤ (paid.map cost).sum := by
  induction required generalizing paid with
  | nil => simp
  | cons version tail prior =>
      have own : version ∈ paid := coverage List.mem_cons_self
      have tailPaid : tail ⊆ paid.erase version := by
        intro remaining member
        have other : remaining ≠ version := by
          intro same
          subst remaining
          exact (List.nodup_cons.mp distinct).1 member
        exact (List.mem_erase_of_ne other).mpr (coverage (List.mem_cons_of_mem _ member))
      have fits := prior (List.nodup_cons.mp distinct).2 tailPaid
      have total := ((List.perm_cons_erase own).map cost).sum_nat
      simp only [List.map_cons, List.sum_cons] at total ⊢
      omega

omit [DecidableEq Ticket] in
theorem all_simultaneously_retained_copies_need_pointwise_capacity
    {rules : Rules slots Command Ticket} {state : State Command Ticket} (safe : Sound rules state)
    (required : List Nat) (distinct : required.Nodup)
    (retained : ∀ version ∈ required, ∃ copy, state.copies version = some copy) (pool : Nat) :
    state.pool.ledger.ordinary pool + SharedExtentAccounting.charges rules.regional.layout pool required ≤
      rules.regional.layout.limit pool := by
  have coverage : required ⊆ state.pool.ledger.debits := by
    intro version member
    obtain ⟨copy, held⟩ := retained version member
    exact (safe.charged version copy held).2.1.1
  have part := sum_of_required_charges_le_total
    (SharedExtentAccounting.allocationBytes rules.regional.layout pool) distinct coverage
  have total := safe.pool.funded.fit pool
  unfold SharedExtentAccounting.Used SharedExtentAccounting.charges at total
  unfold SharedExtentAccounting.charges
  omega

private theorem discarded_version_stays_absent
    {rules : Rules slots Command Ticket} {before after : State Command Ticket} (step : Step rules before after)
    {version : Nat} (issued : version ≤ before.issued) (missing : before.copies version = none) :
    version ≤ after.issued ∧ after.copies version = none := by
  cases step with
  | stage fresh _ newer _ _ _ =>
      have other : version ≠ fresh := by omega
      exact ⟨Nat.le_trans issued (Nat.le_of_lt newer), by simpa [update, setSlot, other] using missing⟩
  | syncBytes updated _ _ ticket =>
      have other : version ≠ updated := by
        intro same
        subst updated
        rw [missing] at ticket
        cases ticket
      exact ⟨issued, by simpa [update, setSlot, other] using missing⟩
  | syncPath updated _ _ ticket =>
      have other : version ≠ updated := by
        intro same
        subst updated
        rw [missing] at ticket
        cases ticket
      exact ⟨issued, by simpa [update, setSlot, other] using missing⟩
  | discard removed =>
      exact ⟨issued, by by_cases same : version = removed <;> simp [update, setSlot, same, missing]⟩
  | _ => exact ⟨issued, missing⟩

theorem a_discarded_scope_cannot_reappear_after_later_steps
    {rules : Rules slots Command Ticket} {first last : State Command Ticket} (trace : Trace rules first last)
    {version : Nat} (issued : version ≤ first.issued) (missing : first.copies version = none) :
    version ≤ last.issued ∧ last.copies version = none := by
  induction trace with
  | same => exact ⟨issued, missing⟩
  | next _ transition prior => exact discarded_version_stays_absent transition prior.1 prior.2

theorem a_pin_keeps_the_same_frames_even_through_a_new_vote
    {rules : Rules slots Command Ticket} {before after : State Command Ticket} (safe : Sound rules before)
    (step : Step rules before after) {version : Nat} {vote : Vote Command}
    (original : Exact before version vote) (held : before.pinned version = true)
    (stillHeld : after.pinned version = true) : Exact after version vote :=
  preserves_roles safe step version vote original (.inr ⟨stillHeld, held⟩)

omit [DecidableEq Ticket] in
theorem staged_replicas_refine_ranked_prefix_agreement
    {Voter : Type} {ledger : PrefixAgreement.Ledger Voter Command}
    (rules : Rules slots Command Ticket) (ballots : PrefixAgreement.BallotRules ledger)
    (replicas : Voter → State Command Ticket)
    (sound : ∀ voter ∈ ledger.members, Sound rules (replicas voter))
    (votes : ∀ voter ∈ ledger.members, ∀ vote, ledger.voted voter vote → (replicas voter).voter.votes vote)
    (replies : ∀ voter ∈ ledger.members, ∀ ballot, ledger.prepared ballot voter = true →
      (replicas voter).voter.replies ballot = some (ledger.report ballot voter))
    {first second : Nat} {left right : List Command}
    (earlier : PrefixAgreement.Chosen ledger first left) (later : PrefixAgreement.Chosen ledger second right) :
    (∀ voter ∈ ledger.members, recover (replicas voter) = (replicas voter).voter.latest) ∧
      (left <+: right ∨ right <+: left) :=
  ⟨fun voter member => exact_reopen_returns_the_last_durable_vote (sound voter member),
    DurableAcceptor.durable_replica_histories_agree ballots (fun voter => (replicas voter).voter)
      (fun voter member => (sound voter member).voter) votes replies earlier later⟩

#print axioms exact_reopen_returns_the_last_durable_vote
#print axioms staged_steps_preserve_exact_discoverable_and_paid_votes
#print axioms arbitrary_staged_traces_keep_pool_and_vote_invariants
#print axioms two_distinct_exact_values_need_independent_charges
#print axioms installed_vote_matches_the_exact_physical_copy
#print axioms all_simultaneously_retained_copies_need_pointwise_capacity
#print axioms a_discarded_scope_cannot_reappear_after_later_steps
#print axioms a_pin_keeps_the_same_frames_even_through_a_new_vote
#print axioms staged_replicas_refine_ranked_prefix_agreement

end StagedVotes
