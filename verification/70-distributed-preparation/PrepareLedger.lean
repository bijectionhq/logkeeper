import FundedWindowMove

set_option warningAsError true

namespace PrepareLedger

open SnapshotAdmission (setSlot)
open FundedWindowMove (State Rules Key Step Trace Holds layout)

variable {slots : Nat} {Payload Ticket : Type}

abbrev Ledger (state : State slots Payload Ticket) := state.appends.regional.pools.ledger
abbrev Pools (state : State slots Payload Ticket) := state.appends.regional.pools

def reserve (state : State slots Payload Ticket) (version : Nat) : State slots Payload Ticket :=
  let pools := Pools state
  let ledger := Ledger state
  let next := {ledger with
    debits := version :: ledger.debits
    issued := version
    provider := setSlot ledger.provider version ProviderIOClosure.initial
    opening := setSlot ledger.opening version true}
  {state with appends := {state.appends with regional := {state.appends.regional with
    pools := {pools with ledger := next}}}}

def claim (state : State slots Payload Ticket) (version : Nat) (key : Key slots) : State slots Payload Ticket :=
  {state with held := setSlot state.held version (some key)}

def prepare (state : State slots Payload Ticket) (version : Nat) (key : Key slots) :
    State slots Payload Ticket :=
  claim (reserve state version) version key

structure CanReserve (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (version : Nat) : Prop where
  fresh : version = (Ledger state).issued + 1
  empty : (Ledger state).catalog.physical version = false
  pool : PoolIncarnations.Eligible (Pools state) ((layout rules).pool version)
  fits : ∀ pool, SharedExtentAccounting.Used (layout rules) (Ledger state) pool +
    SharedExtentAccounting.allocationBytes (layout rules) pool version ≤ (layout rules).limit pool

theorem a_prepare_allocation_charges_only_the_actual_pool
    (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket) (version pool : Nat) :
    SharedExtentAccounting.Used (layout rules) (Ledger (reserve state version)) pool =
      SharedExtentAccounting.Used (layout rules) (Ledger state) pool +
        SharedExtentAccounting.allocationBytes (layout rules) pool version := by
  simp [reserve, SharedExtentAccounting.Used, SharedExtentAccounting.charges, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

variable [DecidableEq Ticket]

theorem reserve_refines_the_existing_regional_ledger
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {version : Nat}
    (safe : FundedWindowMove.Sound rules state) (allowed : CanReserve rules state version) :
    Step rules state (reserve state version) := by
  have alloc : SharedExtentAccounting.Step (layout rules) rules.append.regional.needs
      rules.append.regional.closeAllowed rules.append.regional.reserve (Ledger state) (Ledger (reserve state version)) :=
    .allocate version allowed.fresh allowed.empty allowed.fits
  have update : RegionalRetirement.PoolStep rules.append.regional (Pools state) .account (Pools (reserve state version)) :=
    .account alloc (by
      intro added present absent
      rcases List.mem_cons.mp present with rfl | old
      · exact allowed.pool
      · exact False.elim (absent old)) (fun _ high => False.elim (Nat.lt_irrefl _ high))
  have regional : RegionalRetirement.Step rules.append.regional state.appends.regional
      (reserve state version).appends.regional :=
    .pool .account update rfl (fun _ _ _ same => same)
  let unchangedHistory : ∀ stream,
      ((reserve state version).appends.regional.streams stream).core.stream.history =
        (state.appends.regional.streams stream).core.stream.history := fun _ => rfl
  have preserved : ∀ old window, state.appends.book.windows old = some window →
      FundedAppend.Backed (reserve state version).appends.regional old := by
    intro old window live
    have current := (safe.windows old window live).1
    have older := safe.regional.pools.funded.known old current.1
    have fresh := allowed.fresh
    change version = state.appends.regional.pools.ledger.issued + 1 at fresh
    have other : old ≠ version := by omega
    exact ⟨List.mem_cons_of_mem _ current.1, by simpa [reserve, setSlot, other] using current.2⟩
  exact .ordinary (.regional regional unchangedHistory preserved)
    (fun old key held => List.mem_cons_of_mem _ (safe.claims old key held).2)
    (fun _ => rfl) (fun _ _ _ already => already)

theorem preparing_an_extent_creates_its_exact_paid_claim
    (rules : Rules slots Payload Ticket) (before : State slots Payload Ticket)
    (key : Key slots) (version : Nat)
    (safe : FundedWindowMove.Sound rules before) (allowed : CanReserve rules before version)
    (member : version ∈ (rules.plan key).extents) (owned : rules.owner version = some key)
    (pending : (FundedWindowMove.source before key).core.pending = some key.move) :
    Trace rules before (prepare before version key) ∧
      (prepare before version key).held version = some key ∧ Holds (prepare before version key) version := by
  have noPriorDebit : ¬ Holds before version := by
    intro charged
    have past := safe.regional.pools.funded.known version charged
    have fresh := allowed.fresh
    change version = before.appends.regional.pools.ledger.issued + 1 at fresh
    omega
  have noClaim : before.held version = none := by
    cases found : before.held version with
    | none => rfl
    | some other => exact False.elim (noPriorDebit (safe.claims version other found).2)
  have noWindow : before.appends.book.windows version = none := by
    cases found : before.appends.book.windows version with
    | none => rfl
    | some window => exact False.elim (noPriorDebit (safe.windows version window found).1.1)
  have charged : Holds (reserve before version) version := List.mem_cons_self
  have events : Trace rules before (prepare before version key) :=
    .next (.next (.same _) (reserve_refines_the_existing_regional_ledger safe allowed))
      (.claim key version member owned charged noClaim noWindow pending)
  exact ⟨events, by simp [prepare, claim, setSlot], charged⟩

private theorem join {rules : Rules slots Payload Ticket} {start middle last : State slots Payload Ticket}
    (left : Trace rules start middle) (right : Trace rules middle last) : Trace rules start last := by
  induction right with
  | same => exact left
  | next _ step prior => exact .next prior step

theorem the_two_independent_preparations_supply_the_complete_exact_vector
    (rules : Rules slots Payload Ticket) (before : State slots Payload Ticket)
    (key : Key slots) (first second : Nat)
    (safe : FundedWindowMove.Sound rules before)
    (allowedFirst : CanReserve rules before first)
    (allowedSecond : CanReserve rules (prepare before first key) second)
    (plan : (rules.plan key).extents = [first, second])
    (bothOwned : rules.owner first = some key ∧ rules.owner second = some key)
    (pending : (FundedWindowMove.source before key).core.pending = some key.move) :
    let after := prepare (prepare before first key) second key
    Trace rules before after ∧ FundedWindowMove.Complete rules after key := by
  have inFirst : first ∈ (rules.plan key).extents := by simp [plan]
  have inSecond : second ∈ (rules.plan key).extents := by simp [plan]
  obtain ⟨started, heldFirst, paidFirst⟩ := preparing_an_extent_creates_its_exact_paid_claim
    rules before key first safe allowedFirst inFirst bothOwned.1 pending
  have safeAgain := FundedWindowMove.arbitrary_competing_moves_and_appends_preserve_the_regional_bounds safe started
  obtain ⟨finished, heldSecond, paidSecond⟩ := preparing_an_extent_creates_its_exact_paid_claim
    rules (prepare before first key) key second safeAgain allowedSecond inSecond bothOwned.2 pending
  have separated : first ≠ second := by
    have advances : second = first + 1 := allowedSecond.fresh
    omega
  refine ⟨join started finished, ⟨by simp [plan, separated], ?_, ?_, ?_⟩⟩
  · intro query wanted
    simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at wanted
    rcases wanted with rfl | rfl
    · exact bothOwned.1
    · exact bothOwned.2
  · intro query wanted
    simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at wanted
    rcases wanted with rfl | rfl
    · simp [prepare, claim, reserve, setSlot, separated]
    · exact heldSecond
  · intro query wanted
    simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at wanted
    rcases wanted with rfl | rfl
    · exact List.mem_cons_of_mem _ paidFirst
    · exact paidSecond

def LocalProof (rules : Rules slots Payload Ticket) (state : State slots Payload Ticket)
    (key : Key slots) (pool : Nat) : Prop :=
  ∀ extent ∈ (rules.plan key).extents, (layout rules).pool extent = pool →
    rules.owner extent = some key ∧ state.held extent = some key ∧ Holds state extent

omit [DecidableEq Ticket] in
theorem a_complete_preparation_carries_its_exact_local_proof
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    (complete : FundedWindowMove.Complete rules state key) (pool : Nat) :
    LocalProof rules state key pool :=
  fun extent planned _ => ⟨complete.owners extent planned, complete.held extent planned, complete.paid extent planned⟩

omit [DecidableEq Ticket] in
theorem signed_local_results_authorize_the_existing_seal
    {rules : Rules slots Payload Ticket} {state : State slots Payload Ticket} {key : Key slots}
    {received : List (FundedSeal.Receipt Nat)}
    (complete : FundedWindowMove.Complete rules state key)
    (certify : ∀ pool, 0 < (FundedWindowMove.intent rules key).needs pool →
      LocalProof rules state key pool →
      FundedWindowMove.PreparedReceipt rules key pool ∈ received ∧
        (rules.append.regional.source key.stream).preparedReceipt (FundedWindowMove.PreparedReceipt rules key pool)) :
    FundedWindowMove.ExactReceipts rules key received ∧
      UnifiedSource.full (rules.append.regional.source key.stream) received (FundedWindowMove.intent rules key) := by
  have exactReceipts : FundedWindowMove.ExactReceipts rules key received :=
    fun pool needed => certify pool needed (a_complete_preparation_carries_its_exact_local_proof complete pool)
  exact ⟨exactReceipts, FundedWindowMove.the_existing_seal_uses_the_exact_pointwise_receipts exactReceipts⟩

#print axioms a_prepare_allocation_charges_only_the_actual_pool
#print axioms reserve_refines_the_existing_regional_ledger
#print axioms preparing_an_extent_creates_its_exact_paid_claim
#print axioms the_two_independent_preparations_supply_the_complete_exact_vector
#print axioms a_complete_preparation_carries_its_exact_local_proof
#print axioms signed_local_results_authorize_the_existing_seal

end PrepareLedger
