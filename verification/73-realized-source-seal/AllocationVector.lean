import PoolState
import UnifiedSource

set_option warningAsError true

namespace AllocationVector

open ChannelLifecycle (Key)
open RegistrationRecovery (Binding)
open PoolState (Identity)

variable {slots : Nat} {Payload Ticket : Type}

structure Demand where
  key : Key
  binding : Binding
  bytes : Nat
  deriving DecidableEq

def Demand.pool (demand : Demand) : Nat := demand.key.handle.custodian

structure Plan (slots : Nat) where
  move : SourceOutcomes.Key slots
  target : Kernel.Placement
  append : Demand
  recovery : List Demand

def Plan.demands (plan : Plan slots) : List Demand := plan.append :: plan.recovery

def needs (demands : List Demand) (pool : Nat) : Nat :=
  (demands.map fun demand => if demand.pool = pool then demand.bytes else 0).sum

def Plan.intent (plan : Plan slots) : FundedSeal.Intent Nat :=
  ⟨plan.move.serial, plan.target, needs plan.demands⟩

structure Receipt where
  demand : Demand
  extent : Identity
  deriving DecidableEq

def Charged (rules : Nat → PoolState.Rules Ticket) (pools : PoolState.Region Ticket)
    (receipt : Receipt) : Prop :=
  let pool := receipt.demand.pool
  let current := pools pool
  receipt.extent.pool = pool ∧ receipt.demand.bytes = (rules pool).cost receipt.demand.binding ∧
    current.gate.grants receipt.demand.key = some receipt.demand.binding ∧
    PoolState.Holds current receipt.extent receipt.demand.key receipt.demand.binding

structure Valid (plan : Plan slots) (authentic : Receipt → Prop) (receipts : List Receipt) : Prop where
  exactDemands : receipts.map Receipt.demand = plan.demands
  distinctScopes : (plan.demands.map Demand.key).Nodup
  distinctExtents : (receipts.map Receipt.extent).Nodup
  samePool : ∀ receipt ∈ receipts, receipt.extent.pool = receipt.demand.pool
  paid : ∀ receipt ∈ receipts, authentic receipt

theorem the_first_exact_receipt_is_for_the_append_role
    {plan : Plan slots} {authentic : Receipt → Prop} {receipts : List Receipt}
    (valid : Valid plan authentic receipts) :
    ∃ first rest, receipts = first :: rest ∧ first.demand = plan.append ∧
      rest.map Receipt.demand = plan.recovery ∧ authentic first := by
  cases receipts with
  | nil =>
      have impossible := valid.exactDemands
      simp [Plan.demands] at impossible
  | cons first rest =>
      have shape := valid.exactDemands
      simp [Plan.demands] at shape
      exact ⟨first, rest, rfl, shape.1, shape.2, valid.paid first List.mem_cons_self⟩

theorem a_successful_pool_prepare_constructs_the_exact_paid_receipt
    [DecidableEq Ticket] (rules : Nat → PoolState.Rules Ticket) (region : PoolState.Region Ticket)
    (demand : Demand) (allowed : PoolState.Admits (rules demand.pool) (region demand.pool) demand.key demand.binding)
    (cost : demand.bytes = (rules demand.pool).cost demand.binding) :
    let row := PoolState.allocated (region demand.pool) demand.key demand.binding
    let receipt : Receipt := ⟨demand, row.identity⟩
    PoolState.Step (rules demand.pool) (region demand.pool)
      (PoolState.prepare (region demand.pool) demand.key demand.binding) ∧
    Charged rules (PoolState.prepareAt region demand.pool demand.key demand.binding) receipt := by
  refine ⟨.prepare demand.key demand.binding allowed, rfl, cost, ?_, ?_⟩
  · simp [PoolState.prepareAt, PoolState.replacePool, PoolState.prepare, ChannelLifecycle.setGrant]
  · exact ⟨PoolState.allocated (region demand.pool) demand.key demand.binding,
      by simp [PoolState.prepareAt, PoolState.replacePool, PoolState.prepare], rfl, rfl, rfl⟩

theorem all_realized_extents_remain_distinct
    {plan : Plan slots} {authentic : Receipt → Prop} {receipts : List Receipt}
    (valid : Valid plan authentic receipts) (head : Receipt) (tail : List Receipt)
    (decomposed : receipts = head :: tail) :
    ∀ other ∈ tail, other.extent ≠ head.extent := by
  have unique := valid.distinctExtents
  rw [decomposed, List.map_cons] at unique
  intro other member same
  exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨other, member, same⟩)

def poolReceipt (plan : Plan slots) (pool : Nat) : FundedSeal.Receipt Nat :=
  ⟨plan.intent, pool, plan.intent.needs pool⟩

def vectorProjection (plan : Plan slots) : List (FundedSeal.Receipt Nat) :=
  plan.demands.map fun demand => poolReceipt plan demand.pool

private theorem positive_pool_has_a_demand (demands : List Demand) (pool : Nat)
    (positive : 0 < needs demands pool) : ∃ demand ∈ demands, demand.pool = pool := by
  induction demands with
  | nil => simp [needs] at positive
  | cons head tail prior =>
      by_cases here : head.pool = pool
      · exact ⟨head, List.mem_cons_self, here⟩
      · have remaining : 0 < needs tail pool := by
          simpa [needs, here] using positive
        obtain ⟨demand, member, same⟩ := prior remaining
        exact ⟨demand, List.mem_cons_of_mem _ member, same⟩

theorem an_exact_vector_supplies_the_existing_pointwise_funding
    {plan : Plan slots} {authentic : Receipt → Prop} {receipts : List Receipt}
    (valid : Valid plan authentic receipts) (rules : UnifiedSource.Rules slots Nat Payload Ticket)
    (approve : ∀ pool, 0 < plan.intent.needs pool → Valid plan authentic receipts →
      rules.preparedReceipt (poolReceipt plan pool)) :
    UnifiedSource.full rules (vectorProjection plan) plan.intent := by
  intro pool positive
  obtain ⟨demand, member, same⟩ := positive_pool_has_a_demand plan.demands pool positive
  exact ⟨poolReceipt plan pool, ⟨List.mem_map.mpr ⟨demand, member, congrArg (poolReceipt plan) same⟩,
    approve pool positive valid⟩, rfl, rfl, rfl⟩

theorem an_exact_receipt_cannot_substitute_another_scope_at_equal_price
    {plan : Plan slots} {authentic : Receipt → Prop} {receipt : Receipt} {rest : List Receipt}
    (valid : Valid plan authentic (receipt :: rest)) :
    receipt.demand.key = plan.append.key := by
  have exactDemands := valid.exactDemands
  exact congrArg Demand.key (List.cons.inj exactDemands).1

#print axioms the_first_exact_receipt_is_for_the_append_role
#print axioms a_successful_pool_prepare_constructs_the_exact_paid_receipt
#print axioms all_realized_extents_remain_distinct
#print axioms an_exact_vector_supplies_the_existing_pointwise_funding
#print axioms an_exact_receipt_cannot_substitute_another_scope_at_equal_price

end AllocationVector
