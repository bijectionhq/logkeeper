import ChosenMove
import RealizedSource

set_option warningAsError true

namespace RealizedProgram

open AllocationVector (Demand Plan Receipt Charged Valid)
open CorePrograms (lineage first)
open MoveProgram (slot target sealed activation)
open ChosenReplay (Rules)
open RealizedSource (Vector Pending Sealed Activated)

def demand (pool : Nat) : Demand := ⟨⟨⟨pool, 1, 7, 1⟩, 1⟩, ⟨7, 1, pool⟩, 1⟩
def plan : Plan 1 := ⟨slot, target, demand 2, [demand 1]⟩
def appendReceipt : Receipt := ⟨demand 2, ⟨2, 1⟩⟩
def recoveryReceipt : Receipt := ⟨demand 1, ⟨1, 1⟩⟩
def vector : Vector := ⟨appendReceipt, [recoveryReceipt]⟩

theorem the_dynamic_plan_projects_to_the_original_funded_intent :
    plan.intent = MoveProgram.intent := by
  have needs : AllocationVector.needs plan.demands = MoveProgram.intent.needs := by
    funext pool
    by_cases first : 1 = pool
    · subst pool; decide
    · by_cases second : 2 = pool
      · subst pool; decide
      · have notFirst : pool ≠ 1 := Ne.symm first
        have notSecond : pool ≠ 2 := Ne.symm second
        simp [AllocationVector.needs, AllocationVector.Plan.demands, AllocationVector.Demand.pool,
          plan, demand, MoveProgram.intent, first, second, notFirst, notSecond]
  change FundedSeal.Intent.mk 1 target (AllocationVector.needs plan.demands) =
    FundedSeal.Intent.mk 1 target MoveProgram.intent.needs
  rw [needs]

structure PoolFixture (pools : Nat → PoolState.Rules Unit) (before : PoolState.Region Unit) : Prop where
  left : PoolState.Admits (pools 2) (before 2) (demand 2).key (demand 2).binding
  right : PoolState.Admits (pools 1) (before 1) (demand 1).key (demand 1).binding
  appendCost : (demand 2).bytes = (pools 2).cost (demand 2).binding
  recoveryCost : (demand 1).bytes = (pools 1).cost (demand 1).binding
  leftIssuance : (before 2).issued = 0
  rightIssuance : (before 1).issued = 0

def bothPrepared (before : PoolState.Region Unit) : PoolState.Region Unit :=
  PoolState.prepareAt (PoolState.prepareAt before 2 (demand 2).key (demand 2).binding)
    1 (demand 1).key (demand 1).binding

theorem the_independent_local_decisions_realize_this_exact_vector
    (pools : Nat → PoolState.Rules Unit) (before : PoolState.Region Unit) (ready : PoolFixture pools before) :
    Valid plan (Charged pools (bothPrepared before)) vector.receipts := by
  let started := PoolState.prepareAt before 2 (demand 2).key (demand 2).binding
  have untouched : started 1 = before 1 := by
    simp [started, PoolState.prepareAt, PoolState.replacePool]
  have subsequent : PoolState.Admits (pools 1) (started 1) (demand 1).key (demand 1).binding := by
    rw [untouched]
    exact ready.right
  have left := (AllocationVector.a_successful_pool_prepare_constructs_the_exact_paid_receipt
    pools before (demand 2) ready.left ready.appendCost).2
  have right := (AllocationVector.a_successful_pool_prepare_constructs_the_exact_paid_receipt
    pools started (demand 1) subsequent ready.recoveryCost).2
  have firstIdentity : (PoolState.allocated (before 2) (demand 2).key (demand 2).binding).identity =
      appendReceipt.extent := by
    simp [PoolState.allocated, PoolState.Row.identity, ready.leftIssuance, appendReceipt, demand]
  have secondIdentity : (PoolState.allocated (started 1) (demand 1).key (demand 1).binding).identity =
      recoveryReceipt.extent := by
    simp [PoolState.allocated, PoolState.Row.identity, untouched, ready.rightIssuance, recoveryReceipt, demand]
  have leftPaid : Charged pools (bothPrepared before) appendReceipt := by
    change Charged pools started ⟨demand 2, (PoolState.allocated (before 2) (demand 2).key (demand 2).binding).identity⟩
      at left
    rw [firstIdentity] at left
    simpa [Charged, bothPrepared, PoolState.prepareAt, PoolState.replacePool, appendReceipt,
      demand, AllocationVector.Demand.pool, started] using left
  have rightPaid : Charged pools (bothPrepared before) recoveryReceipt := by
    change Charged pools (bothPrepared before)
      ⟨demand 1, (PoolState.allocated (started 1) (demand 1).key (demand 1).binding).identity⟩ at right
    rw [secondIdentity] at right
    exact right
  refine ⟨rfl, by decide, by decide, ?_, ?_⟩
  · intro receipt member
    rcases List.mem_cons.mp member with rfl | tail
    · rfl
    · have same : receipt = recoveryReceipt := List.mem_singleton.mp tail
      subst receipt
      rfl
  · intro receipt member
    rcases List.mem_cons.mp member with rfl | tail
    · exact leftPaid
    · exact (List.mem_singleton.mp tail).symm ▸ rightPaid

def pending : Pending 1 Nat := ⟨ChosenMove.reserved, lineage, plan⟩
def sealedWithExtents : Sealed 1 Nat := ⟨sealed, ⟨lineage, MoveProgram.anchor, vector⟩⟩
def installation : RealizedSource.Install 1 Nat Unit := ⟨activation, vector⟩
def modeledAlias : RealizedSource.Alias := fun _ position => position + 5
def active : Activated 1 Nat := ⟨MoveProgram.activated, sealedWithExtents.record, 10, appendReceipt.extent⟩

theorem independent_allocations_seal_and_activate_with_a_lower_physical_serial
    (rules : Rules 1 Nat Unit) (pools : Nat → PoolState.Rules Unit) (before : PoolState.Region Unit)
    (localAdmission : PoolFixture pools before) (paid : CorePrograms.PaidFixture rules)
    (planned : (rules.append.regional.source lineage.stream).plan slot MoveProgram.intent ChosenMove.participants)
    (approve : ∀ pool, 0 < plan.intent.needs pool →
      Valid plan (Charged pools (bothPrepared before)) vector.receipts →
      (rules.append.regional.source lineage.stream).preparedReceipt (AllocationVector.poolReceipt plan pool))
    (installed : MoveProgram.VerifiedMove rules) :
    RealizedSource.reserve rules lineage CorePrograms.committed plan ChosenMove.participants (· = plan) = some pending ∧
    RealizedSource.chooseSeal rules pending first vector (Charged pools (bothPrepared before)) = some sealedWithExtents ∧
    RealizedSource.activate rules modeledAlias sealedWithExtents installation (·.mounted = vector) = some active ∧
    active.physical.serial < CorePrograms.committed.book.latest lineage.stream ∧
    active.image.book.latest lineage.stream = 10 ∧
    active.image.source.core.stream.authority = .active MoveProgram.nextWriter ∧
    active.image.source.core.stream.history = [CorePrograms.entry] ∧
    ∃ results, ReceiptReplay.replay rules lineage MoveProgram.earlier
      (CorePrograms.start ++ [RealizedSource.reserveFrame lineage CorePrograms.committed plan ChosenMove.participants,
        RealizedSource.sealFrame lineage ChosenMove.reserved first plan,
        RealizedSource.installFrame sealedWithExtents installation]) =
        some (⟨active.image, MoveProgram.retainedRows⟩, results) ∧
      ReceiptReplay.lookup lineage True ⟨active.image, MoveProgram.retainedRows⟩ MoveProgram.original =
        .committed MoveProgram.receipt := by
  have valid := the_independent_local_decisions_realize_this_exact_vector pools before localAdmission
  have reserved : ChosenReplay.decide rules lineage CorePrograms.committed
      (RealizedSource.reserveFrame lineage CorePrograms.committed plan ChosenMove.participants) =
      (ChosenMove.reserved, .accepted) := by
    simp only [RealizedSource.reserveFrame, the_dynamic_plan_projects_to_the_original_funded_intent]
    exact ChosenMove.an_exact_plan_is_reserved_at_its_ordered_position rules planned
  have chooseReserve := RealizedSource.accepted_reservation_retains_the_exact_plan rules lineage CorePrograms.committed
    plan ChosenMove.participants (· = plan) rfl (congrArg Prod.snd reserved)
  have full := AllocationVector.an_exact_vector_supplies_the_existing_pointwise_funding valid
    (rules.append.regional.source lineage.stream) approve
  have legacyFull : UnifiedSource.full (rules.append.regional.source lineage.stream)
      (AllocationVector.vectorProjection plan) MoveProgram.intent := by
    rw [← the_dynamic_plan_projects_to_the_original_funded_intent]
    exact full
  have innerSeal : ChosenReplay.decide rules lineage ChosenMove.reserved
      (RealizedSource.sealFrame lineage ChosenMove.reserved first plan) = (sealed, .accepted) :=
    ChosenMove.full_local_receipts_order_the_exact_sealed_source rules (AllocationVector.vectorProjection plan) legacyFull
  have projected : ChosenReplay.decide rules sealedWithExtents.record.lineage sealedWithExtents.image
      (RealizedSource.installFrame sealedWithExtents installation) = (MoveProgram.activated, .accepted) :=
    MoveProgram.the_funded_activation_moves_writer_and_window_with_the_same_exact_history rules installed
  have matched : RealizedSource.Matches modeledAlias sealedWithExtents installation ∧ installation.mounted = vector :=
    ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  refine ⟨by simpa only [reserved, pending] using chooseReserve, ?_, ?_, by decide, rfl, rfl, rfl, ?_⟩
  · unfold RealizedSource.chooseSeal
    split
    · simp only [pending, innerSeal]
      rfl
    · rename_i denied
      exact False.elim (denied valid)
  · simp only [RealizedSource.activate, ite_eq_left matched, projected]
    rfl
  · let reserveFrame := RealizedSource.reserveFrame (Ticket := Unit) lineage CorePrograms.committed plan ChosenMove.participants
    let sealFrame := RealizedSource.sealFrame (Ticket := Unit) lineage ChosenMove.reserved first plan
    let installFrame := RealizedSource.installFrame sealedWithExtents installation
    let records : List (ChosenReplay.Applied 1 Nat Unit) :=
      [⟨reserveFrame, .accepted⟩, ⟨sealFrame, .accepted⟩, ⟨installFrame, .accepted⟩]
    have applyFirst (base next : ChosenReplay.Image 1 Nat) (frame : ChosenReplay.Frame 1 Nat Unit)
        (eligible : ChosenReplay.eligibleFrame lineage base frame)
        (accepts : ChosenReplay.decide rules lineage base frame = (next, .accepted))
        (suffix : List (ChosenReplay.Frame 1 Nat Unit)) :
        ChosenReplay.replay rules lineage base (frame :: suffix) =
          (ChosenReplay.replay rules lineage next suffix).map fun rest => (rest.1, ⟨frame, .accepted⟩ :: rest.2) := by
      simp only [ChosenReplay.replay, ite_eq_left eligible, accepts]
    have replayed : ChosenReplay.replay rules lineage CorePrograms.committed [reserveFrame, sealFrame, installFrame] =
        some (active.image, records) := by
      rw [applyFirst CorePrograms.committed ChosenMove.reserved reserveFrame ⟨rfl, rfl⟩ reserved,
        applyFirst ChosenMove.reserved sealed sealFrame ⟨rfl, rfl⟩ innerSeal,
        applyFirst sealed MoveProgram.activated installFrame ⟨rfl, rfl⟩ projected]
      rfl
    have suffix : ReceiptReplay.replay rules lineage ⟨CorePrograms.committed, MoveProgram.retainedRows⟩
        [reserveFrame, sealFrame, installFrame] = some (⟨active.image, MoveProgram.retainedRows⟩, records) := by
      simp only [ReceiptReplay.replay, replayed]
      rfl
    have boot := MoveProgram.the_common_append_program_populates_its_exact_receipt_row rules paid
    have whole := ReceiptReplay.a_selected_receipt_checkpoint_reconstructs_the_whole_retained_book rules lineage
      MoveProgram.earlier ⟨CorePrograms.committed, MoveProgram.retainedRows⟩ ⟨active.image, MoveProgram.retainedRows⟩
      _ _ boot suffix
    exact ⟨_, whole, ReceiptReplay.the_exact_retained_receipt_is_available_without_appending ⟨trivial, rfl⟩
      (by decide) (by decide) rfl rfl⟩

#print axioms the_dynamic_plan_projects_to_the_original_funded_intent
#print axioms the_independent_local_decisions_realize_this_exact_vector
#print axioms independent_allocations_seal_and_activate_with_a_lower_physical_serial

end RealizedProgram
