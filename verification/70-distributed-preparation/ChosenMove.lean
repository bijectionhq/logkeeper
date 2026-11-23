import PrepareLedger
import MoveProgram

set_option warningAsError true

namespace ChosenMove

open CorePrograms (committed lineage first frame entry)
open CoreReference (stream)
open MoveProgram (slot intent sealed retainedRows earlier activationFrame nextWriter original changed receipt)
open ChosenReplay (Rules Image Frame Applied)

def participants : List (SettlementComposition.Participant Nat) := [.target, .pool 1, .pool 2]
def pendingRow : SourceOutcomes.Row (FundedSeal.Intent Nat) (SettlementComposition.Participant Nat) :=
  ⟨1, intent, none, participants⟩
def reserved : Image 1 Nat :=
  let book := { (SourceOutcomes.setRow committed.source.core.book slot.slot (some pendingRow)) with issued := 1 }
  {committed with source := ⟨{committed.source.core with pending := some slot, book}, 3⟩}
def reserveFrame : Frame 1 Nat Unit := frame 3 (.source (.reserve slot intent participants))
def sealFrame (received : List (FundedSeal.Receipt Nat)) : Frame 1 Nat Unit :=
  frame 4 (.source (.fundedSeal first slot received))

theorem an_exact_plan_is_reserved_at_its_ordered_position
    (rules : Rules 1 Nat Unit) (plan : (rules.append.regional.source lineage.stream).plan slot intent participants) :
    ChosenReplay.decide rules lineage committed reserveFrame = (reserved, .accepted) := by
  have outcome : UnifiedSource.decide (rules.append.regional.limits lineage.stream)
      (rules.append.regional.source lineage.stream) committed.source.core (committed.source.position + 1)
      (.reserve slot intent participants) = (reserved.source.core, .accepted) := by
    simp only [UnifiedSource.decide]
    split
    · rfl
    · rename_i denied
      exact False.elim (denied ⟨⟨first, rfl⟩, rfl, rfl, rfl, rfl, plan⟩)
  have unchanged : (UnifiedSource.decide (rules.append.regional.limits lineage.stream)
      (rules.append.regional.source lineage.stream) committed.source.core (committed.source.position + 1)
      (.reserve slot intent participants)).1.stream.history = committed.source.core.stream.history := by
    rw [outcome]
    rfl
  simp only [ChosenReplay.decide, reserveFrame, frame, ite_eq_left unchanged, outcome]
  rfl

theorem full_local_receipts_order_the_exact_sealed_source
    (rules : Rules 1 Nat Unit) (received : List (FundedSeal.Receipt Nat))
    (funded : UnifiedSource.full (rules.append.regional.source lineage.stream) received intent) :
    ChosenReplay.decide rules lineage reserved (sealFrame received) = (sealed, .accepted) := by
  have ready : UnifiedSource.Ready reserved.source.core slot pendingRow := ⟨rfl, rfl, rfl⟩
  have outcome : UnifiedSource.decide (rules.append.regional.limits lineage.stream)
      (rules.append.regional.source lineage.stream) reserved.source.core (reserved.source.position + 1)
      (.fundedSeal first slot received) = (sealed.source.core, .accepted) := by
    rw [UnifiedSource.decide_funded_seal_accepts_the_exact_pending_row _ _ _ _ _ _ _ _
      ready rfl (by decide) (by decide) funded]
    apply congrArg (fun core => (core, UnifiedSource.Reply.accepted))
    have exactRows : (UnifiedSource.terminal reserved.source.core slot pendingRow .committed).book.rows =
        sealed.source.core.book.rows := by
      funext index
      have same : index = slot.slot := Subsingleton.elim _ _
      subst index
      rfl
    have exactBook : (UnifiedSource.terminal reserved.source.core slot pendingRow .committed).book =
        sealed.source.core.book := by
      exact congrArg (SourceOutcomes.Book.mk 1) exactRows
    change UnifiedSource.Core.mk sealed.source.core.stream
      (UnifiedSource.terminal reserved.source.core slot pendingRow .committed).book
      none sealed.source.core.handoff = sealed.source.core
    rw [exactBook]
    rfl
  have unchanged : (UnifiedSource.decide (rules.append.regional.limits lineage.stream)
      (rules.append.regional.source lineage.stream) reserved.source.core (reserved.source.position + 1)
      (.fundedSeal first slot received)).1.stream.history = reserved.source.core.stream.history := by
    rw [outcome]
    rfl
  simp only [ChosenReplay.decide, sealFrame, frame, ite_eq_left unchanged, outcome]
  rfl

theorem one_chosen_history_funds_appends_moves_and_recovers_the_exact_receipt
    (rules : Rules 1 Nat Unit) (paid : CorePrograms.PaidFixture rules)
    (plan : (rules.append.regional.source lineage.stream).plan slot intent participants)
    (received : List (FundedSeal.Receipt Nat))
    (funded : UnifiedSource.full (rules.append.regional.source lineage.stream) received intent)
    (installed : MoveProgram.VerifiedMove rules) :
    ∃ final responses,
      ReceiptReplay.replay rules lineage earlier
        (CorePrograms.start ++ [reserveFrame, sealFrame received, activationFrame]) = some (final, responses) ∧
      (stream final.image).authority = .active nextWriter ∧ (stream final.image).history = [entry] ∧
      final.image.book.latest lineage.stream = 10 ∧ Kernel.barrier (stream final.image) nextWriter = some 1 ∧
      ReceiptReplay.lookup lineage True final original = .committed receipt ∧
      ReceiptReplay.lookup lineage True final changed = .conflict := by
  let reserveReply : Applied 1 Nat Unit := ⟨reserveFrame, .accepted⟩
  let sealReply : Applied 1 Nat Unit := ⟨sealFrame received, .accepted⟩
  have nextReserve : ChosenReplay.eligibleFrame lineage committed reserveFrame := ⟨rfl, rfl⟩
  have nextSeal : ChosenReplay.eligibleFrame lineage reserved (sealFrame received) := ⟨rfl, rfl⟩
  have reservedChosen := an_exact_plan_is_reserved_at_its_ordered_position rules plan
  have eligibleAfterReserve : ChosenReplay.eligibleFrame lineage
      (ChosenReplay.decide rules lineage committed reserveFrame).1 (sealFrame received) := by
    rw [reservedChosen]
    exact nextSeal
  have ordered : ChosenReplay.replay rules lineage committed [reserveFrame, sealFrame received] =
      some (sealed, [reserveReply, sealReply]) := by
    simp only [ChosenReplay.replay, ite_eq_left nextReserve, ite_eq_left eligibleAfterReserve,
      reservedChosen,
      full_local_receipts_order_the_exact_sealed_source rules received funded, Option.map_some]
    rfl
  have moved : ReceiptReplay.replay rules lineage ⟨committed, retainedRows⟩ [reserveFrame, sealFrame received] =
      some (⟨sealed, retainedRows⟩, [reserveReply, sealReply]) := by
    simp only [ReceiptReplay.replay, ordered]
    rfl
  obtain ⟨final, replies, recovered, accepted⟩ :=
    MoveProgram.a_successor_recovers_the_original_reply_and_its_cut_without_another_append rules installed
  have exactSuffix := ReceiptReplay.a_selected_receipt_checkpoint_reconstructs_the_whole_retained_book
    rules lineage ⟨committed, retainedRows⟩ ⟨sealed, retainedRows⟩ final _ _ moved recovered
  have booted := MoveProgram.the_common_append_program_populates_its_exact_receipt_row rules paid
  have exactHistory := ReceiptReplay.a_selected_receipt_checkpoint_reconstructs_the_whole_retained_book
    rules lineage earlier ⟨committed, retainedRows⟩ final _ _ booted exactSuffix
  exact ⟨final, _, exactHistory, accepted⟩

def moveKey : FundedWindowMove.Key 1 := ⟨lineage.stream, slot⟩

theorem two_paid_pool_preparations_reach_the_successor_and_original_reply
    (rules : Rules 1 Nat Unit) (funding : FundedWindowMove.Rules 1 Nat Unit)
    (before : FundedWindowMove.State 1 Nat Unit) (firstExtent secondExtent : Nat)
    (commonRules : funding.append = rules.append)
    (sameSource : FundedWindowMove.source before moveKey = reserved.source)
    (sameWindow : (funding.plan moveKey).window = MoveProgram.newGrant.version)
    (sameIntent : FundedWindowMove.intent funding moveKey = intent)
    (extents : (funding.plan moveKey).extents = [firstExtent, secondExtent])
    (owners : funding.owner firstExtent = some moveKey ∧ funding.owner secondExtent = some moveKey)
    (safe : FundedWindowMove.Sound funding before)
    (roomFirst : PrepareLedger.CanReserve funding before firstExtent)
    (roomSecond : PrepareLedger.CanReserve funding (PrepareLedger.prepare before firstExtent moveKey) secondExtent)
    (paid : CorePrograms.PaidFixture rules)
    (plan : (rules.append.regional.source lineage.stream).plan slot intent participants)
    (installed : MoveProgram.VerifiedMove rules)
    (received : List (FundedSeal.Receipt Nat))
    (certify : ∀ pool, 0 < (FundedWindowMove.intent funding moveKey).needs pool →
      PrepareLedger.LocalProof funding
        (PrepareLedger.prepare (PrepareLedger.prepare before firstExtent moveKey) secondExtent moveKey) moveKey pool →
      FundedWindowMove.PreparedReceipt funding moveKey pool ∈ received ∧
        (funding.append.regional.source moveKey.stream).preparedReceipt
          (FundedWindowMove.PreparedReceipt funding moveKey pool)) :
    FundedWindowMove.Trace funding before
      (PrepareLedger.prepare (PrepareLedger.prepare before firstExtent moveKey) secondExtent moveKey) ∧
    ∃ final responses,
      ReceiptReplay.replay rules lineage earlier
        (CorePrograms.start ++ [reserveFrame, sealFrame received, activationFrame]) = some (final, responses) ∧
      (stream final.image).authority = .active nextWriter ∧ (stream final.image).history = [entry] ∧
      final.image.book.latest lineage.stream = (funding.plan moveKey).window ∧
      Kernel.barrier (stream final.image) nextWriter = some 1 ∧
      ReceiptReplay.lookup lineage True final original = .committed receipt ∧
      ReceiptReplay.lookup lineage True final changed = .conflict := by
  have pending : (FundedWindowMove.source before moveKey).core.pending = some moveKey.move := by
    rw [sameSource]
    rfl
  obtain ⟨prepares, complete⟩ :=
    PrepareLedger.the_two_independent_preparations_supply_the_complete_exact_vector funding before moveKey
      firstExtent secondExtent safe roomFirst roomSecond extents owners pending
  have funded := (PrepareLedger.signed_local_results_authorize_the_existing_seal complete certify).2
  rw [commonRules, sameIntent] at funded
  obtain ⟨final, replies, applied, active, history, window, cut, originalResult, changedResult⟩ :=
    one_chosen_history_funds_appends_moves_and_recovers_the_exact_receipt rules paid plan received funded installed
  exact ⟨prepares, final, replies, applied, active, history, window.trans sameWindow.symm, cut,
    originalResult, changedResult⟩

#print axioms an_exact_plan_is_reserved_at_its_ordered_position
#print axioms full_local_receipts_order_the_exact_sealed_source
#print axioms one_chosen_history_funds_appends_moves_and_recovers_the_exact_receipt
#print axioms two_paid_pool_preparations_reach_the_successor_and_original_reply

end ChosenMove
