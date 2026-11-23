import AtomicPublication
import ReadIndexProof

set_option warningAsError true

namespace OrderedReplyAdmission

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Route Barrier)
open OrderedReadReplay (Rules Image Frame Delivery advance decideDelivery deliveryFrame position replay authority)
open AtomicPublication (JournalScope ChosenDelivery)
open RecoverableRead (Permit Row)

variable {width slots capacity : Nat} {Payload Ticket Voter Signature : Type}

noncomputable def planDelivery (before : Image slots capacity Payload) (call : Invocation) :
    Option (Delivery capacity) := do
  let permit ← (List.finRange capacity).findSome? (RecoverableRead.permitAt before.reads call)
  let basis ← before.reads.view.snapshots permit.serial
  some ⟨call, permit, basis⟩

theorem a_server_can_name_the_exact_live_basis_without_the_callers_old_permit
    (before : Image slots capacity Payload) (slot : Fin capacity) (row : Row)
    (found : before.reads.rows slot = some row)
    (unique : RecoverableRead.UniqueRows (fun item => item.reply.invocation) before.reads.rows)
    (basis : SnapshotAdmission.Basis) (held : before.reads.view.snapshots row.serial = some basis) :
    planDelivery before row.reply.invocation = some ⟨row.reply.invocation, ⟨slot, row.serial⟩, basis⟩ := by
  have planned := RecoverableRead.the_exact_live_permit_is_found_by_its_invocation before.reads slot row found unique
  simp [planDelivery, planned, held]

theorem the_ordered_delivery_requires_the_exact_live_result_and_paid_basis
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) (reply : Barrier)
    (allowed : decideDelivery rules lineage before request evidence = .delivery reply) :
    OrderedReadReplay.EligibleDelivery lineage before request ∧ OrderedReadReplay.PaidDelivery rules lineage request evidence ∧
    ∃ row, before.reads.rows request.permit.slot = some row ∧ row.serial = request.permit.serial ∧
      row.reply = reply ∧ reply.invocation = request.call ∧
      before.reads.view.snapshots request.permit.serial = some request.basis ∧ request.basis.stop = reply.cut := by
  cases found : before.reads.rows request.permit.slot with
  | none => simp [decideDelivery, found] at allowed
  | some row =>
      simp only [decideDelivery, found] at allowed
      split at allowed
      · next guard =>
          cases allowed
          exact ⟨guard.1, guard.2.2, row, rfl,
            OrderedReadReplay.delivery_checks_the_exact_permit_serial _ _ _ guard.2.1,
            rfl, guard.2.1.2.1, guard.2.1.2.2.1, guard.2.1.2.2.2⟩
      · simp at allowed

theorem the_committed_delivery_does_not_consume_another_invocation_or_change_the_read_book
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) :
    let after := (OrderedReadReplay.decide rules lineage before (.deliver request evidence)).1
    after.reads = before.reads ∧ after.readThrough = before.readThrough ∧
      authority after = authority before ∧ position after = position before + 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem an_exact_ordered_close_prevents_later_delivery_from_its_released_slot
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity Payload) (permit : Permit capacity) (stop : Ticket)
    (past : Barrier → Prop) (sound : RecoverableRead.SoundFor width rules.snapshot past before.reads)
    (closed : OrderedReadReplay.decide rules lineage before (.close permit stop) = (after, .closed))
    (request : Delivery capacity) (evidence : Ticket) (sameSlot : request.permit.slot = permit.slot) :
    decideDelivery rules lineage after request evidence = .refused := by
  have released := (OrderedReadReplay.an_applied_close_clears_its_result_and_hold_at_one_ordered_position
    rules lineage before after permit stop past sound closed).2.2.2.1
  simp [decideDelivery, sameSlot, released]

theorem a_recycled_slots_serial_cannot_authorize_a_different_original_borrow
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (row : Row) (evidence : Ticket)
    (found : before.reads.rows request.permit.slot = some row) (stale : row.serial ≠ request.permit.serial) :
    decideDelivery rules lineage before request evidence = .refused := by
  have refused : ¬ OrderedReadReplay.MatchesDelivery before.reads request row :=
    fun matched => stale (OrderedReadReplay.delivery_checks_the_exact_permit_serial _ _ _ matched)
  simp [decideDelivery, found, refused]

theorem an_overtaken_delivery_frame_cannot_authorize_at_a_later_position
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) (earlier : Nat) (overtaken : earlier ≠ position before + 1) :
    OrderedReadReplay.step rules lineage before ⟨lineage, earlier, .deliver request evidence⟩ = none := by
  simp [OrderedReadReplay.step, OrderedReadReplay.Eligible, overtaken]

theorem the_same_paid_borrow_can_be_reframed_if_the_original_basis_is_still_live
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) (row : Row)
    (same : request.call.lineage = lineage) (openScope : OrderedReadReplay.deliveryOpen (authority before) = true)
    (found : before.reads.rows request.permit.slot = some row)
    (exact : OrderedReadReplay.MatchesDelivery before.reads request row)
    (paid : OrderedReadReplay.PaidDelivery rules lineage request evidence) :
    let frame := deliveryFrame lineage before request evidence
    OrderedReadReplay.step rules lineage before frame = some (advance before) ∧
      (OrderedReadReplay.decide rules lineage before frame.command).2 = .delivery row.reply := by
  have eligible : OrderedReadReplay.EligibleDelivery lineage before request := ⟨same, openScope⟩
  simp [deliveryFrame, OrderedReadReplay.step, OrderedReadReplay.Eligible, OrderedReadReplay.decide,
    decideDelivery, found, eligible, exact, paid]

theorem a_sealed_predecessor_cannot_authorize_a_new_delivery
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) (target : Kernel.Placement) (writer : Kernel.Writer)
    (sealed : authority before = .sealed target writer) :
    decideDelivery rules lineage before request evidence = .refused := by
  have refuses : ¬ OrderedReadReplay.EligibleDelivery lineage before request := by
    simp [OrderedReadReplay.EligibleDelivery, sealed, OrderedReadReplay.deliveryOpen]
  cases found : before.reads.rows request.permit.slot <;> simp [decideDelivery, found, refuses]

theorem a_live_original_result_can_be_authorized_at_its_retired_current_journal
    (rules : Rules width slots capacity Payload Ticket) (lineage : Lineage) (before : Image slots capacity Payload)
    (request : Delivery capacity) (evidence : Ticket) (row : Row)
    (retired : authority before = .retired) (same : request.call.lineage = lineage)
    (found : before.reads.rows request.permit.slot = some row)
    (exact : OrderedReadReplay.MatchesDelivery before.reads request row)
    (paid : OrderedReadReplay.PaidDelivery rules lineage request evidence) :
    decideDelivery rules lineage before request evidence = .delivery row.reply := by
  simp [decideDelivery, found, exact, paid, OrderedReadReplay.EligibleDelivery, same, retired, OrderedReadReplay.deliveryOpen]

theorem a_fresh_read_index_covers_a_close_chosen_before_the_probe
    {members : List Voter} {stores : ReadIndexProof.Stores Voter (Frame slots capacity Payload Ticket)}
    {call : ReadIndexProof.Invocation} {round : ReadIndexProof.Round Voter (Frame slots capacity Payload Ticket)}
    (checked : ReadIndexProof.Evidence members stores call round)
    (keeps : ReadIndexProof.MonotoneWithinScope stores) (closedAt : Nat) (beforeOpen : closedAt ≤ round.opened)
    (closedPrefix : List (Frame slots capacity Payload Ticket))
    (durable : ReadIndexProof.DurableBasis members stores round.scope closedAt closedPrefix)
    (applied : List (Frame slots capacity Payload Ticket)) (covers : round.target.length ≤ applied.length) :
    closedPrefix.length ≤ applied.length :=
  Nat.le_trans (ReadIndexProof.sampled_maximum_covers_prior_choice checked keeps beforeOpen durable) covers

theorem a_delivery_grant_comes_from_an_exact_chosen_and_successfully_applied_control_frame
    {rules : Rules width slots capacity Payload Ticket}
    {journal : JournalScope Voter slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (accepted : ChosenDelivery rules journal origin) :
    let frame := deliveryFrame journal.lineage accepted.before accepted.request accepted.evidence
    PrefixAgreement.Chosen journal.ledger accepted.ballot (accepted.history ++ [frame]) ∧
    frame.position = position accepted.before + 1 ∧
    replay rules journal.lineage origin (accepted.history ++ [frame]) = some (advance accepted.before) := by
  let frame := deliveryFrame journal.lineage accepted.before accepted.request accepted.evidence
  refine ⟨accepted.chosen, rfl, ?_⟩
  have eligible : OrderedReadReplay.Eligible journal.lineage accepted.before frame := ⟨rfl, rfl⟩
  have stepped : OrderedReadReplay.step rules journal.lineage accepted.before frame = some (advance accepted.before) := by
    simp only [OrderedReadReplay.step, ite_eq_left eligible]
    rfl
  change replay rules journal.lineage origin (accepted.history ++ [frame]) = some (advance accepted.before)
  rw [OrderedReadReplay.replay_after_a_certified_combined_base rules journal.lineage accepted.history [frame] accepted.applied]
  change (OrderedReadReplay.step rules journal.lineage accepted.before frame).bind some = some (advance accepted.before)
  simp [stepped]

theorem a_chosen_refusal_cannot_make_a_reply_token
    (rules : Rules width slots capacity Payload Ticket)
    (journal : JournalScope Voter slots capacity Payload Ticket) (origin before : Image slots capacity Payload)
    (history : List (Frame slots capacity Payload Ticket)) (request : Delivery capacity) (evidence : Ticket) (ballot : Nat)
    (applied : replay rules journal.lineage origin history = some before)
    (chosen : PrefixAgreement.Chosen journal.ledger ballot
      (history ++ [deliveryFrame journal.lineage before request evidence]))
    (refused : decideDelivery rules journal.lineage before request evidence = .refused) :
    AtomicPublication.authorizeDelivery rules journal origin history before request evidence ballot applied chosen = none := by
  simp [AtomicPublication.authorizeDelivery, refused]

theorem an_authorized_receipt_finishes_with_the_original_paid_use_without_calling_the_old_journal
    {rules : Rules width slots capacity Payload Ticket}
    {journal : JournalScope Voter slots capacity Payload Ticket} {origin : Image slots capacity Payload}
    (accepted : ChosenDelivery rules journal origin) (sign : Route → EnvelopeCodec.Bytes → Signature)
    (held : Invocation → Permit capacity → SnapshotAdmission.Basis → Ticket → Prop)
    (canFinish : held accepted.request.call accepted.request.permit accepted.request.basis accepted.evidence) :
    let body := AppliedBarrierReceipt.encode width accepted.reply
    AtomicPublication.finishReply (AtomicPublication.beginChosenReply accepted sign) held =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf accepted.reply.invocation) body⟩ := by
  obtain ⟨_, _, _, _, _, _, invocation, _, _⟩ :=
    the_ordered_delivery_requires_the_exact_live_result_and_paid_basis
      rules journal.lineage accepted.before accepted.request accepted.evidence accepted.reply accepted.accepted
  simp [AtomicPublication.finishReply, AtomicPublication.beginChosenReply, canFinish, invocation]

#print axioms a_server_can_name_the_exact_live_basis_without_the_callers_old_permit
#print axioms the_ordered_delivery_requires_the_exact_live_result_and_paid_basis
#print axioms the_committed_delivery_does_not_consume_another_invocation_or_change_the_read_book
#print axioms an_exact_ordered_close_prevents_later_delivery_from_its_released_slot
#print axioms a_recycled_slots_serial_cannot_authorize_a_different_original_borrow
#print axioms an_overtaken_delivery_frame_cannot_authorize_at_a_later_position
#print axioms the_same_paid_borrow_can_be_reframed_if_the_original_basis_is_still_live
#print axioms a_sealed_predecessor_cannot_authorize_a_new_delivery
#print axioms a_live_original_result_can_be_authorized_at_its_retired_current_journal
#print axioms a_fresh_read_index_covers_a_close_chosen_before_the_probe
#print axioms a_delivery_grant_comes_from_an_exact_chosen_and_successfully_applied_control_frame
#print axioms a_chosen_refusal_cannot_make_a_reply_token
#print axioms an_authorized_receipt_finishes_with_the_original_paid_use_without_calling_the_old_journal

end OrderedReplyAdmission
