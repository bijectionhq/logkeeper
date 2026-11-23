import RetainedDelivery

set_option warningAsError true

namespace AtomicReadCapture

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Barrier)
open RecoverableRead (Permit)
open DeliveryBook (Entry atKey)
open RetainedDelivery (Image entryAt)
open SourceOutcomes (Key)

variable {width slots capacity limit : Nat} {Payload Ticket Signature : Type}

structure Credit (limit : Nat) where
  lineage : Lineage
  writer : Kernel.Writer
  key : Key limit
  borrow : PoolState.Identity

structure Rules (width slots capacity limit : Nat) (Payload Ticket : Type) where
  retained : RetainedDelivery.Rules width slots capacity limit Payload Ticket
  credit : Ticket → Option (Credit limit)
  covers : Credit limit → SnapshotAdmission.Basis → Prop
  abandon : Credit limit → Ticket → Prop

structure Open (capacity limit : Nat) (Ticket : Type) where
  call : Invocation
  slot : Fin capacity
  key : Key limit
  proof : Ticket

structure Paid (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (call : Invocation) (key : Key limit) (basis : SnapshotAdmission.Basis) (credit : Credit limit)
    (proof : Ticket) : Prop where
  authentic : rules.credit proof = some credit
  lineageBound : credit.lineage = lineage
  writerBound : credit.writer = call.writer
  keyBound : credit.key = key
  coverage : rules.covers credit basis

theorem a_delegation_must_cover_the_basis_selected_at_application
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (call : Invocation) (key : Key limit) (basis : SnapshotAdmission.Basis) (credit : Credit limit)
    (proof : Ticket) (paid : Paid rules lineage call key basis credit proof) : rules.covers credit basis := by
  exact paid.coverage

def admissionRules (rules : Rules width slots capacity limit Payload Ticket) (key : Key limit)
    (credit : Credit limit) : OrderedReadReplay.Rules width slots capacity Payload Ticket :=
  {rules.retained.ordered with
    reservation := fun lineage _ call _ basis proof => Paid rules lineage call key basis credit proof}

def basisAt (before : Image slots capacity limit Payload) : SnapshotAdmission.Basis :=
  SnapshotAdmission.currentBasis before.ordered.reads.view

def retainedEntry (before : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (credit : Credit limit) (permit : Permit capacity) (reply : Barrier) : Entry capacity :=
  entryAt before request.key ⟨request.call, permit, basisAt before⟩ credit.borrow reply

inductive Reply (Payload : Type) (capacity : Nat) where
  | unchanged (reply : RetainedDelivery.Reply Payload capacity)
  | opened (permit : Permit capacity) (reply : Barrier)
  | abandoned
  | refused

abbrev Result (slots capacity limit : Nat) (Payload : Type) :=
  Image slots capacity limit Payload × Reply Payload capacity

def refuse (before : Image slots capacity limit Payload) : Result slots capacity limit Payload :=
  (RetainedDelivery.advance before, .refused)

noncomputable def chooseOpen (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (request : Open capacity limit Ticket) :
    Result slots capacity limit Payload := by
  classical
  exact match rules.credit request.proof with
  | none => refuse before
  | some credit =>
      match OrderedReadReplay.decide (admissionRules rules request.key credit) lineage before.ordered
          (.admit request.call request.slot request.proof) with
      | (ordered, .admitted permit reply) =>
          let entry := retainedEntry before request credit permit reply
          if DeliveryBook.MayInsert width before.deliveries request.key entry then
            (⟨ordered, DeliveryBook.insert before.deliveries request.key entry⟩, .opened permit reply)
          else refuse before
      | _ => refuse before

theorem an_open_publishes_its_exact_capture_and_independent_delivery_together
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (permit : Permit capacity) (reply : Barrier) (valid : before.deliveries.Valid width)
    (applied : chooseOpen rules lineage before request = (after, .opened permit reply)) :
    ∃ credit, Paid rules lineage request.call request.key (basisAt before) credit request.proof ∧
      reply = RTDBFailover.barrierAt request.call before.ordered.journal ∧
      (after.ordered.reads, permit) = RecoverableRead.captured before.ordered.reads request.slot reply ∧
      atKey after.deliveries request.key = some (retainedEntry before request credit permit reply) ∧
      after.deliveries.issued = request.key.serial ∧ after.deliveries.Valid width := by
  cases paid : rules.credit request.proof with
  | none => simp [chooseOpen, paid, refuse] at applied
  | some credit =>
      cases selected : OrderedReadReplay.decide (admissionRules rules request.key credit) lineage before.ordered
          (.admit request.call request.slot request.proof) with
      | mk ordered result =>
          cases result <;> simp [chooseOpen, paid, selected, refuse] at applied
          case admitted actualPermit actualReply =>
            split at applied
            · next fits =>
                obtain ⟨rfl, rfl, rfl⟩ := applied
                have original := OrderedReadReplay.every_admitted_reply_is_the_exact_marker_and_attested_basis
                  (admissionRules rules request.key credit) lineage before.ordered ordered request.call request.slot
                  request.proof permit reply selected
                have stored := DeliveryBook.an_exact_insert_keeps_the_bounded_book_well_formed _ _ _ valid fits
                exact ⟨credit, original.2.2.2.1, original.1, original.2.2.2.2, stored.2, rfl, stored.1⟩
            · simp at applied

theorem a_missing_delivery_slot_refuses_the_whole_open
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (unavailable : request.key.serial ≤ before.deliveries.issued ∨
      before.deliveries.rows request.key.slot ≠ none) :
    chooseOpen rules lineage before request = refuse before := by
  cases paid : rules.credit request.proof with
  | none => simp [chooseOpen, paid]
  | some credit =>
      cases selected : OrderedReadReplay.decide (admissionRules rules request.key credit) lineage before.ordered
          (.admit request.call request.slot request.proof) with
      | mk ordered result =>
          cases result <;> simp [chooseOpen, paid, selected]
          case admitted actualPermit actualReply =>
            intro canInsert
            rcases unavailable with earlier | occupied
            · have exactNext := canInsert.1
              omega
            · exact (occupied canInsert.2.2.1).elim

theorem a_credit_for_a_previous_uncovered_basis_cannot_authorize_current_capture
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (credit : Credit limit) (issued : rules.credit request.proof = some credit)
    (uncovered : ¬ rules.covers credit (basisAt before)) :
    chooseOpen rules lineage before request = refuse before := by
  have refused : OrderedReadReplay.decide (admissionRules rules request.key credit) lineage before.ordered
      (.admit request.call request.slot request.proof) = (OrderedReadReplay.advance before.ordered, .refused) := by
    simp only [OrderedReadReplay.decide]
    split
    · next checks =>
        exact (uncovered (a_delegation_must_cover_the_basis_selected_at_application rules lineage request.call
          request.key (basisAt before) credit request.proof checks.2.2.2.1)).elim
    · rfl
  simp [chooseOpen, issued, refused]

theorem a_valid_latest_capture_with_available_credit_and_slots_opens_in_one_step
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (credit : Credit limit) (issued : rules.credit request.proof = some credit)
    (ordered : OrderedReadReplay.Image slots capacity Payload) (permit : Permit capacity) (reply : Barrier)
    (selected : OrderedReadReplay.decide (admissionRules rules request.key credit) lineage before.ordered
      (.admit request.call request.slot request.proof) = (ordered, .admitted permit reply))
    (room : DeliveryBook.MayInsert width before.deliveries request.key (retainedEntry before request credit permit reply)) :
    chooseOpen rules lineage before request =
      (⟨ordered, DeliveryBook.insert before.deliveries request.key (retainedEntry before request credit permit reply)⟩,
        .opened permit reply) := by
  simp [chooseOpen, issued, selected, room]

theorem one_prepaid_credit_can_cover_the_exact_current_basis_without_preselecting_a_position
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (request : Open capacity limit Ticket) (credit : Credit limit)
    (issued : rules.credit request.proof = some credit)
    (scope : credit.lineage = lineage) (writer : credit.writer = request.call.writer) (key : credit.key = request.key)
    (_coverage : rules.covers credit (basisAt before))
    (callScope : request.call.lineage = lineage)
    (marker : (JointSource.decide rules.retained.ordered.journal lineage before.ordered.journal
      (AppliedBarrierReceipt.readCommand request.call)).2 =
        .stream (.readCut request.call.nonce (RTDBFailover.barrierAt request.call before.ordered.journal).cut))
    (reservable : RecoverableRead.Reservable width rules.retained.ordered.snapshot before.ordered.reads request.slot
      (RTDBFailover.barrierAt request.call before.ordered.journal))
    (fresh : ReadInvocationFloor.Fresh width (OrderedReadReplay.authority before.ordered) before.ordered.readThrough
      request.call.writer request.call.nonce)
    (room : let reply := RTDBFailover.barrierAt request.call before.ordered.journal
      let permit := (RecoverableRead.captured before.ordered.reads request.slot reply).2
      DeliveryBook.MayInsert width before.deliveries request.key (retainedEntry before request credit permit reply)) :
    ∃ after permit, chooseOpen rules lineage before request =
      (after, .opened permit (RTDBFailover.barrierAt request.call before.ordered.journal)) := by
  have paid : Paid rules lineage request.call request.key (basisAt before) credit request.proof :=
    by
      refine ⟨issued, scope, writer, key, ?_⟩
      first | exact _coverage | trivial
  let reply := RTDBFailover.barrierAt request.call before.ordered.journal
  let captured := RecoverableRead.captured before.ordered.reads request.slot reply
  let journal := (JointSource.decide rules.retained.ordered.journal lineage before.ordered.journal
    (AppliedBarrierReceipt.readCommand request.call)).1
  let ordered : OrderedReadReplay.Image slots capacity Payload := ⟨journal, captured.1, request.call.nonce⟩
  have chosen : OrderedReadReplay.decide (admissionRules rules request.key credit) lineage before.ordered
      (.admit request.call request.slot request.proof) = (ordered, .admitted captured.2 reply) := by
    unfold OrderedReadReplay.decide
    exact ite_eq_left ⟨callScope, marker, reservable, paid, fresh⟩
  exact ⟨_, captured.2, a_valid_latest_capture_with_available_credit_and_slots_opens_in_one_step
    rules lineage before request credit issued ordered captured.2 reply chosen room⟩

def fenceNext (before : Image slots capacity limit Payload) (key : Key limit) : Image slots capacity limit Payload :=
  {RetainedDelivery.advance before with deliveries := {before.deliveries with issued := key.serial}}

noncomputable def abandonUnused (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (before : Image slots capacity limit Payload) (credit : Credit limit) (proof : Ticket) :
    Result slots capacity limit Payload := by
  classical
  exact if credit.lineage = lineage ∧ OrderedReadReplay.deliveryOpen (OrderedReadReplay.authority before.ordered) = true ∧
      rules.abandon credit proof ∧ credit.key.serial = before.deliveries.issued + 1 ∧
      credit.key.serial < EnvelopeCodec.wordLimit width then
    (fenceNext before credit.key, .abandoned)
  else refuse before

theorem a_chosen_unused_fence_preserves_outstanding_rows_and_refuses_delayed_open
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before fenced : Image slots capacity limit Payload) (credit : Credit limit) (proof : Ticket)
    (request : Open capacity limit Ticket) (same : request.key = credit.key)
    (fence : abandonUnused rules lineage before credit proof = (fenced, .abandoned)) :
    fenced.deliveries.rows = before.deliveries.rows ∧
      chooseOpen rules lineage fenced request = refuse fenced := by
  simp only [abandonUnused] at fence
  split at fence
  · cases fence
    refine ⟨rfl, a_missing_delivery_slot_refuses_the_whole_open rules lineage _ request (.inl ?_)⟩
    simp [fenceNext, same]
  · simp [refuse] at fence

theorem the_current_owner_can_fence_unused_credit_after_writer_replacement
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (credit : Credit limit) (proof : Ticket)
    (installed : Kernel.Writer)
    (current : OrderedReadReplay.authority before.ordered = .active installed)
    (scope : credit.lineage = lineage) (authentic : rules.abandon credit proof)
    (next : credit.key.serial = before.deliveries.issued + 1)
    (fits : credit.key.serial < EnvelopeCodec.wordLimit width) :
    abandonUnused rules lineage before credit proof = (fenceNext before credit.key, .abandoned) := by
  have openGate : OrderedReadReplay.deliveryOpen (OrderedReadReplay.authority before.ordered) = true := by
    rw [current]
    rfl
  exact ite_eq_left ⟨scope, openGate, authentic, next, fits⟩

theorem an_assigned_credit_can_no_longer_be_fenced_as_unused
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (permit : Permit capacity) (reply : Barrier) (valid : before.deliveries.Valid width)
    (applied : chooseOpen rules lineage before request = (after, .opened permit reply))
    (credit : Credit limit) (proof : Ticket) (same : credit.key = request.key) :
    abandonUnused rules lineage after credit proof = refuse after := by
  obtain ⟨_, _, _, _, _, assigned, _⟩ := an_open_publishes_its_exact_capture_and_independent_delivery_together
    rules lineage before after request permit reply valid applied
  have impossible : credit.key.serial ≠ after.deliveries.issued + 1 := by
    simp [same, assigned]
  simp [abandonUnused, impossible]

theorem successful_open_can_finish_from_its_own_exact_borrow
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (request : Open capacity limit Ticket)
    (permit : Permit capacity) (reply : Barrier) (valid : before.deliveries.Valid width)
    (applied : chooseOpen rules lineage before request = (after, .opened permit reply))
    (authenticated : Invocation → Prop)
    (held : Key limit → PoolState.Identity → OrderedReadReplay.Delivery capacity → Prop)
    (sign : RTDBFailover.Route → EnvelopeCodec.Bytes → Signature)
    (caller : authenticated reply.invocation)
    (inUse : ∀ credit, rules.credit request.proof = some credit →
      held request.key credit.borrow (retainedEntry before request credit permit reply).request) :
    let body := AppliedBarrierReceipt.encode width reply
    RetainedDelivery.finish width after.deliveries request.key reply.invocation authenticated held sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf reply.invocation) body⟩ := by
  obtain ⟨credit, paid, _, _, stored, _, _⟩ := an_open_publishes_its_exact_capture_and_independent_delivery_together
    rules lineage before after request permit reply valid applied
  exact RetainedDelivery.a_retained_result_completes_from_the_original_live_borrow_without_the_old_frame width
    after.deliveries request.key (retainedEntry before request credit permit reply) authenticated held sign
    stored caller (inUse credit paid.authentic)

inductive Command (slots capacity limit : Nat) (Payload Ticket : Type) where
  | existing (command : RetainedDelivery.Command slots capacity limit Payload Ticket)
  | openRead (request : Open capacity limit Ticket)
  | abandonCredit (credit : Credit limit) (proof : Ticket)

noncomputable def decide (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    Result slots capacity limit Payload :=
  match command with
  | .existing command =>
      let applied := RetainedDelivery.decide rules.retained lineage before command
      (applied.1, .unchanged applied.2)
  | .openRead request => chooseOpen rules lineage before request
  | .abandonCredit credit proof => abandonUnused rules lineage before credit proof

structure Frame (slots capacity limit : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots capacity limit Payload Ticket

noncomputable def step (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (frame : Frame slots capacity limit Payload Ticket) :
    Option (Image slots capacity limit Payload) := by
  classical
  exact if frame.lineage = lineage ∧ frame.position = RetainedDelivery.position before + 1 then
    some (decide rules lineage before frame.command).1
  else none

noncomputable def replay (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket)) :
    Option (Image slots capacity limit Payload) :=
  frames.foldlM (step rules lineage) origin

theorem any_exact_checkpoint_and_suffix_reproduce_the_same_atomic_open_and_fence_history
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin first second : Image slots capacity limit Payload)
    (history : List (Frame slots capacity limit Payload Ticket)) (oldCut newCut : Nat)
    (oldCertified : replay rules lineage origin (history.take oldCut) = some first)
    (newCertified : replay rules lineage origin (history.take newCut) = some second) :
    replay rules lineage first (history.drop oldCut) = replay rules lineage second (history.drop newCut) := by
  have afterBase (base : Image slots capacity limit Payload) (cut : Nat)
      (certified : replay rules lineage origin (history.take cut) = some base) :
      replay rules lineage base (history.drop cut) = replay rules lineage origin history := by
    calc
      replay rules lineage base (history.drop cut) =
          replay rules lineage origin (history.take cut ++ history.drop cut) := by
        simp only [replay] at certified ⊢
        rw [List.foldlM_append, certified]
        rfl
      _ = replay rules lineage origin history := by rw [List.take_append_drop]
  exact (afterBase first oldCut oldCertified).trans (afterBase second newCut newCertified).symm

#print axioms a_delegation_must_cover_the_basis_selected_at_application
#print axioms an_open_publishes_its_exact_capture_and_independent_delivery_together
#print axioms a_missing_delivery_slot_refuses_the_whole_open
#print axioms a_credit_for_a_previous_uncovered_basis_cannot_authorize_current_capture
#print axioms a_valid_latest_capture_with_available_credit_and_slots_opens_in_one_step
#print axioms one_prepaid_credit_can_cover_the_exact_current_basis_without_preselecting_a_position
#print axioms the_current_owner_can_fence_unused_credit_after_writer_replacement
#print axioms a_chosen_unused_fence_preserves_outstanding_rows_and_refuses_delayed_open
#print axioms an_assigned_credit_can_no_longer_be_fenced_as_unused
#print axioms successful_open_can_finish_from_its_own_exact_borrow
#print axioms any_exact_checkpoint_and_suffix_reproduce_the_same_atomic_open_and_fence_history

end AtomicReadCapture
