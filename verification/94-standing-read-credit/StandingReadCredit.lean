import AtomicReadCapture

set_option warningAsError true

namespace StandingReadCredit

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Barrier)
open RecoverableRead (Permit)
open RetainedDelivery (Image)
open SourceOutcomes (Key)

variable {width slots capacity limit : Nat} {Payload Ticket : Type}

structure SerialSlice where
  pool : Nat
  first : Nat
  size : Nat

def SerialSlice.issue (slice : SerialSlice) (index : Nat) : PoolState.Identity :=
  ⟨slice.pool, slice.first + index⟩

def SerialSlice.Contains (slice : SerialSlice) (borrow : PoolState.Identity) : Prop :=
  borrow.pool = slice.pool ∧ slice.first ≤ borrow.serial ∧ borrow.serial < slice.first + slice.size

theorem issue_uses_the_original_pool_and_only_its_prepaid_range (slice : SerialSlice)
    (index : Nat) (room : index < slice.size) : slice.Contains (slice.issue index) := by
  exact ⟨rfl, Nat.le_add_right _ _, Nat.add_lt_add_left room _⟩

def SerialSlice.Disjoint (left right : SerialSlice) : Prop :=
  left.pool ≠ right.pool ∨ left.first + left.size ≤ right.first ∨ right.first + right.size ≤ left.first

theorem disjoint_provider_ranges_cannot_issue_the_same_borrow
    (left right : SerialSlice) (disjoint : left.Disjoint right)
    (a b : Nat) (leftRoom : a < left.size) (rightRoom : b < right.size) :
    left.issue a ≠ right.issue b := by
  intro alias
  have samePool := congrArg PoolState.Identity.pool alias
  have sameSerial := congrArg PoolState.Identity.serial alias
  change left.pool = right.pool at samePool
  change left.first + a = right.first + b at sameSerial
  rcases disjoint with different | earlier | later
  · exact different samePool
  · omega
  · omega

structure Window where
  lineage : Lineage
  generation : Nat
  placement : Kernel.Placement
  allocation : PoolState.Identity
  serials : SerialSlice

structure StandingGrant (Ticket : Type) where
  window : Window
  proof : Ticket
  used : Nat

structure State (slots capacity limit : Nat) (Payload Ticket : Type) where
  retained : Image slots capacity limit Payload
  current : Option (StandingGrant Ticket)
  installedThrough : Nat

structure Rules (width slots capacity limit : Nat) (Payload Ticket : Type) where
  retained : RetainedDelivery.Rules width slots capacity limit Payload Ticket
  certified : Ticket → Option Window
  covers : Window → SnapshotAdmission.Basis → Prop

structure Ready (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (writer : Kernel.Writer) (grant : StandingGrant Ticket) : Prop where
  certified : rules.certified grant.proof = some grant.window
  lineage : grant.window.lineage = lineage
  placement : grant.window.placement = writer.placement
  pool : grant.window.allocation.pool = grant.window.serials.pool
  disjointAllocation : ¬ grant.window.serials.Contains grant.window.allocation
  withinWidth : grant.window.serials.first + grant.window.serials.size ≤ EnvelopeCodec.wordLimit width
  cursorFits : grant.window.serials.size < EnvelopeCodec.wordLimit width
  available : grant.used < grant.window.serials.size

def assignment (state : State slots capacity limit Payload Ticket) (lineage : Lineage)
    (grant : StandingGrant Ticket) (call : Invocation) (slot : Fin limit) : AtomicReadCapture.Credit limit :=
  ⟨lineage, call.writer, ⟨slot, state.retained.deliveries.issued + 1⟩, grant.window.serials.issue grant.used⟩

theorem physical_preparation_does_not_reserve_a_delivery_serial
    (state : State slots capacity limit Payload Ticket) (lineage : Lineage)
    (first second : StandingGrant Ticket) (call : Invocation) (slot : Fin limit) :
    (assignment state lineage first call slot).key = (assignment state lineage second call slot).key := rfl

noncomputable def atomicRules (rules : Rules width slots capacity limit Payload Ticket)
    (grant : StandingGrant Ticket) (credit : AtomicReadCapture.Credit limit) :
    AtomicReadCapture.Rules width slots capacity limit Payload Ticket := by
  classical
  exact ⟨rules.retained, fun proof => if proof = grant.proof then some credit else none,
    fun candidate basis => candidate = credit ∧ rules.covers grant.window basis, fun _ _ => False⟩

def refused (state : State slots capacity limit Payload Ticket) :
    State slots capacity limit Payload Ticket × AtomicReadCapture.Reply Payload capacity :=
  ({state with retained := RetainedDelivery.advance state.retained}, .refused)

noncomputable def tryOpen (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket)
    (call : Invocation) (readSlot : Fin capacity) (deliverySlot : Fin limit) :
    State slots capacity limit Payload Ticket × AtomicReadCapture.Reply Payload capacity := by
  classical
  exact match state.current with
  | none => refused state
  | some grant =>
      if Ready rules lineage call.writer grant then
        let credit := assignment state lineage grant call deliverySlot
        let request : AtomicReadCapture.Open capacity limit Ticket := ⟨call, readSlot, credit.key, grant.proof⟩
        match AtomicReadCapture.chooseOpen (atomicRules rules grant credit) lineage state.retained request with
        | (opened, .opened permit reply) =>
            ({state with retained := opened, current := some {grant with used := grant.used + 1}}, .opened permit reply)
        | _ => refused state
      else refused state

theorem the_window_range_must_have_room_at_application
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (writer : Kernel.Writer) (grant : StandingGrant Ticket)
    (ready : Ready rules lineage writer grant) : grant.used < grant.window.serials.size := by
  exact ready.available

theorem exhausted_standing_allowance_refuses_before_spending_the_read_nonce
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket)
    (call : Invocation) (readSlot : Fin capacity) (deliverySlot : Fin limit)
    (grant : StandingGrant Ticket) (installed : state.current = some grant)
    (full : grant.window.serials.size ≤ grant.used) :
    tryOpen rules lineage state call readSlot deliverySlot = refused state := by
  have blocked : ¬ Ready rules lineage call.writer grant :=
    fun ready => Nat.not_lt_of_ge full (the_window_range_must_have_room_at_application rules lineage call.writer grant ready)
  simp [tryOpen, installed, blocked]

theorem a_successful_choice_advances_both_cursors_and_keeps_the_original_borrow
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state after : State slots capacity limit Payload Ticket)
    (call : Invocation) (readSlot : Fin capacity) (deliverySlot : Fin limit)
    (permit : Permit capacity) (reply : Barrier) (valid : state.retained.deliveries.Valid width)
    (opened : tryOpen rules lineage state call readSlot deliverySlot = (after, .opened permit reply)) :
    ∃ grant row,
      state.current = some grant ∧ Ready rules lineage call.writer grant ∧
      after.current = some {grant with used := grant.used + 1} ∧
      after.installedThrough = state.installedThrough ∧
      after.retained.deliveries.issued = state.retained.deliveries.issued + 1 ∧
      DeliveryBook.atKey after.retained.deliveries ⟨deliverySlot, state.retained.deliveries.issued + 1⟩ = some row ∧
      row.borrow = grant.window.serials.issue grant.used ∧ rules.covers grant.window (AtomicReadCapture.basisAt state.retained) := by
  cases selected : state.current with
  | none => simp [tryOpen, selected, refused] at opened
  | some grant =>
      by_cases ready : Ready rules lineage call.writer grant
      · let credit := assignment state lineage grant call deliverySlot
        let request : AtomicReadCapture.Open capacity limit Ticket := ⟨call, readSlot, credit.key, grant.proof⟩
        have selectedOpen :
            tryOpen rules lineage state call readSlot deliverySlot =
              (match AtomicReadCapture.chooseOpen (atomicRules rules grant credit) lineage state.retained request with
              | (opened, .opened permit reply) =>
                  ({state with retained := opened, current := some {grant with used := grant.used + 1}}, .opened permit reply)
              | _ => refused state) := by
          simp only [tryOpen, selected, ite_eq_left ready]
          rfl
        rw [selectedOpen] at opened
        cases chosen : AtomicReadCapture.chooseOpen (atomicRules rules grant credit) lineage state.retained request with
        | mk retained outcome =>
            cases outcome <;> simp [chosen, refused] at opened
            case opened actualPermit actualReply =>
              obtain ⟨rfl, rfl, rfl⟩ := opened
              obtain ⟨actualCredit, paid, _, _, stored, serial, _⟩ :=
                AtomicReadCapture.an_open_publishes_its_exact_capture_and_independent_delivery_together
                  (atomicRules rules grant credit) lineage state.retained retained request actualPermit actualReply valid chosen
              obtain ⟨rfl, covers⟩ := paid.coverage
              exact ⟨grant, _, rfl, ready, rfl, rfl, serial, stored, rfl, covers⟩
      · simp [tryOpen, selected, ready, refused] at opened

theorem one_reserved_range_can_pay_only_its_bounded_number_of_chosen_operations
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (state after : State slots capacity limit Payload Ticket) (call : Invocation)
    (readSlot : Fin capacity) (deliverySlot : Fin limit)
    (permit : Permit capacity) (reply : Barrier) (valid : state.retained.deliveries.Valid width)
    (opened : tryOpen rules lineage state call readSlot deliverySlot = (after, .opened permit reply)) :
    ∃ grant, after.current = some grant ∧ grant.used ≤ grant.window.serials.size := by
  obtain ⟨grant, _, _, ready, exactWindow, _, _, _, _, _⟩ :=
    a_successful_choice_advances_both_cursors_and_keeps_the_original_borrow rules lineage state after
      call readSlot deliverySlot permit reply valid opened
  exact ⟨_, exactWindow, Nat.succ_le_of_lt (the_window_range_must_have_room_at_application rules lineage call.writer grant ready)⟩

structure Fence (capacity limit : Nat) (Ticket : Type) where
  grant : StandingGrant Ticket
  cut : Nat
  book : DeliveryBook.Book limit capacity

def frozenBook (state : State slots capacity limit Payload Ticket) (grant : StandingGrant Ticket) :
    Fence capacity limit Ticket :=
  ⟨grant, RetainedDelivery.position state.retained + 1, state.retained.deliveries⟩

structure Installable (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (next : Window) (proof : Ticket) : Prop where
  authority : OrderedReadReplay.authority state.retained.ordered = .active writer
  ready : Ready rules lineage writer ⟨next, proof, 0⟩
  newer : state.installedThrough < next.generation
  fits : next.generation < EnvelopeCodec.wordLimit width
  distinct : ∀ old, state.current = some old → old.window.serials.Disjoint next.serials

def install (state : State slots capacity limit Payload Ticket) (next : Window) (proof : Ticket) :
    State slots capacity limit Payload Ticket :=
  ⟨RetainedDelivery.advance state.retained, some ⟨next, proof, 0⟩, next.generation⟩

noncomputable def installWindow (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (next : Window) (proof : Ticket) : Option (State slots capacity limit Payload Ticket × Option (Fence capacity limit Ticket)) := by
  classical
  exact if Installable rules lineage state writer next proof then
    some (install state next proof, state.current.map (frozenBook state))
  else none

theorem installation_carries_the_old_book_and_needs_only_the_new_paid_window
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (next : Window) (proof : Ticket) (ready : Installable rules lineage state writer next proof) :
    installWindow rules lineage state writer next proof =
      some (install state next proof, state.current.map (frozenBook state)) :=
  ite_eq_left ready

theorem a_window_at_or_below_the_installed_watermark_is_never_reinstalled
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (next : Window) (proof : Ticket) (spent : next.generation ≤ state.installedThrough) :
    installWindow rules lineage state writer next proof = none :=
  by
    apply ite_eq_right
    intro ready
    exact Nat.not_lt_of_ge spent ready.newer

theorem replacement_fences_the_old_window_with_the_exact_delivery_book
    (rules : Rules width slots capacity limit Payload Ticket)
    (lineage : Lineage) (state after : State slots capacity limit Payload Ticket) (writer : Kernel.Writer)
    (next : Window) (proof : Ticket) (old : StandingGrant Ticket)
    (original : state.current = some old) (returned : Option (Fence capacity limit Ticket))
    (installed : installWindow rules lineage state writer next proof = some (after, returned)) :
    after.retained.deliveries = state.retained.deliveries ∧ after.installedThrough = next.generation ∧
      returned = some ⟨old, RetainedDelivery.position state.retained + 1, state.retained.deliveries⟩ := by
  unfold installWindow at installed
  split at installed
  · have equal := Option.some.inj installed
    exact ⟨(congrArg (fun value => value.1.retained.deliveries) equal).symm,
      (congrArg (fun value => value.1.installedThrough) equal).symm,
      by simpa [original, frozenBook] using (congrArg Prod.snd equal).symm⟩
  · contradiction

structure ReturnReady (authentic : Fence capacity limit Ticket → Prop) (settled : DeliveryBook.Entry capacity → Prop)
    (fence : Fence capacity limit Ticket) : Prop where
  chosen : authentic fence
  drained : ∀ slot row, fence.book.rows slot = some row →
    fence.grant.window.serials.Contains row.borrow → settled row

theorem provider_silence_cannot_refund_a_hidden_chosen_delivery
    (authentic : Fence capacity limit Ticket → Prop) (settled : DeliveryBook.Entry capacity → Prop)
    (fence : Fence capacity limit Ticket)
    (slot : Fin limit) (row : DeliveryBook.Entry capacity) (chosen : fence.book.rows slot = some row)
    (original : fence.grant.window.serials.Contains row.borrow) (live : ¬ settled row) :
    ¬ ReturnReady authentic settled fence :=
  fun refund => live (refund.drained slot row chosen original)

#print axioms issue_uses_the_original_pool_and_only_its_prepaid_range
#print axioms disjoint_provider_ranges_cannot_issue_the_same_borrow
#print axioms physical_preparation_does_not_reserve_a_delivery_serial
#print axioms the_window_range_must_have_room_at_application
#print axioms exhausted_standing_allowance_refuses_before_spending_the_read_nonce
#print axioms a_successful_choice_advances_both_cursors_and_keeps_the_original_borrow
#print axioms one_reserved_range_can_pay_only_its_bounded_number_of_chosen_operations
#print axioms installation_carries_the_old_book_and_needs_only_the_new_paid_window
#print axioms a_window_at_or_below_the_installed_watermark_is_never_reinstalled
#print axioms replacement_fences_the_old_window_with_the_exact_delivery_book
#print axioms provider_silence_cannot_refund_a_hidden_chosen_delivery

end StandingReadCredit
