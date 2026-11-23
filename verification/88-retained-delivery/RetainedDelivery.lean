import DeliveryBook

set_option warningAsError true

namespace RetainedDelivery

open ChosenReplay (Lineage)
open RTDBFailover (Invocation Route Barrier)
open SourceOutcomes (Key)
open DeliveryBook (Book Entry atKey)
open OrderedReadReplay (Delivery)
open EnvelopeCodec (Bytes Field)

variable {width slots capacity limit : Nat} {Payload Ticket Voter Signature : Type}

structure Image (slots capacity limit : Nat) (Payload : Type) where
  ordered : OrderedReadReplay.Image slots capacity Payload
  deliveries : Book limit capacity

structure Funding (limit capacity : Nat) where
  lineage : Lineage
  key : Key limit
  request : Delivery capacity
  borrow : PoolState.Identity

structure Rules (width slots capacity limit : Nat) (Payload Ticket : Type) where
  ordered : OrderedReadReplay.Rules width slots capacity Payload Ticket
  funding : Ticket → Option (Funding limit capacity)
  settled : Lineage → Key limit → Entry capacity → Ticket → Prop

inductive Command (slots capacity limit : Nat) (Payload Ticket : Type) where
  | source (command : OrderedReadReplay.Command slots capacity Payload Ticket)
  | grant (key : Key limit) (request : Delivery capacity) (borrow : PoolState.Identity) (evidence : Ticket)
  | settle (key : Key limit) (borrow : PoolState.Identity) (evidence : Ticket)

inductive Reply (Payload : Type) (capacity : Nat) where
  | source (reply : OrderedReadReplay.Reply Payload capacity)
  | granted (reply : Barrier)
  | settled
  | refused

def position (image : Image slots capacity limit Payload) : Nat :=
  OrderedReadReplay.position image.ordered

def advance (before : Image slots capacity limit Payload) : Image slots capacity limit Payload :=
  {before with ordered := OrderedReadReplay.advance before.ordered}

def entryAt (before : Image slots capacity limit Payload) (key : Key limit) (request : Delivery capacity)
    (borrow : PoolState.Identity) (reply : Barrier) : Entry capacity :=
  ⟨key.serial, position before + 1, request.permit, request.basis.root, request.basis.start, borrow, reply⟩

noncomputable def grant (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (key : Key limit) (request : Delivery capacity)
    (borrow : PoolState.Identity) (evidence : Ticket) : Image slots capacity limit Payload × Reply Payload capacity := by
  classical
  exact match OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence with
  | .delivery reply =>
      let row := entryAt before key request borrow reply
      if rules.funding evidence = some ⟨lineage, key, request, borrow⟩ ∧
          DeliveryBook.MayInsert width before.deliveries key row then
        ({advance before with deliveries := DeliveryBook.insert before.deliveries key row}, .granted reply)
      else (advance before, .refused)
  | _ => (advance before, .refused)

noncomputable def decide (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket) :
    Image slots capacity limit Payload × Reply Payload capacity := by
  classical
  exact match command with
  | .source (.deliver _ _) => (advance before, .refused)
  | .source command =>
      let result := OrderedReadReplay.decide rules.ordered lineage before.ordered command
      ({before with ordered := result.1}, .source result.2)
  | .grant key request borrow evidence => grant rules lineage before key request borrow evidence
  | .settle key borrow evidence =>
      match atKey before.deliveries key with
      | none => (advance before, .refused)
      | some row =>
          if row.borrow = borrow ∧ OrderedReadReplay.deliveryOpen (OrderedReadReplay.authority before.ordered) = true ∧
              rules.settled lineage key row evidence then
            ({advance before with deliveries := DeliveryBook.clear before.deliveries key}, .settled)
          else (advance before, .refused)

theorem the_bare_delivery_command_cannot_bypass_the_retained_book
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (request : Delivery capacity) (evidence : Ticket) :
    decide rules lineage before (.source (.deliver request evidence)) = (advance before, .refused) := by
  rfl

theorem a_successful_grant_commits_its_retained_evidence_in_the_same_ordered_step
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (key : Key limit) (request : Delivery capacity)
    (borrow : PoolState.Identity) (evidence : Ticket) (reply : Barrier)
    (valid : before.deliveries.Valid width)
    (accepted : decide rules lineage before (.grant key request borrow evidence) = (after, .granted reply)) :
    after.ordered = (OrderedReadReplay.decide rules.ordered lineage before.ordered (.deliver request evidence)).1 ∧
    OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence = .delivery reply ∧
    rules.funding evidence = some ⟨lineage, key, request, borrow⟩ ∧
    atKey after.deliveries key = some (entryAt before key request borrow reply) ∧ after.deliveries.Valid width := by
  simp only [decide, grant] at accepted
  cases outcome : OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence <;>
    simp only [outcome] at accepted
  case delivery selected =>
    split at accepted
    · next allowed =>
        cases accepted
        have maintained := DeliveryBook.an_exact_insert_keeps_the_bounded_book_well_formed _ _ _ valid allowed.2
        exact ⟨rfl, rfl, allowed.1, maintained.2, maintained.1⟩
    · simp at accepted
  all_goals simp at accepted

theorem a_stale_or_occupied_delivery_slot_refuses_without_changing_the_book
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (key : Key limit) (request : Delivery capacity)
    (borrow : PoolState.Identity) (evidence : Ticket)
    (unavailable : key.serial ≤ before.deliveries.issued ∨ (before.deliveries.rows key.slot).isSome = true) :
    decide rules lineage before (.grant key request borrow evidence) = (advance before, .refused) := by
  have refused (row : Entry capacity) : ¬ DeliveryBook.MayInsert width before.deliveries key row := by
    intro allowed
    rcases unavailable with already | filled
    · have next := allowed.1
      omega
    · simp [allowed.2.2.1] at filled
  cases outcome : OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence <;>
    simp [decide, grant, outcome, refused]

theorem an_immutable_funding_proof_cannot_be_rebound_to_another_delivery
    (rules : Rules width slots capacity limit Payload Ticket) (evidence : Ticket)
    (original rival : Funding limit capacity)
    (funded : rules.funding evidence = some original) (substituted : rules.funding evidence = some rival) :
    original = rival :=
  Option.some.inj (funded.symm.trans substituted)

theorem closing_the_original_read_leaves_the_independent_delivery_record
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (permit : RecoverableRead.Permit capacity) (evidence : Ticket) :
    (decide rules lineage before (.source (.close permit evidence))).1.deliveries = before.deliveries := rfl

theorem exact_settlement_clears_only_the_named_delivery_after_original_custody_stops
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (key : Key limit) (borrow : PoolState.Identity) (evidence : Ticket)
    (valid : before.deliveries.Valid width)
    (settled : decide rules lineage before (.settle key borrow evidence) = (after, .settled)) :
    (∃ row, atKey before.deliveries key = some row ∧ row.borrow = borrow ∧ rules.settled lineage key row evidence) ∧
    atKey after.deliveries key = none ∧ after.deliveries.issued = before.deliveries.issued ∧ after.deliveries.Valid width ∧
    ∀ other : Key limit, other.slot ≠ key.slot → atKey after.deliveries other = atKey before.deliveries other := by
  simp only [decide] at settled
  cases found : atKey before.deliveries key with
  | none => simp [found] at settled
  | some row =>
      simp only [found] at settled
      split at settled
      · next permitted =>
          cases settled
          have exactRow := DeliveryBook.exact_release_keeps_the_issuance_frontier_and_other_rows before.deliveries key valid
          exact ⟨⟨row, rfl, permitted.1, permitted.2.2⟩, exactRow.2.2.1, exactRow.2.1, exactRow.1, exactRow.2.2.2⟩
      · simp at settled

noncomputable def finish (width : Nat) (book : Book limit capacity) (key : Key limit)
    (call : Invocation) (authenticate : Invocation → Prop)
    (held : Key limit → PoolState.Identity → Delivery capacity → Prop)
    (sign : Route → Bytes → Signature) : Option (AppliedBarrierReceipt.Packet Signature) := by
  classical
  exact do
    let row ← atKey book key
    if row.reply.invocation = call ∧ authenticate call ∧ held key row.borrow row.request then
      let body := AppliedBarrierReceipt.encode width row.reply
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf call) body⟩
    else none

theorem a_retained_result_completes_from_the_original_live_borrow_without_the_old_frame
    (width : Nat) (book : Book limit capacity) (key : Key limit) (row : Entry capacity)
    (authenticate : Invocation → Prop) (held : Key limit → PoolState.Identity → Delivery capacity → Prop)
    (sign : Route → Bytes → Signature) (found : atKey book key = some row)
    (caller : authenticate row.reply.invocation) (physical : held key row.borrow row.request) :
    let body := AppliedBarrierReceipt.encode width row.reply
    finish width book key row.reply.invocation authenticate held sign =
      some ⟨body, sign (AppliedBarrierReceipt.sourceOf row.reply.invocation) body⟩ := by
  simp [finish, found, caller, physical]

theorem possession_of_the_retained_result_cannot_finish_after_its_borrow_stops
    (width : Nat) (book : Book limit capacity) (key : Key limit) (row : Entry capacity)
    (call : Invocation) (authenticate : Invocation → Prop)
    (held : Key limit → PoolState.Identity → Delivery capacity → Prop)
    (sign : Route → Bytes → Signature) (found : atKey book key = some row) (stopped : ¬ held key row.borrow row.request) :
    finish width book key call authenticate held sign = none := by
  simp [finish, found, stopped]

structure Frame (slots capacity limit : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots capacity limit Payload Ticket

noncomputable def step (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (frame : Frame slots capacity limit Payload Ticket) :
    Option (Image slots capacity limit Payload) := by
  classical
  exact if frame.lineage = lineage ∧ frame.position = position before + 1 then
    some (decide rules lineage before frame.command).1
  else none

noncomputable def replay (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket)) :
    Option (Image slots capacity limit Payload) :=
  frames.foldlM (step rules lineage) origin

theorem replay_after_any_certified_base (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin base : Image slots capacity limit Payload)
    (older suffix : List (Frame slots capacity limit Payload Ticket))
    (prefixApplied : replay rules lineage origin older = some base) :
    replay rules lineage base suffix = replay rules lineage origin (older ++ suffix) := by
  simp only [replay] at prefixApplied ⊢
  rw [List.foldlM_append, prefixApplied]
  rfl

private theorem all_ordered_decisions_preserve_the_book_bound
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (command : Command slots capacity limit Payload Ticket)
    (valid : before.deliveries.Valid width) : (decide rules lineage before command).1.deliveries.Valid width := by
  cases command with
  | source command => cases command <;> exact valid
  | grant key request borrow evidence =>
      simp only [decide, grant]
      cases outcome : OrderedReadReplay.decideDelivery rules.ordered lineage before.ordered request evidence <;> dsimp only
      case delivery selected =>
        split
        · next allowed =>
            exact (DeliveryBook.an_exact_insert_keeps_the_bounded_book_well_formed _ _ _ valid allowed.2).1
        · exact valid
      all_goals exact valid
  | settle key borrow evidence =>
      simp only [decide]
      cases found : atKey before.deliveries key with
      | none => exact valid
      | some row =>
          dsimp only
          split
          · exact (DeliveryBook.exact_release_keeps_the_issuance_frontier_and_other_rows _ _ valid).1
          · exact valid

theorem every_replayed_trace_preserves_the_fixed_delivery_book_bound
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before after : Image slots capacity limit Payload) (frames : List (Frame slots capacity limit Payload Ticket))
    (valid : before.deliveries.Valid width) (restored : replay rules lineage before frames = some after) :
    after.deliveries.Valid width := by
  induction frames generalizing before with
  | nil =>
      have same : before = after := by simpa [replay] using restored
      exact same ▸ valid
  | cons frame rest later =>
      cases applied : step rules lineage before frame with
      | none => simp [replay, applied] at restored
      | some next =>
          have preserved : next.deliveries.Valid width := by
            unfold step at applied
            split at applied
            · cases applied
              exact all_ordered_decisions_preserve_the_book_bound rules lineage before frame.command valid
            · simp at applied
          exact later next preserved (by simpa [replay, applied] using restored)

end RetainedDelivery
