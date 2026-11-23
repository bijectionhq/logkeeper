import TerminalDeliveryWitness

set_option warningAsError true

namespace SelectorReceipts

open JournalRotation (View)
open ChosenReplay (Lineage)
open RetainedDelivery (Frame Image Rules)
open EnvelopeCodec (Field)

variable {Name Ticket Record Payload Voter : Type} {width slots capacity limit : Nat}

structure Media (Name Ticket : Type) where
  bytes : Name → Option Ticket
  names : Name → Prop

def replace [DecidableEq Name] (rows : Name → Option Ticket) (name : Name) (row : Option Ticket) :
    Name → Option Ticket :=
  fun key => if key = name then row else rows key

def Media.stage [DecidableEq Name] (media : Media Name Ticket) (name : Name) (ticket : Ticket) :
    Media Name Ticket :=
  {media with bytes := replace media.bytes name (some ticket)}

def Media.syncName (media : Media Name Ticket) (name : Name) : Media Name Ticket :=
  {media with names := fun key => key = name ∨ media.names key}

def Media.remove [DecidableEq Name] (media : Media Name Ticket) (name : Name) : Media Name Ticket :=
  ⟨replace media.bytes name none, fun key => key ≠ name ∧ media.names key⟩

def DurableAttachment (media : Media Name Ticket) (name : Name) (ticket : Ticket) : Prop :=
  media.bytes name = some ticket ∧ media.names name

theorem proof_bytes_without_a_durable_name_cannot_back_a_selector
    (media : Media Name Ticket) (name : Name) (ticket : Ticket)
    (durable : DurableAttachment media name ticket) : media.names name := by
  exact durable.2

private theorem durable_after_both_barriers (media : Media Name Ticket) (name : Name) (ticket : Ticket)
    (written : media.bytes name = some ticket) (_named : media.names name) :
    DurableAttachment media name ticket := by
  refine ⟨written, ?_⟩
  first | exact _named | trivial

structure State (Record Name Ticket : Type) where
  journal : JournalRotation.State Record
  media : Media Name Ticket
  pins : Name → Option Ticket

abbrev Dependencies (Record Name Ticket : Type) := List Record → View → Name → Ticket → Prop

def Needed (dependencies : Dependencies Record Name Ticket) (journal : JournalRotation.State Record)
    (name : Name) (ticket : Ticket) : Prop :=
  ∃ view, JournalRotation.Selectable journal view ∧ dependencies journal.history view name ticket

def Sound (dependencies : Dependencies Record Name Ticket) (state : State Record Name Ticket) : Prop :=
  (∀ name ticket, Needed dependencies state.journal name ticket → DurableAttachment state.media name ticket) ∧
  ∀ name ticket, state.pins name = some ticket → DurableAttachment state.media name ticket

def Removable (dependencies : Dependencies Record Name Ticket) (state : State Record Name Ticket)
    (name : Name) : Prop :=
  (∀ ticket, ¬ Needed dependencies state.journal name ticket) ∧ state.pins name = none

inductive Step [DecidableEq Name] (dependencies : Dependencies Record Name Ticket) :
    State Record Name Ticket → State Record Name Ticket → Prop where
  | journal {before : State Record Name Ticket} {next : JournalRotation.State Record}
      (step : JournalRotation.Step before.journal next)
      (readied : ∀ name ticket, Needed dependencies next name ticket →
        ¬ Needed dependencies before.journal name ticket → DurableAttachment before.media name ticket) :
      Step dependencies before {before with journal := next}
  | stage {before : State Record Name Ticket} (name : Name) (ticket : Ticket)
      (vacant : before.media.bytes name = none) (unnamed : ¬ before.media.names name) :
      Step dependencies before {before with media := before.media.stage name ticket}
  | syncName {before : State Record Name Ticket} (name : Name) (ticket : Ticket)
      (written : before.media.bytes name = some ticket) :
      Step dependencies before {before with media := before.media.syncName name}
  | pin {before : State Record Name Ticket} (name : Name) (ticket : Ticket)
      (readable : DurableAttachment before.media name ticket) :
      Step dependencies before {before with pins := replace before.pins name (some ticket)}
  | finish (before : State Record Name Ticket) (name : Name) :
      Step dependencies before {before with pins := replace before.pins name none}
  | remove {before : State Record Name Ticket} (name : Name) (allowed : Removable dependencies before name) :
      Step dependencies before {before with media := before.media.remove name}

inductive Trace [DecidableEq Name] (dependencies : Dependencies Record Name Ticket) :
    State Record Name Ticket → State Record Name Ticket → Prop where
  | same (state : State Record Name Ticket) : Trace dependencies state state
  | next {first before after : State Record Name Ticket} (earlier : Trace dependencies first before)
      (last : Step dependencies before after) : Trace dependencies first after

private theorem stage_preserves_durable_bytes [DecidableEq Name] {media : Media Name Ticket} {name : Name}
    (ticket : Ticket) (vacant : media.bytes name = none) {existing : Name} {previous : Ticket}
    (available : DurableAttachment media existing previous) :
    DurableAttachment (media.stage name ticket) existing previous := by
  have distinct : existing ≠ name := by
    intro same
    subst existing
    have impossible := vacant.symm.trans available.1
    cases impossible
  have bytes : (media.stage name ticket).bytes existing = some previous := by
    simpa [Media.stage, replace, distinct] using available.1
  exact durable_after_both_barriers _ _ _ bytes
    (proof_bytes_without_a_durable_name_cannot_back_a_selector media existing previous available)

private theorem remove_preserves_other_durable_bytes [DecidableEq Name] {media : Media Name Ticket}
    {name existing : Name} {previous : Ticket} (distinct : existing ≠ name)
    (available : DurableAttachment media existing previous) :
    DurableAttachment (media.remove name) existing previous := by
  have bytes : (media.remove name).bytes existing = some previous := by
    simpa [Media.remove, replace, distinct] using available.1
  exact durable_after_both_barriers _ _ _ bytes
    ⟨distinct, proof_bytes_without_a_durable_name_cannot_back_a_selector media existing previous available⟩

theorem every_step_preserves_selector_receipts_and_pins [DecidableEq Name]
    {dependencies : Dependencies Record Name Ticket} {before after : State Record Name Ticket}
    (safe : Sound dependencies before) (transition : Step dependencies before after) :
    Sound dependencies after := by
  classical
  cases transition with
  | journal _ readied =>
      refine ⟨?_, safe.2⟩
      intro name ticket required
      by_cases already : Needed dependencies before.journal name ticket
      · exact safe.1 name ticket already
      · exact readied name ticket required already
  | stage name ticket vacant _ =>
      exact ⟨fun old proof used => stage_preserves_durable_bytes ticket vacant (safe.1 old proof used),
        fun old proof held => stage_preserves_durable_bytes ticket vacant (safe.2 old proof held)⟩
  | syncName _ _ _ =>
      exact ⟨fun old proof used => durable_after_both_barriers _ _ _ (safe.1 old proof used).1
        (Or.inr (proof_bytes_without_a_durable_name_cannot_back_a_selector _ _ _ (safe.1 old proof used))),
        fun old proof held => durable_after_both_barriers _ _ _ (safe.2 old proof held).1
          (Or.inr (proof_bytes_without_a_durable_name_cannot_back_a_selector _ _ _ (safe.2 old proof held)))⟩
  | pin name ticket readable =>
      refine ⟨safe.1, ?_⟩
      intro other proof held
      by_cases same : other = name
      · subst other
        have equal : ticket = proof := by simpa [replace] using held
        exact equal ▸ readable
      · exact safe.2 other proof (by simpa [replace, same] using held)
  | finish name =>
      refine ⟨safe.1, ?_⟩
      intro other proof held
      by_cases same : other = name
      · simp [replace, same] at held
      · exact safe.2 other proof (by simpa [replace, same] using held)
  | remove name allowed =>
      constructor
      · intro other proof used
        have distinct : other ≠ name := by
          intro same
          subst other
          exact allowed.1 proof used
        exact remove_preserves_other_durable_bytes distinct (safe.1 other proof used)
      · intro other proof held
        have distinct : other ≠ name := by
          intro same
          subst other
          have impossible := allowed.2.symm.trans held
          cases impossible
        exact remove_preserves_other_durable_bytes distinct (safe.2 other proof held)

theorem every_trace_keeps_the_journal_and_exact_selector_receipts [DecidableEq Name]
    {dependencies : Dependencies Record Name Ticket} {first last : State Record Name Ticket}
    (journal : JournalRotation.Safe first.journal) (namespaceTracked : JournalRotation.TracksNamespace first.journal)
    (receipts : Sound dependencies first) (trace : Trace dependencies first last) :
    JournalRotation.Safe last.journal ∧ JournalRotation.TracksNamespace last.journal ∧ Sound dependencies last := by
  induction trace with
  | same => exact ⟨journal, namespaceTracked, receipts⟩
  | next _ step prior =>
      have witnessed := every_step_preserves_selector_receipts_and_pins prior.2.2 step
      cases step with
      | journal action _ =>
          exact ⟨JournalRotation.step_preserves_safety prior.1 prior.2.1 action,
            JournalRotation.step_tracks_all_crash_choices prior.2.1 action, witnessed⟩
      | _ => exact ⟨prior.1, prior.2.1, witnessed⟩

theorem successful_publication_requires_exact_bytes_and_name_for_each_new_receipt
    [DecidableEq Name] {dependencies : Dependencies Record Name Ticket} {before after : State Record Name Ticket}
    (safe : Sound dependencies before) (transition : Step dependencies before after)
    (view : View) (possible : JournalRotation.Selectable after.journal view)
    (name : Name) (ticket : Ticket) (requires : dependencies after.journal.history view name ticket) :
    DurableAttachment after.media name ticket :=
  (every_step_preserves_selector_receipts_and_pins safe transition).1 name ticket ⟨view, possible, requires⟩

theorem old_selector_or_live_pin_can_keep_a_logically_settled_receipt
    {dependencies : Dependencies Record Name Ticket} (state : State Record Name Ticket)
    (name : Name) (ticket : Ticket)
    (needed : dependencies state.journal.history state.journal.stable name ticket ∨ state.pins name = some ticket) :
    ¬ Removable dependencies state name := by
  intro allowed
  rcases needed with byOld | byPin
  · exact allowed.1 ticket ⟨state.journal.stable, Or.inl rfl, byOld⟩
  · have impossible := allowed.2.symm.trans byPin
    cases impossible

structure Attachment (Name Ticket : Type) (capacity : Nat) where
  name : Name
  proof : Ticket
  row : DeliveryBook.Entry capacity

structure ReceiptPlan (Name Ticket : Type) (capacity limit : Nat) where
  attached : Fin limit → Option (Attachment Name Ticket capacity)

def Attested (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (base : Image slots capacity limit Payload) (plan : ReceiptPlan Name Ticket capacity limit) : Prop :=
  ∀ slot evidence, plan.attached slot = some evidence →
    base.deliveries.rows slot = some evidence.row ∧
    rules.settled lineage ⟨slot, evidence.row.serial⟩ evidence.row evidence.proof

def Named (media : Media Name Ticket) (plan : ReceiptPlan Name Ticket capacity limit) : Prop :=
  ∀ slot evidence, plan.attached slot = some evidence → DurableAttachment media evidence.name evidence.proof

noncomputable def reopen (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload)
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    (cutoff : List (Frame slots capacity limit Payload Ticket)) {ballot : Nat}
    (chosen : PrefixAgreement.Chosen ledger ballot cutoff) (base : DeliveryRecovery.Base rules lineage origin cutoff)
    (media : Media Name Ticket) (plan : ReceiptPlan Name Ticket capacity limit)
    (diskTail : List (Frame slots capacity limit Payload Ticket)) : Option (Image slots capacity limit Payload) := by
  classical
  exact if Attested rules lineage base.image plan ∧ Named media plan then
    DeliveryRecovery.reopen rules lineage origin cutoff chosen base diskTail
  else none

theorem a_crash_selectable_named_receipt_is_available_to_ranked_recovery [DecidableEq Name]
    {dependencies : Dependencies (Frame slots capacity limit Payload Ticket) Name Ticket}
    {first last : State (Frame slots capacity limit Payload Ticket) Name Ticket}
    (safe : JournalRotation.Safe first.journal) (tracked : JournalRotation.TracksNamespace first.journal)
    (sound : Sound dependencies first) (trace : Trace dependencies first last)
    (view : View) (survived : last.journal.namespaceChoices view)
    (plan : ReceiptPlan Name Ticket capacity limit)
    (bound : ∀ slot evidence, plan.attached slot = some evidence →
      dependencies last.journal.history view evidence.name evidence.proof) :
    Named last.media plan := by
  obtain ⟨_, namespaceTracked, ready⟩ := every_trace_keeps_the_journal_and_exact_selector_receipts
    safe tracked sound trace
  intro slot evidence attached
  exact ready.1 evidence.name evidence.proof ⟨view, (namespaceTracked view).mp survived, bound slot evidence attached⟩

theorem named_receipts_cannot_change_the_recovered_ranked_book
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload)
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    (cutoff : List (Frame slots capacity limit Payload Ticket)) {ballot : Nat}
    (chosen : PrefixAgreement.Chosen ledger ballot cutoff)
    (old new : DeliveryRecovery.Base rules lineage origin cutoff)
    (firstMedia otherMedia : Media Name Ticket) (firstPlan otherPlan : ReceiptPlan Name Ticket capacity limit)
    (oldTail newTail : List (Frame slots capacity limit Payload Ticket)) (first second : Image slots capacity limit Payload)
    (older : reopen rules lineage origin cutoff chosen old firstMedia firstPlan oldTail = some first)
    (newer : reopen rules lineage origin cutoff chosen new otherMedia otherPlan newTail = some second) :
    first = second := by
  unfold reopen at older newer
  split at older
  · split at newer
    · exact DeliveryRecovery.either_exact_base_reopens_the_same_delivery_lifecycle rules lineage origin cutoff chosen
        old new oldTail newTail first second older newer
    · contradiction
  · contradiction

theorem an_authenticated_local_receipt_plan_and_chosen_tail_can_reopen
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin : Image slots capacity limit Payload)
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    (cutoff : List (Frame slots capacity limit Payload Ticket)) {ballot : Nat}
    (chosen : PrefixAgreement.Chosen ledger ballot cutoff) (base : DeliveryRecovery.Base rules lineage origin cutoff)
    (media : Media Name Ticket) (plan : ReceiptPlan Name Ticket capacity limit)
    (tail : List (Frame slots capacity limit Payload Ticket)) (reopened : Image slots capacity limit Payload)
    (authentic : Attested rules lineage base.image plan) (named : Named media plan)
    (ranked : DeliveryRecovery.reopen rules lineage origin cutoff chosen base tail = some reopened) :
    reopen rules lineage origin cutoff chosen base media plan tail = some reopened := by
  simp [reopen, authentic, named, ranked]

def readTail (media : JournalRotation.Contents Record) (start : Nat) : Nat → Option (List Record)
  | 0 => some []
  | count + 1 =>
      match media (.tail start), readTail media (start + 1) count with
      | some [record], some later => some (record :: later)
      | _, _ => none

private theorem read_tail_from_each_exact_durable_frame (media : JournalRotation.Contents Record)
    (records : List Record) (start : Nat)
    (known : ∀ index record, records[index]? = some record → media (.tail (start + index)) = some [record]) :
    readTail media start records.length = some records := by
  induction records generalizing start with
  | nil => rfl
  | cons first later ih =>
      have head : media (.tail start) = some [first] := by
        simpa using known 0 first rfl
      have rest : readTail media (start + 1) later.length = some later := by
        apply ih
        intro index record found
        have authored := known (index + 1) record (by simpa using found)
        have offset : start + 1 + index = start + (index + 1) := by omega
        simpa only [offset] using authored
      simp [readTail, head, rest]

theorem a_selected_root_reads_its_exact_suffix_including_inline_settlement_proofs
    {journal : JournalRotation.State Record} {view : View} (exactMedia : JournalRotation.Exact journal view) :
    readTail journal.media view.cut (journal.history.length - view.cut) = some (journal.history.drop view.cut) := by
  rw [← List.length_drop]
  apply read_tail_from_each_exact_durable_frame
  intro index record found
  have atPosition : journal.history[view.cut + index]? = some record := by
    simpa only [List.getElem?_drop, Nat.add_comm] using found
  exact exactMedia.2.2 (view.cut + index) record (Nat.le_add_right _ _) atPosition

def ReceiptPlan.inStore (plan : ReceiptPlan Name Ticket capacity limit) (media : Media Name Ticket)
    (store : TerminalDeliveryWitness.Store width capacity limit Ticket) :
    TerminalDeliveryWitness.Store width capacity limit Ticket :=
  {store with
    receipts := fun slot => (plan.attached slot).map Attachment.proof
    durable := fun proof => ∃ slot evidence, plan.attached slot = some evidence ∧
      evidence.proof = proof ∧ DurableAttachment media evidence.name proof}

theorem a_named_attested_receipt_supplies_the_exact_terminal_witness
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (base : Image slots capacity limit Payload)
    (plan : ReceiptPlan Name Ticket capacity limit) (media : Media Name Ticket)
    (store : TerminalDeliveryWitness.Store width capacity limit Ticket)
    (authentic : Attested rules lineage base plan) (named : Named media plan)
    (slot : Fin limit) (evidence : Attachment Name Ticket capacity) (attached : plan.attached slot = some evidence) :
    TerminalDeliveryWitness.Terminal rules lineage (plan.inStore media store) slot evidence.row := by
  exact ⟨evidence.proof, by simp [ReceiptPlan.inStore, attached],
    ⟨slot, evidence, attached, rfl, named slot evidence attached⟩, (authentic slot evidence attached).2⟩

theorem a_crash_choice_recovers_the_exact_chosen_book_with_its_named_receipts [DecidableEq Name]
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (origin current : Image slots capacity limit Payload)
    {ledger : PrefixAgreement.Ledger Voter (Frame slots capacity limit Payload Ticket)}
    (cutoff : List (Frame slots capacity limit Payload Ticket)) {ballot : Nat}
    (chosen : PrefixAgreement.Chosen ledger ballot cutoff) (base : DeliveryRecovery.Base rules lineage origin cutoff)
    {dependencies : Dependencies (Frame slots capacity limit Payload Ticket) Name Ticket}
    {first last : State (Frame slots capacity limit Payload Ticket) Name Ticket}
    (safe : JournalRotation.Safe first.journal) (tracked : JournalRotation.TracksNamespace first.journal)
    (sound : Sound dependencies first) (trace : Trace dependencies first last)
    (view : View) (survived : last.journal.namespaceChoices view)
    (history : last.journal.history = cutoff) (aligned : view.cut = base.cut)
    (plan : ReceiptPlan Name Ticket capacity limit) (attested : Attested rules lineage base.image plan)
    (bound : ∀ slot evidence, plan.attached slot = some evidence →
      dependencies last.journal.history view evidence.name evidence.proof)
    (valid : RetainedDelivery.replay rules lineage origin cutoff = some current) :
    ∃ tail,
      readTail last.journal.media view.cut (last.journal.history.length - view.cut) = some tail ∧
      reopen rules lineage origin cutoff chosen base last.media plan tail = some current := by
  obtain ⟨journal, namespaceTracked, _⟩ := every_trace_keeps_the_journal_and_exact_selector_receipts
    safe tracked sound trace
  have exactMedia := JournalRotation.selectable_has_exact_cut journal ((namespaceTracked view).mp survived)
  have read := a_selected_root_reads_its_exact_suffix_including_inline_settlement_proofs exactMedia
  have localNames := a_crash_selectable_named_receipt_is_available_to_ranked_recovery safe tracked sound trace
    view survived plan bound
  refine ⟨cutoff.drop base.cut, ?_, ?_⟩
  · simpa [history, aligned] using read
  · apply an_authenticated_local_receipt_plan_and_chosen_tail_can_reopen rules lineage origin cutoff chosen base
      last.media plan (cutoff.drop base.cut) current attested localNames
    unfold DeliveryRecovery.reopen
    have matching : cutoff.drop base.cut <+: cutoff.drop base.cut := ⟨[], List.append_nil _⟩
    rw [ite_eq_left matching]
    rw [RetainedDelivery.replay_after_any_certified_base rules lineage origin base.image _ _ base.certified,
      List.take_append_drop]
    exact valid

theorem replaying_a_self_contained_settlement_needs_no_detached_stop_receipt
    (rules : Rules width slots capacity limit Payload Ticket) (lineage : Lineage)
    (before : Image slots capacity limit Payload) (key : SourceOutcomes.Key limit)
    (row : DeliveryBook.Entry capacity) (proof : Ticket) (present : DeliveryBook.atKey before.deliveries key = some row)
    (authority : OrderedReadReplay.deliveryOpen (OrderedReadReplay.authority before.ordered) = true)
    (settlement : rules.settled lineage key row proof) :
    RetainedDelivery.replay rules lineage before
      [⟨lineage, RetainedDelivery.position before + 1, .settle key row.borrow proof⟩] =
      some {RetainedDelivery.advance before with deliveries := DeliveryBook.clear before.deliveries key} := by
  simp [RetainedDelivery.replay, RetainedDelivery.step, RetainedDelivery.decide, present, authority, settlement]

#print axioms proof_bytes_without_a_durable_name_cannot_back_a_selector
#print axioms every_step_preserves_selector_receipts_and_pins
#print axioms every_trace_keeps_the_journal_and_exact_selector_receipts
#print axioms successful_publication_requires_exact_bytes_and_name_for_each_new_receipt
#print axioms old_selector_or_live_pin_can_keep_a_logically_settled_receipt
#print axioms a_crash_selectable_named_receipt_is_available_to_ranked_recovery
#print axioms named_receipts_cannot_change_the_recovered_ranked_book
#print axioms an_authenticated_local_receipt_plan_and_chosen_tail_can_reopen

#print axioms a_selected_root_reads_its_exact_suffix_including_inline_settlement_proofs
#print axioms a_named_attested_receipt_supplies_the_exact_terminal_witness
#print axioms a_crash_choice_recovers_the_exact_chosen_book_with_its_named_receipts

#print axioms replaying_a_self_contained_settlement_needs_no_detached_stop_receipt

end SelectorReceipts
