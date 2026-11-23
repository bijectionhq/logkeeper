import SealBody

set_option warningAsError true

namespace CompleteSettlement

open AllocationVector (Receipt)
open RealizedSource (Activated Record Cleanup)
open SettlementComposition (Participant)

variable {slots : Nat} {Payload Ticket : Type}

structure Attestation (slots : Nat) where
  record : Record slots
  pool : Nat
  fenced : Cleanup slots → Prop
  absent : Cleanup slots → Prop
  chargedCustody : Cleanup slots → Prop

def scopeOf (record : Record slots) (receipt : Receipt) : Cleanup slots :=
  ⟨record.lineage, record.anchor, receipt.extent, receipt.demand.key, receipt.demand.binding⟩

def Settled (proof : Attestation slots) (receipt : Receipt) : Prop :=
  let exactScope := scopeOf proof.record receipt
  proof.fenced exactScope ∧ (proof.absent exactScope ∨ proof.chargedCustody exactScope)

def CoversPool (proof : Attestation slots) : Prop :=
  ∀ receipt ∈ proof.record.vector.recovery, receipt.extent.pool = proof.pool → Settled proof receipt

def Verified (record : Record slots) (pool : Nat) (proof : Attestation slots) : Prop :=
  proof.record = record ∧ proof.pool = pool ∧ CoversPool proof

theorem one_certificate_covers_every_original_scope_in_the_pool
    {record : Record slots} {proof : Attestation slots} {pool : Nat} {receipt : Receipt}
    (valid : Verified record pool proof)
    (required : receipt ∈ record.vector.recovery) (located : receipt.extent.pool = pool) :
    Settled proof receipt :=
  valid.2.2 receipt (valid.1.symm ▸ required) (valid.2.1.symm ▸ located)

def useAttestations (base : UnifiedSource.Rules slots Nat Payload Ticket) (record : Record slots)
    (openTicket : Ticket → Attestation slots) (authentic : Ticket → Prop) :
    UnifiedSource.Rules slots Nat Payload Ticket :=
  {base with settledReceipt := fun reply ticket =>
    match reply.participant with
    | .target => base.settledReceipt reply ticket
    | .pool pool =>
        reply.decision = record.anchor.decision ∧ authentic ticket ∧ Verified record pool (openTicket ticket)}

def receiptFor (record : Record slots) (pool : Nat) : UnifiedSource.Receipt slots Nat :=
  ⟨record.anchor.decision, .pool pool⟩

theorem a_partial_pool_report_cannot_advance_the_actual_source_book
    (limits : Kernel.Limits) (base : UnifiedSource.Rules slots Nat Payload Ticket)
    (state : UnifiedSource.State slots Nat Payload) (record : Record slots) (pool : Nat)
    (read : Ticket → Attestation slots) (authentic : Ticket → Prop) (ticket : Ticket)
    (remaining : Receipt) (outstanding : remaining ∈ record.vector.recovery)
    (belongs : remaining.extent.pool = pool) (missing : ¬ Settled (read ticket) remaining) :
    UnifiedSource.decide limits (useAttestations base record read authentic) state.core (state.position + 1)
      (.acknowledge (receiptFor record pool) (some ticket)) = (state.core, .refused) := by
  have refuses : ¬ UnifiedSource.AcceptsReceipt (useAttestations base record read authentic)
      (receiptFor record pool) (some ticket) := by
    intro accepted
    obtain ⟨other, same, verified⟩ := accepted
    have exactTicket := Option.some.inj same
    subst other
    exact missing (one_certificate_covers_every_original_scope_in_the_pool verified.2.2 outstanding belongs)
  simp only [receiptFor] at refuses
  cases found : SourceOutcomes.lookup state.core.book record.anchor.decision.key <;>
    simp [UnifiedSource.decide, receiptFor, found, refuses]

theorem the_complete_certificate_settles_only_its_own_participant
    (limits : Kernel.Limits) (base : UnifiedSource.Rules slots Nat Payload Ticket)
    (state : UnifiedSource.State slots Nat Payload) (record : Record slots) (pool : Nat)
    (read : Ticket → Attestation slots) (authentic : Ticket → Prop) (ticket : Ticket)
    (signed : authentic ticket) (complete : Verified record pool (read ticket))
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (Participant Nat))
    (found : SourceOutcomes.lookup state.core.book record.anchor.decision.key = some row)
    (binding : row.binding = record.anchor.decision.binding) (result : row.result = some record.anchor.decision.result) :
    let after := (UnifiedSource.decide limits (useAttestations base record read authentic) state.core (state.position + 1)
      (.acknowledge (receiptFor record pool) (some ticket))).1
    SourceOutcomes.lookup after.book record.anchor.decision.key =
      some {row with waiting := row.waiting.filter (fun participant => if participant = .pool pool then false else true)} := by
  have serial := (Option.filter_eq_some_iff.mp found).2
  have validates : UnifiedSource.AcceptsReceipt (useAttestations base record read authentic)
      (receiptFor record pool) (some ticket) := ⟨ticket, rfl, rfl, signed, complete⟩
  simp only [receiptFor] at validates
  let waiting := row.waiting.filter (fun participant => if participant = .pool pool then false else true)
  let book := SourceOutcomes.setRow state.core.book record.anchor.decision.key.slot (some {row with waiting})
  let next := {state.core with book}
  have decision : UnifiedSource.decide limits (useAttestations base record read authentic) state.core
      (state.position + 1) (.acknowledge (receiptFor record pool) (some ticket)) = (next, .accepted) := by
    change UnifiedSource.decide limits (useAttestations base record read authentic)
      state.core (state.position + 1) (.acknowledge ⟨record.anchor.decision, .pool pool⟩ (some ticket)) = _
    simp [UnifiedSource.decide, found, validates, binding, result, next, book, waiting]
    congr 4
    funext participant
    by_cases isPool : participant = .pool pool <;> simp [isPool]
  dsimp only
  rw [decision]
  simp [next, book, SourceOutcomes.lookup, SourceOutcomes.setRow, serial, waiting]

structure Window where
  lineage : ChosenReplay.Lineage
  installedAt : Nat
  physical : PoolState.Identity

structure Control (slots : Nat) (Payload : Type) where
  source : UnifiedSource.State slots Nat Payload
  realized : Fin slots → Option EnvelopeCodec.Bytes
  window : Option Window

def MatchesSlot (state : Control slots Payload) (lineage : ChosenReplay.Lineage)
    (key : SourceOutcomes.Key slots)
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (Participant Nat)) (record : Record slots) : Prop :=
  record.lineage = lineage ∧ record.anchor.decision.key = key ∧
  record.anchor.decision.binding = row.binding ∧ row.result = some .committed ∧
  record.anchor.position ≤ state.source.position

noncomputable def openSlot (atoms : SealBody.Atoms width) (maxRecovery : Nat) (state : Control slots Payload)
    (lineage : ChosenReplay.Lineage) (key : SourceOutcomes.Key slots) : Option (Record slots) := by
  classical
  exact do
    let row ← SourceOutcomes.lookup state.source.core.book key
    let wire ← state.realized key.slot
    let body ← SealBody.decode width maxRecovery wire
    let record ← SealBody.decodeRecord atoms slots body
    if MatchesSlot state lineage key row record then some record else none

theorem the_named_checkpoint_slot_reopens_the_original_realization_without_the_frame
    (atoms : SealBody.Atoms width) (maxRecovery : Nat)
    {catalog : EnvelopeRecovery.Catalog width (Control slots Payload) Data}
    {authentic : EnvelopeCodec.Bytes → Prop} {expected : EnvelopeRecovery.Anchor width}
    {needed : EnvelopeCodec.Field width → Prop} {envelope : EnvelopeCodec.Envelope width}
    {wire : EnvelopeCodec.Bytes} {body : EnvelopeRecovery.Contents width (Control slots Payload) Data}
    (opened : EnvelopeRecovery.Opened catalog authentic expected needed wire envelope body)
    (lineage : ChosenReplay.Lineage) (key : SourceOutcomes.Key slots)
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (Participant Nat))
    (found : SourceOutcomes.lookup body.control.source.core.book key = some row)
    (canonical : SealBody.Body width) (original : Record slots) (count : canonical.recovery.length ≤ maxRecovery)
    (widthPositive : 0 < width) (stored : body.control.realized key.slot = some (SealBody.encode canonical))
    (typed : SealBody.decodeRecord atoms slots canonical = some original)
    (matched : MatchesSlot body.control lineage key row original) :
    openSlot atoms maxRecovery body.control lineage key = some original ∧
      ∀ dependency, needed dependency → catalog.retained dependency := by
  have exactBytes := SealBody.a_valid_body_round_trips canonical maxRecovery widthPositive count
  refine ⟨?_, fun dependency use => EnvelopeRecovery.opened_checkpoint_covers_every_required_object opened dependency use⟩
  simp [openSlot, found, stored, exactBytes, typed, matched]

noncomputable def compact (limits : Kernel.Limits) (rules : UnifiedSource.Rules slots Nat Payload Ticket)
    (state : Control slots Payload) (key : SourceOutcomes.Key slots) : Control slots Payload := by
  classical
  let decided := UnifiedSource.decide limits rules state.source.core (state.source.position + 1) (.compact key)
  exact {state with
    source := ⟨decided.1, state.source.position + 1⟩
    realized := match decided.2 with
      | .accepted => fun slot => if slot = key.slot then none else state.realized slot
      | _ => state.realized}

theorem compacting_a_source_result_keeps_its_independent_serving_window
    (limits : Kernel.Limits) (rules : UnifiedSource.Rules slots Nat Payload Ticket)
    (state : Control slots Payload) (key : SourceOutcomes.Key slots)
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (Participant Nat))
    (found : SourceOutcomes.lookup state.source.core.book key = some row)
    (done : SourceOutcomes.MayCompact row) :
    let compacted := compact limits rules state key
    compacted.realized key.slot = none ∧ compacted.window = state.window ∧
      SourceOutcomes.lookup compacted.source.core.book key = none := by
  simp only [compact, UnifiedSource.decide, found, ite_eq_left done]
  simp [SourceOutcomes.lookup, SourceOutcomes.setRow]

theorem an_outstanding_participant_retains_the_canonical_seal_body
    (limits : Kernel.Limits) (rules : UnifiedSource.Rules slots Nat Payload Ticket)
    (state : Control slots Payload) (key : SourceOutcomes.Key slots)
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (Participant Nat))
    (found : SourceOutcomes.lookup state.source.core.book key = some row)
    (outstanding : row.waiting ≠ []) :
    (compact limits rules state key).realized = state.realized := by
  have blocked : ¬ SourceOutcomes.MayCompact row := fun allowed => outstanding allowed.2
  simp [compact, UnifiedSource.decide, found, blocked]

theorem compacting_the_source_cannot_reclaim_a_frame_needed_by_a_selectable_base
    {protection : JointCheckpoint.Protection Evidence Claim} {frame : Evidence} {basis : JournalRotation.View}
    (selectable : JointCheckpoint.Selectable protection basis) (needed : protection.tail basis frame) :
    ¬ JointCheckpoint.MayRemove protection frame := by
  intro discard
  exact discard.1 basis selectable needed

#print axioms one_certificate_covers_every_original_scope_in_the_pool
#print axioms a_partial_pool_report_cannot_advance_the_actual_source_book
#print axioms the_complete_certificate_settles_only_its_own_participant
#print axioms the_named_checkpoint_slot_reopens_the_original_realization_without_the_frame
#print axioms compacting_a_source_result_keeps_its_independent_serving_window
#print axioms an_outstanding_participant_retains_the_canonical_seal_body
#print axioms compacting_the_source_cannot_reclaim_a_frame_needed_by_a_selectable_base

end CompleteSettlement
