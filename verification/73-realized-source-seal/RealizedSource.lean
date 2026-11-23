import AllocationVector
import ChosenReplay

set_option warningAsError true

namespace RealizedSource

open AllocationVector (Demand Plan Receipt Valid)
open ChosenReplay (Frame Image Lineage Rules)

variable {slots : Nat} {Payload Ticket : Type}

structure Vector where
  append : Receipt
  recovery : List Receipt
  deriving DecidableEq

def Vector.receipts (vector : Vector) : List Receipt := vector.append :: vector.recovery

structure Record (slots : Nat) where
  lineage : Lineage
  anchor : UnifiedSource.Anchor slots Nat
  vector : Vector

structure Sealed (slots : Nat) (Payload : Type) where
  image : Image slots Payload
  record : Record slots

structure Pending (slots : Nat) (Payload : Type) where
  image : Image slots Payload
  lineage : Lineage
  plan : Plan slots

def reserveFrame (lineage : Lineage) (image : Image slots Payload) (plan : Plan slots)
    (participants : UnifiedSource.Participants Nat) : Frame slots Payload Ticket :=
  ⟨lineage, image.source.position + 1, .source (.reserve plan.move plan.intent participants)⟩

noncomputable def reserve (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (plan : Plan slots) (participants : UnifiedSource.Participants Nat)
    (authorized : Plan slots → Prop) : Option (Pending slots Payload) := by
  classical
  exact if authorized plan then
    let applied := ChosenReplay.decide rules lineage image (reserveFrame lineage image plan participants)
    match applied.2 with
    | .accepted => some ⟨applied.1, lineage, plan⟩
    | _ => none
  else none

theorem accepted_reservation_retains_the_exact_plan
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (plan : Plan slots) (participants : UnifiedSource.Participants Nat) (authorized : Plan slots → Prop)
    (planned : authorized plan)
    (chosen : (ChosenReplay.decide rules lineage image (reserveFrame lineage image plan participants)).2 = .accepted) :
    reserve rules lineage image plan participants authorized = some
      ⟨(ChosenReplay.decide rules lineage image (reserveFrame lineage image plan participants)).1, lineage, plan⟩ := by
  simp only [reserve, ite_eq_left planned, chosen]

def sealFrame (lineage : Lineage) (image : Image slots Payload)
    (writer : Kernel.Writer) (plan : Plan slots) : Frame slots Payload Ticket :=
  ⟨lineage, image.source.position + 1, .source (.fundedSeal writer plan.move (AllocationVector.vectorProjection plan))⟩

noncomputable def chooseSeal (rules : Rules slots Payload Ticket) (before : Pending slots Payload)
    (writer : Kernel.Writer) (vector : Vector) (authentic : Receipt → Prop) : Option (Sealed slots Payload) := by
  classical
  exact if Valid before.plan authentic vector.receipts then
    let frame := sealFrame before.lineage before.image writer before.plan
    let applied := ChosenReplay.decide rules before.lineage before.image frame
    match applied.2, applied.1.source.core.handoff with
    | .accepted, some anchor => some ⟨applied.1, ⟨before.lineage, anchor, vector⟩⟩
    | _, _ => none
  else none

theorem an_equal_price_vector_with_a_different_scope_cannot_seal
    (rules : Rules slots Payload Ticket) (before : Pending slots Payload)
    (writer : Kernel.Writer) (vector : Vector) (authentic : Receipt → Prop)
    (wrongScope : vector.append.demand.key ≠ before.plan.append.key) :
    chooseSeal rules before writer vector authentic = none := by
  have denied : ¬ Valid before.plan authentic vector.receipts :=
    fun verified => wrongScope (AllocationVector.an_exact_receipt_cannot_substitute_another_scope_at_equal_price verified)
  simp only [chooseSeal, ite_eq_right denied]

theorem choosing_the_realized_vector_seals_the_actual_source_in_the_same_position
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (before : Image slots Payload)
    (writer : Kernel.Writer) (plan : Plan slots) (vector : Vector) (authentic : Receipt → Prop)
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (SettlementComposition.Participant Nat))
    (valid : Valid plan authentic vector.receipts)
    (approve : ∀ pool, 0 < plan.intent.needs pool → Valid plan authentic vector.receipts →
      (rules.append.regional.source lineage.stream).preparedReceipt (AllocationVector.poolReceipt plan pool))
    (ready : UnifiedSource.Ready before.source.core plan.move row)
    (planned : row.binding = plan.intent)
    (holder : before.source.core.stream.authority = .active writer)
    (advances : writer.placement.generation < row.binding.target.generation)
    (relocates : writer.placement.group ≠ row.binding.target.group) :
    let frame := sealFrame (Ticket := Ticket) lineage before writer plan
    let applied := ChosenReplay.decide rules lineage before frame
    let anchor : UnifiedSource.Anchor slots Nat :=
      ⟨⟨plan.move, row.binding, .committed⟩, frame.position⟩
    chooseSeal rules ⟨before, lineage, plan⟩ writer vector authentic = some ⟨applied.1, ⟨lineage, anchor, vector⟩⟩ ∧
      applied.2 = .accepted ∧ applied.1.source.core.handoff = some anchor ∧
      applied.1.source.core.stream.history = before.source.core.stream.history := by
  let position := before.source.position + 1
  let command : UnifiedSource.Command slots Nat Payload Ticket :=
    .fundedSeal writer plan.move (AllocationVector.vectorProjection plan)
  let inner := rules.append.regional.source lineage.stream
  let limits := rules.append.regional.limits lineage.stream
  let after : UnifiedSource.Core slots Nat Payload :=
    {UnifiedSource.terminal before.source.core plan.move row .committed with
      stream := {before.source.core.stream with authority := .sealed row.binding.target writer}
      handoff := some ⟨⟨plan.move, row.binding, .committed⟩, position⟩}
  have full : UnifiedSource.full inner (AllocationVector.vectorProjection plan) row.binding := by
    rw [planned]
    exact AllocationVector.an_exact_vector_supplies_the_existing_pointwise_funding valid inner approve
  have effect : UnifiedSource.decide limits inner before.source.core position command = (after, .accepted) :=
    UnifiedSource.decide_funded_seal_accepts_the_exact_pending_row limits inner before.source.core position
      writer plan.move row (AllocationVector.vectorProjection plan) ready holder advances relocates full
  have unchanged : (UnifiedSource.decide limits inner before.source.core position command).1.stream.history =
      before.source.core.stream.history := by
    rw [effect]
  have chosen : ChosenReplay.decide rules lineage before (sealFrame lineage before writer plan) =
    ({before with source := ⟨after, position⟩}, .accepted) := by
    simp only [limits, inner, position, command] at unchanged effect
    simp only [ChosenReplay.decide, sealFrame, ite_eq_left unchanged, effect]
    rfl
  dsimp only
  rw [chosen]
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [chooseSeal, ite_eq_left valid, chosen]
  rfl

structure Install (slots : Nat) (Payload Ticket : Type) where
  original : ChosenReplay.Activation slots Payload Ticket
  mounted : Vector

abbrev Alias := Lineage → Nat → Nat

def Matches (alias : Alias) (state : Sealed slots Payload) (install : Install slots Payload Ticket) : Prop :=
  install.original.installation.anchor = state.record.anchor ∧
  install.mounted = state.record.vector ∧
  install.original.grant.version = alias state.record.lineage (state.image.source.position + 1)

def installFrame (state : Sealed slots Payload) (install : Install slots Payload Ticket) :
    Frame slots Payload Ticket :=
  ⟨state.record.lineage, state.image.source.position + 1, .activate install.original⟩

structure Activated (slots : Nat) (Payload : Type) where
  image : Image slots Payload
  record : Record slots
  alias : Nat
  physical : PoolState.Identity

noncomputable def activate (rules : Rules slots Payload Ticket) (alias : Alias)
    (state : Sealed slots Payload) (install : Install slots Payload Ticket)
    (installed : Install slots Payload Ticket → Prop) : Option (Activated slots Payload) := by
  classical
  exact if Matches alias state install ∧ installed install then
    let applied := ChosenReplay.decide rules state.record.lineage state.image (installFrame state install)
    match applied.2 with
    | .accepted => some ⟨applied.1, state.record, install.original.grant.version, install.mounted.append.extent⟩
    | _ => none
  else none

theorem an_activation_with_the_original_receipts_uses_its_source_alias_and_exact_extent
    (rules : Rules slots Payload Ticket) (alias : Alias)
    (state : Sealed slots Payload) (install : Install slots Payload Ticket)
    (installed : Install slots Payload Ticket → Prop)
    (exactBinding : Matches alias state install) (durable : installed install)
    (allowed : ChosenReplay.AcceptsActivation rules state.record.lineage state.image install.original) :
    let effect := ChosenReplay.decide rules state.record.lineage state.image (installFrame state install)
    let window := alias state.record.lineage (state.image.source.position + 1)
    activate rules alias state install installed =
      some ⟨effect.1, state.record, window, state.record.vector.append.extent⟩ ∧
      effect.2 = .accepted ∧ effect.1.book.latest state.record.lineage.stream = window := by
  let applied := (ChosenReplay.applyActivation rules state.record.lineage state.image install.original).1
  have choice : ChosenReplay.decide rules state.record.lineage state.image (installFrame state install) =
      (ChosenReplay.installWindow state.record.lineage applied install.original.grant, .accepted) := by
    simp only [ChosenReplay.decide, installFrame, ite_eq_left allowed, applied]
  have latest :
      (ChosenReplay.installWindow state.record.lineage applied install.original.grant).book.latest
        state.record.lineage.stream = install.original.grant.version := by
    simp [ChosenReplay.installWindow, ChosenReplay.advancePosition, SnapshotAdmission.setSlot]
  simp [activate, ite_eq_left (And.intro exactBinding durable), choice, exactBinding.2.1, exactBinding.2.2, latest]

theorem replay_refuses_a_different_realized_vector
    (rules : Rules slots Payload Ticket) (alias : Alias)
    (state : Sealed slots Payload) (install : Install slots Payload Ticket)
    (installed : Install slots Payload Ticket → Prop)
    (substituted : install.mounted ≠ state.record.vector) :
    activate rules alias state install installed = none := by
  have denied : ¬ (Matches alias state install ∧ installed install) := by
    intro allowed
    exact substituted allowed.1.2.1
  simp only [activate, ite_eq_right denied]

structure Cleanup (slots : Nat) where
  lineage : Lineage
  anchor : UnifiedSource.Anchor slots Nat
  extent : PoolState.Identity
  key : ChannelLifecycle.Key
  binding : RegistrationRecovery.Binding

def MaySettle (state : Activated slots Payload) (proof : Cleanup slots) (gone : Cleanup slots → Prop) : Prop :=
  proof.lineage = state.record.lineage ∧ proof.anchor = state.record.anchor ∧ gone proof ∧
  ∃ receipt ∈ state.record.vector.recovery,
    receipt.extent = proof.extent ∧ receipt.demand.key = proof.key ∧ receipt.demand.binding = proof.binding

theorem exact_recovery_cleanup_never_releases_the_append_extent
    {state : Activated slots Payload} {proof : Cleanup slots} {gone : Cleanup slots → Prop}
    (distinct : (state.record.vector.receipts.map Receipt.extent).Nodup)
    (settles : MaySettle state proof gone) : proof.extent ≠ state.record.vector.append.extent := by
  obtain ⟨receipt, member, identity, _, _⟩ := settles.2.2.2
  intro same
  exact (List.nodup_cons.mp distinct).1 (List.mem_map.mpr ⟨receipt, member, identity.trans same⟩)

theorem exact_cleanup_needs_evidence_for_its_original_pool_and_binding
    {state : Activated slots Payload} {proof : Cleanup slots} {gone : Cleanup slots → Prop}
    (settles : MaySettle state proof gone) :
    ∃ receipt ∈ state.record.vector.recovery, receipt.extent.pool = proof.extent.pool ∧
      receipt.demand.key = proof.key ∧ receipt.demand.binding = proof.binding ∧
      proof.lineage = state.record.lineage ∧ proof.anchor = state.record.anchor ∧ gone proof := by
  obtain ⟨receipt, member, identity, key, binding⟩ := settles.2.2.2
  exact ⟨receipt, member, congrArg PoolState.Identity.pool identity, key, binding, settles.1, settles.2.1, settles.2.2.1⟩

theorem the_exact_cleanup_refunds_only_its_named_local_row
    [DecidableEq Ticket] {rules : PoolState.Rules Ticket} {localPool : PoolState.Image Ticket}
    {state : Activated slots Payload} {proof : Cleanup slots}
    {row : PoolState.Row Ticket} (earlier later : List (PoolState.Row Ticket))
    (exactRows : localPool.rows = earlier ++ row :: later)
    (safe : PoolState.Sound rules localPool)
    (sameRow : row.identity = proof.extent ∧ row.key = proof.key ∧ row.binding = proof.binding)
    (closed : CopyFence.Closed localPool.gate row.key)
    (effect : MaySettle state proof (fun request => request = proof ∧ row.provider.erased = true))
    (distinct : (state.record.vector.receipts.map Receipt.extent).Nodup) :
    let after := {localPool with rows := earlier ++ later}
    PoolState.Step rules localPool after ∧ PoolState.Sound rules after ∧
      ProviderIOClosure.StableAbsence row.provider ∧
      proof.extent.pool = rules.authority.custodian ∧ row.identity ≠ state.record.vector.append.extent ∧
      ∀ survivor ∈ localPool.rows, survivor.identity ≠ proof.extent → survivor ∈ after.rows := by
  have refund : PoolState.Step rules localPool {localPool with rows := earlier ++ later} :=
    .refund earlier later exactRows closed effect.2.2.1.2
  have member : row ∈ localPool.rows := by rw [exactRows]; simp
  have recordedPool := safe.localPool row member
  refine ⟨refund, PoolState.every_local_decision_preserves_capacity_and_exact_paid_grants safe refund,
    PoolState.a_physical_refund_requires_its_own_provider_absence safe member effect.2.2.1.2,
    sameRow.1 ▸ recordedPool, ?_, ?_⟩
  · rw [sameRow.1]
    exact exact_recovery_cleanup_never_releases_the_append_extent distinct effect
  · intro survivor present different
    rw [exactRows] at present
    rcases List.mem_append.mp present with front | suffix
    · exact List.mem_append_left _ front
    · rcases List.mem_cons.mp suffix with rfl | back
      · exact False.elim (different sameRow.1)
      · exact List.mem_append_right _ back

#print axioms accepted_reservation_retains_the_exact_plan
#print axioms an_equal_price_vector_with_a_different_scope_cannot_seal
#print axioms choosing_the_realized_vector_seals_the_actual_source_in_the_same_position
#print axioms an_activation_with_the_original_receipts_uses_its_source_alias_and_exact_extent
#print axioms replay_refuses_a_different_realized_vector
#print axioms exact_recovery_cleanup_never_releases_the_append_extent
#print axioms exact_cleanup_needs_evidence_for_its_original_pool_and_binding
#print axioms the_exact_cleanup_refunds_only_its_named_local_row

end RealizedSource
