import CopyFence
import RecoveryCapacity
import FundedSeal
import SourceOutcomes

set_option warningAsError true

namespace SettlementComposition

variable {Pool Payload Voter Ticket : Type} {width : Nat}

abbrev Decision (width : Nat) (Pool : Type) := SourceOutcomes.Decision width (FundedSeal.Intent Pool)

inductive Participant (Pool : Type) where
  | pool (identity : Pool)
  | target
  deriving DecidableEq

abbrev Receipt (width : Nat) (Pool : Type) :=
  SourceOutcomes.Receipt width (FundedSeal.Intent Pool) (Participant Pool)

def outcome (decision : Decision width Pool) : FundedSeal.Outcome Pool :=
  match decision.result with
  | .canceled => .aborted decision.binding
  | .committed => .sealed decision.binding

def Chosen (source : FundedSeal.Source Payload Pool) (decision : Decision width Pool) : Prop :=
  decision.key.serial = decision.binding.serial ∧
  source.settled decision.key.serial = some (outcome decision)

structure Debit (width : Nat) (Pool : Type) where
  decision : Decision width Pool
  pool : Pool
  bytes : Nat

structure Local (width : Nat) (Pool Ticket : Type) where
  gate : ChannelLifecycle.Store
  provider : ProviderIOClosure.State Ticket
  debit : Option (Debit width Pool)

def ExactDebit (localState : Local width Pool Ticket) (decision : Decision width Pool)
    (pool : Pool) (required : Nat) : Prop :=
  ∃ debit, localState.debit = some debit ∧ debit.decision = decision ∧ debit.pool = pool ∧ required ≤ debit.bytes

theorem a_charged_copy_uses_its_own_decision_and_pool
    {localState : Local width Pool Ticket} {decision : Decision width Pool} {pool : Pool}
    {required : Nat} (charged : ExactDebit localState decision pool required) :
    ∃ debit, localState.debit = some debit ∧ debit.decision = decision ∧ debit.pool = pool ∧ required ≤ debit.bytes := by
  obtain ⟨debit, stored, exactScope, location, enough⟩ := charged
  exact ⟨debit, stored, exactScope, location, enough⟩

structure AbortSettlement (localState : Local width Pool Ticket) (decision : Decision width Pool)
    (pool : Pool) (originalKey : ChannelLifecycle.Key) (required : Nat) : Prop where
  fence : CopyFence.Closed localState.gate originalKey
  sound : ProviderIOClosure.Sound localState.provider
  released : localState.provider.target = false
  charge : localState.provider.erased = true ∨ ExactDebit localState decision pool required

theorem a_pool_abort_receipt_preserves_physical_backing
    {localState : Local width Pool Ticket} {decision : Decision width Pool} {pool : Pool}
    {originalKey : ChannelLifecycle.Key} {required : Nat}
    (settled : AbortSettlement localState decision pool originalKey required) :
    (∀ binding, ChannelLifecycle.decideAcquire localState.gate originalKey binding = .refuse) ∧
    (ProviderIOClosure.StableAbsence localState.provider ∨
      (∃ record, localState.provider.custodian = some record ∧ ProviderIOClosure.Covers localState.provider record) ∧
      (∃ debit, localState.debit = some debit ∧ debit.decision = decision ∧ debit.pool = pool ∧ required ≤ debit.bytes)) := by
  refine ⟨CopyFence.closed_copy_refuses_every_binding settled.fence, ?_⟩
  by_cases erased : localState.provider.erased = true
  · exact .inl (settled.sound.erasure erased)
  · have charged := settled.charge.resolve_left erased
    rcases ProviderIOClosure.release_needs_stable_absence_or_reserved_custody settled.sound settled.released with
      stable | custody
    · exact .inl stable
    · exact .inr ⟨custody, a_charged_copy_uses_its_own_decision_and_pool charged⟩

def poolAmount [DecidableEq Pool] (pool : Pool) (bytes : Nat) (query : Pool) : Nat :=
  if query = pool then bytes else 0

theorem a_live_old_write_can_move_to_exact_local_custody_without_new_capacity
    [DecidableEq Ticket] [DecidableEq Pool] (state : ProviderIOClosure.State Ticket)
    (record : ProviderIOClosure.Custody Ticket) (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (ticket : Ticket) (pending : ProviderIOClosure.MayWrite state ticket)
    (covers : ProviderIOClosure.Covers state record) (room : reserve record)
    (ledger : PreparedCapacity.Occupancy Pool) (pool : Pool) (bytes : Nat)
    (held : bytes ≤ ledger.prepared pool) :
    ∃ after, ProviderIOClosure.Trace reserve state after ∧ after.target = false ∧
      after.custodian = some record ∧ ProviderIOClosure.MayWrite after ticket ∧
      ∀ query, PreparedCapacity.usage (PreparedCapacity.attributeToSeal ledger (poolAmount pool bytes)) query =
        PreparedCapacity.usage ledger query := by
  obtain ⟨after, steps, returned, custody, stillPending⟩ :=
    ProviderIOClosure.target_release_can_keep_a_write_pending state record reserve ticket pending covers room
  refine ⟨after, steps, returned, custody, stillPending, ?_⟩
  apply PreparedCapacity.moving_owned_credit_to_sealed_accounting_preserves_usage
  intro query
  by_cases same : query = pool
  · subst query
    simpa [poolAmount] using held
  · simp [poolAmount, same]

structure SealAtCut (width : Nat) (Pool Payload : Type) where
  decision : Decision width Pool
  history : List (OrderedApplication.Command Payload)

def MatchesCut (attached : SealAtCut width Pool Payload) (decision : Decision width Pool)
    (history : List (OrderedApplication.Command Payload)) : Prop :=
  attached.decision = decision ∧ attached.history = history

theorem install_certifies_exact_decision_and_cut {attached : SealAtCut width Pool Payload}
    {decision : Decision width Pool} {history : List (OrderedApplication.Command Payload)}
    (matched : MatchesCut attached decision history) :
    attached.decision = decision ∧ attached.history = history := by
  exact ⟨matched.1, matched.2⟩

structure TargetInstall (certified : SealAtCut width Pool Payload → Prop) (decision : Decision width Pool)
    (Voter : Type) where
  context : RecoveryCapacity.Context Payload Voter
  exactPlacement : context.target = decision.binding.target
  cut : RecoveryCapacity.Cut context
  installed : RecoveryCapacity.Installation cut
  attached : SealAtCut width Pool Payload
  chosen : certified attached
  attachedMatches : MatchesCut attached decision cut.history

theorem a_certified_target_ack_has_exact_replay_at_a_recovery_majority
    {certified : SealAtCut width Pool Payload → Prop} {decision : Decision width Pool}
    (install : TargetInstall certified decision Voter)
    (available : Voter → Bool)
    (quorum : JournalRefinement.Majority install.installed.family.ledger.members available) :
    install.attached.decision = decision ∧ install.attached.history = install.cut.history ∧
    install.context.target = decision.binding.target ∧ install.context.authorizedTarget install.installed.family ∧
    ∃ voter ∈ install.installed.family.ledger.members, available voter = true ∧
      install.installed.family.installed voter install.cut.history := by
  have exactCut := install_certifies_exact_decision_and_cut install.attachedMatches
  exact ⟨exactCut.1, exactCut.2, install.exactPlacement,
    RecoveryCapacity.every_recovery_majority_reads_the_exact_charged_cut install.installed available quorum⟩

structure Evidence (width : Nat) (Pool Ticket Payload Voter : Type) where
  issue : SourceOutcomes.Key width → FundedSeal.Intent Pool → Prop
  plan : SourceOutcomes.Key width → FundedSeal.Intent Pool → List (Participant Pool) → Prop
  localState : Decision width Pool → Pool → Local width Pool Ticket
  originalKey : FundedSeal.Intent Pool → Pool → ChannelLifecycle.Key
  footprint : Decision width Pool → Pool → Nat
  closedTarget : FundedSeal.Intent Pool → Prop
  certifiedSeal : SealAtCut width Pool Payload → Prop

def Settled (evidence : Evidence width Pool Ticket Payload Voter) (receipt : Receipt width Pool) : Prop :=
  let decision := receipt.decision
  match decision.result, receipt.participant with
  | .canceled, .pool pool =>
      AbortSettlement (evidence.localState decision pool) decision pool
        (evidence.originalKey decision.binding pool) (evidence.footprint decision pool)
  | .committed, .pool pool =>
      Nonempty (TargetInstall evidence.certifiedSeal decision Voter) ∧
      ExactDebit (evidence.localState decision pool) decision pool (evidence.footprint decision pool)
  | .canceled, .target => evidence.closedTarget decision.binding
  | .committed, .target => Nonempty (TargetInstall evidence.certifiedSeal decision Voter)

def authority (source : FundedSeal.Source Payload Pool) (evidence : Evidence width Pool Ticket Payload Voter) :
    SourceOutcomes.Authority width (FundedSeal.Intent Pool) (Participant Pool) where
  planned := evidence.plan
  chosen := Chosen source
  settled := fun receipt => Chosen source receipt.decision ∧ Settled evidence receipt
  authenticIssue := evidence.issue

theorem the_source_choice_remains_valid_for_late_participant_delivery
    {limits : Kernel.Limits} {live : FundedSeal.Receipt Pool → Prop}
    {first last : FundedSeal.Source Payload Pool} {decision : Decision width Pool}
    (unresolved : FundedSeal.Unresolved first) (chosen : Chosen first decision)
    (trace : FundedSeal.Trace limits live first last) : Chosen last decision :=
  ⟨chosen.1, FundedSeal.a_chosen_seal_or_abort_survives_every_later_trace unresolved chosen.2 trace⟩

theorem retirement_fills_the_reserved_abort_result_before_any_participant_replies
    [DecidableEq (FundedSeal.Intent Pool)] [DecidableEq Pool] {limits : Kernel.Limits}
    {live : FundedSeal.Receipt Pool → Prop} {source : FundedSeal.Source Payload Pool} {writer : Kernel.Writer}
    {intent : FundedSeal.Intent Pool} (authorized : source.stream.authority = .active writer)
    (prepared : source.pending = some intent)
    (evidence : Evidence width Pool Ticket Payload Voter)
    (book : SourceOutcomes.Book width (FundedSeal.Intent Pool) (Participant Pool))
    (key : SourceOutcomes.Key width) (serial : key.serial = intent.serial)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (Participant Pool))
    (found : SourceOutcomes.lookup book key = some row) (binding : row.binding = intent)
    (unresolved : row.result = none) :
    ∃ closed, FundedSeal.Step limits live source closed ∧ closed.stream.authority = .retired ∧
      SourceOutcomes.apply (authority closed evidence) book (.resolve ⟨key, intent, .canceled⟩) =
        SourceOutcomes.setRow book key.slot (some {row with result := some .canceled}) := by
  obtain ⟨closed, transition, retired, _, aborted⟩ :=
    FundedSeal.retiring_a_prepared_stream_yields_its_exact_abort_without_pool_access
      (limits := limits) (live := live) authorized prepared
  have chosen : Chosen closed (⟨key, intent, .canceled⟩ : Decision width Pool) :=
    ⟨serial, by simpa [outcome, serial] using aborted⟩
  exact ⟨closed, transition, retired,
    SourceOutcomes.deciding_a_reserved_row_needs_no_result_slot found binding unresolved chosen⟩

theorem an_exact_participant_receipt_updates_only_its_owed_result
    [DecidableEq (FundedSeal.Intent Pool)] [DecidableEq Pool]
    (source : FundedSeal.Source Payload Pool) (evidence : Evidence width Pool Ticket Payload Voter)
    (book : SourceOutcomes.Book width (FundedSeal.Intent Pool) (Participant Pool))
    (receipt : Receipt width Pool)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (Participant Pool))
    (found : SourceOutcomes.lookup book receipt.decision.key = some row)
    (binding : receipt.decision.binding = row.binding) (result : row.result = some receipt.decision.result)
    (chosen : Chosen source receipt.decision) (finished : Settled evidence receipt) :
    SourceOutcomes.apply (authority source evidence) book (.acknowledge receipt) =
      SourceOutcomes.setRow book receipt.decision.key.slot
        (some {row with waiting := row.waiting.filter (· != receipt.participant)}) := by
  have backed : (authority source evidence).settled receipt := ⟨chosen, finished⟩
  simp [SourceOutcomes.apply, found, SourceOutcomes.MayAccept, binding, result, backed]

theorem the_last_exact_receipt_allows_compaction_without_changing_other_rows
    [DecidableEq (FundedSeal.Intent Pool)] [DecidableEq Pool]
    (source : FundedSeal.Source Payload Pool) (evidence : Evidence width Pool Ticket Payload Voter)
    (book : SourceOutcomes.Book width (FundedSeal.Intent Pool) (Participant Pool))
    (receipt : Receipt width Pool)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (Participant Pool))
    (found : SourceOutcomes.lookup book receipt.decision.key = some row)
    (binding : receipt.decision.binding = row.binding) (result : row.result = some receipt.decision.result)
    (chosen : Chosen source receipt.decision) (finished : Settled evidence receipt)
    (last : row.waiting = [receipt.participant])
    (other : SourceOutcomes.Key width) (different : other.slot ≠ receipt.decision.key.slot) :
    let acknowledged := SourceOutcomes.apply (authority source evidence) book (.acknowledge receipt)
    let compacted := SourceOutcomes.apply (authority source evidence) acknowledged (.compact receipt.decision.key)
    compacted.rows receipt.decision.key.slot = none ∧ compacted.issued = book.issued ∧
      SourceOutcomes.lookup compacted other = SourceOutcomes.lookup book other := by
  let auth := authority source evidence
  let updatedRow : SourceOutcomes.Row (FundedSeal.Intent Pool) (Participant Pool) := {row with waiting := []}
  let acknowledged := SourceOutcomes.setRow book receipt.decision.key.slot (some updatedRow)
  have intake : SourceOutcomes.apply auth book (.acknowledge receipt) = acknowledged := by
    rw [an_exact_participant_receipt_updates_only_its_owed_result
      source evidence book receipt row found binding result chosen finished]
    simp [acknowledged, updatedRow, last]
  have matched := (Option.filter_eq_some_iff.mp found).2
  have lookupUpdated : SourceOutcomes.lookup acknowledged receipt.decision.key = some updatedRow := by
    simp [acknowledged, updatedRow, SourceOutcomes.lookup, SourceOutcomes.setRow, matched]
  have settled : SourceOutcomes.MayCompact updatedRow := by simp [updatedRow, SourceOutcomes.MayCompact, result]
  have returned := SourceOutcomes.a_later_settled_slot_can_be_returned_independently
    (auth := auth) lookupUpdated settled different
  have otherBefore : SourceOutcomes.lookup acknowledged other = SourceOutcomes.lookup book other := by
    simp [acknowledged, SourceOutcomes.lookup, SourceOutcomes.setRow, different]
  dsimp only
  rw [intake]
  exact ⟨returned.2.1, returned.1, returned.2.2.trans otherBefore⟩

#print axioms a_charged_copy_uses_its_own_decision_and_pool
#print axioms a_pool_abort_receipt_preserves_physical_backing
#print axioms a_live_old_write_can_move_to_exact_local_custody_without_new_capacity
#print axioms install_certifies_exact_decision_and_cut
#print axioms a_certified_target_ack_has_exact_replay_at_a_recovery_majority
#print axioms the_source_choice_remains_valid_for_late_participant_delivery
#print axioms retirement_fills_the_reserved_abort_result_before_any_participant_replies
#print axioms an_exact_participant_receipt_updates_only_its_owed_result
#print axioms the_last_exact_receipt_allows_compaction_without_changing_other_rows

end SettlementComposition
