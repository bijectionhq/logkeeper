import LatePrepare
import UnifiedSource

set_option warningAsError true

namespace AbortCut

open ChannelLifecycle (Key)
open RegistrationRecovery (Binding)
open LatePrepare (World Adm Trace)
open UnifiedSource (Command)
open SettlementComposition (Participant)

variable {slots : Nat} {Payload Ticket Voter : Type}

structure Plan (slots : Nat) where
  move : SourceOutcomes.Key slots
  intent : FundedSeal.Intent Nat
  key : Key
  binding : Binding

def AbortAt (limits : Kernel.Limits) (source : UnifiedSource.Rules slots Nat Payload Ticket)
    (initial : UnifiedSource.State slots Nat Payload)
    (ledger : PrefixAgreement.Ledger Voter (Command slots Nat Payload Ticket))
    (registered : Plan slots → Prop) (plan : Plan slots) : Prop :=
  registered plan ∧ ∃ ballot commands row, PrefixAgreement.Chosen ledger ballot commands ∧
    SourceOutcomes.lookup (UnifiedSource.replay limits source initial commands).1.core.book plan.move = some row ∧
    row.binding = plan.intent ∧ row.result = some .canceled ∧
    Participant.pool plan.key.handle.custodian ∈ row.waiting

def verifies (plan : Plan slots) (aborted : Prop) (key : Key) (binding : Binding) : Prop :=
  key = plan.key ∧ binding = plan.binding ∧ aborted

theorem a_chosen_abort_receipt_has_the_original_physical_scope
    {plan : Plan slots} {aborted : Prop} {key : Key} {binding : Binding}
    (received : verifies plan aborted key binding) : key = plan.key :=
  received.1

def abortCommand (retire : Bool) (writer : Kernel.Writer) (move : SourceOutcomes.Key slots) :
    Command slots Nat Payload Ticket :=
  if retire then .retire writer else .cancel writer move

theorem either_ordered_abort_certifies_the_exact_result_and_rejects_later_seals
    (limits : Kernel.Limits) (source : UnifiedSource.Rules slots Nat Payload Ticket)
    (initial : UnifiedSource.State slots Nat Payload)
    (ledger : PrefixAgreement.Ledger Voter (Command slots Nat Payload Ticket))
    (registered : Plan slots → Prop) (plan : Plan slots) (original : registered plan)
    (earlier : List (Command slots Nat Payload Ticket)) (ballot position : Nat)
    (writer : Kernel.Writer) (retire : Bool)
    (row : SourceOutcomes.Row (FundedSeal.Intent Nat) (Participant Nat))
    (chosen : PrefixAgreement.Chosen ledger ballot (earlier ++ [abortCommand retire writer plan.move]))
    (ready : UnifiedSource.Ready (UnifiedSource.replay limits source initial earlier).1.core plan.move row)
    (writerIsCurrent : (UnifiedSource.replay limits source initial earlier).1.core.stream.authority = .active writer)
    (matching : row.binding = plan.intent) (participant : .pool plan.key.handle.custodian ∈ row.waiting) :
    AbortAt limits source initial ledger registered plan ∧
      ∀ receipts,
        let after := (UnifiedSource.replay limits source initial (earlier ++ [abortCommand retire writer plan.move])).1.core
        UnifiedSource.decide limits source after position (.fundedSeal writer plan.move receipts) = (after, .refused) := by
  let before := (UnifiedSource.replay limits source initial earlier).1
  let full := earlier ++ [abortCommand retire writer plan.move]
  let next := (UnifiedSource.replay limits source initial full).1.core
  let abortedRow := {row with result := some SourceOutcomes.Resolution.canceled}
  have exactCut : next =
      (UnifiedSource.decide limits source before.core (before.position + 1) (abortCommand retire writer plan.move)).1 := by
    simp only [next, full, UnifiedSource.replay_append]
    rfl
  have found : SourceOutcomes.lookup next.book plan.move = some abortedRow := by
    rw [exactCut]
    cases retire
    · exact UnifiedSource.a_prepared_cancellation_records_its_exact_abort limits source
        before.core (before.position + 1) writer plan.move row ready writerIsCurrent
    · exact (UnifiedSource.a_prepared_retirement_records_its_abort_at_the_same_position limits source
        before.core (before.position + 1) writer plan.move row ready (Or.inl writerIsCurrent)).2
  refine ⟨⟨original, ballot, full, abortedRow, chosen, found, matching, rfl, participant⟩, ?_⟩
  intro receipts
  exact UnifiedSource.a_decided_move_refuses_a_delivered_seal limits source next position writer plan.move
    receipts abortedRow found (by intro impossible; cases impossible)

def forAbort (rules : LatePrepare.Rules Ticket) (plan : Plan slots) (aborted : Prop) : LatePrepare.Rules Ticket :=
  {rules with chosenAbort := verifies plan aborted}

theorem a_delayed_request_can_prepare_after_abort_and_is_then_fenced_without_refund
    [DecidableEq Ticket]
    (limits : Kernel.Limits) (source : UnifiedSource.Rules slots Nat Payload Ticket)
    (initial : UnifiedSource.State slots Nat Payload)
    (ledger : PrefixAgreement.Ledger Voter (Command slots Nat Payload Ticket))
    (registered : Plan slots → Prop) (plan : Plan slots)
    (rules : LatePrepare.Rules Ticket) (world : World Ticket)
    (certified : AbortAt limits source initial ledger registered plan)
    (issued : plan.key.handle.nonce ≤ world.gate.issued)
    (delayed : Adm rules world plan.key plan.binding) :
    let rules := forAbort rules plan (AbortAt limits source initial ledger registered plan)
    ∃ funded fenced, Trace rules world funded ∧ Trace rules funded fenced ∧
      funded.gate.grants plan.key = some plan.binding ∧
      rules.extent plan.key ∈ funded.ledger.debits ∧
      fenced.ledger = funded.ledger ∧ CopyFence.Closed fenced.gate plan.key := by
  let exactRules := forAbort rules plan (AbortAt limits source initial ledger registered plan)
  let funded := LatePrepare.prepare world plan.key plan.binding (rules.extent plan.key)
  obtain ⟨prepare, held, paid, _⟩ :=
    LatePrepare.a_late_preparation_has_the_same_exact_backing_and_retry_result exactRules world plan.key plan.binding
      ⟨delayed.planned, delayed.gateRoom, delayed.openScope, delayed.correctPool, delayed.fresh, delayed.empty, delayed.room⟩
  have sameIssuance : plan.key.handle.nonce ≤ funded.gate.issued := issued
  have verified : exactRules.chosenAbort plan.key plan.binding := ⟨rfl, rfl, certified⟩
  obtain ⟨fence, closed, unchanged⟩ :=
    LatePrepare.a_chosen_exact_abort_fences_even_an_empty_scope exactRules funded plan.key plan.binding
      verified sameIssuance (.inr held)
  exact ⟨funded, _, .next (.same _) prepare, .next (.same _) fence, held, paid, unchanged, closed⟩

#print axioms a_chosen_abort_receipt_has_the_original_physical_scope
#print axioms either_ordered_abort_certifies_the_exact_result_and_rejects_later_seals
#print axioms a_delayed_request_can_prepare_after_abort_and_is_then_fenced_without_refund

end AbortCut
