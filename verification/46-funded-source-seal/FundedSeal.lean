import Kernel
import PreparedCapacity

set_option warningAsError true

namespace FundedSeal

variable {Payload Pool : Type}

structure Intent (Pool : Type) where
  serial : Nat
  target : Kernel.Placement
  needs : Pool → Nat

structure Receipt (Pool : Type) where
  intent : Intent Pool
  pool : Pool
  bytes : Nat

def Matches (intent : Intent Pool) (pool : Pool) (receipt : Receipt Pool) : Prop :=
  receipt.intent = intent ∧ receipt.pool = pool ∧ receipt.bytes = intent.needs pool

def FullVector (live : Receipt Pool → Prop) (intent : Intent Pool) : Prop :=
  ∀ pool, 0 < intent.needs pool → ∃ receipt, live receipt ∧ Matches intent pool receipt

private theorem matches_intent {intent : Intent Pool} {pool : Pool} {receipt : Receipt Pool}
    (matched : Matches intent pool receipt) : receipt.intent = intent := by
  exact matched.1

theorem a_vector_uses_exact_live_receipts {live : Receipt Pool → Prop} {intent : Intent Pool}
    (full : FullVector live intent) (pool : Pool) (nonzero : 0 < intent.needs pool) :
    ∃ receipt, live receipt ∧ receipt.intent = intent ∧ receipt.pool = pool ∧
      receipt.bytes = intent.needs pool := by
  obtain ⟨receipt, held, matched⟩ := full pool nonzero
  exact ⟨receipt, held, matches_intent matched, matched.2⟩

inductive Outcome (Pool : Type) where
  | sealed (intent : Intent Pool)
  | aborted (intent : Intent Pool)

structure Source (Payload Pool : Type) where
  stream : Kernel.State Payload
  issued : Nat
  pending : Option (Intent Pool)
  settled : Nat → Option (Outcome Pool)

def record (source : Source Payload Pool) (serial : Nat) (outcome : Outcome Pool) :
    Source Payload Pool :=
  {source with pending := none, settled := fun query =>
    if query = serial then some outcome else source.settled query}

def retire (source : Source Payload Pool) : Source Payload Pool :=
  let closed := match source.pending with
    | none => source
    | some intent => record source intent.serial (.aborted intent)
  {closed with stream := {source.stream with authority := .retired}}

def Serving (stream : Kernel.State Payload) : Prop :=
  ∃ writer, stream.authority = .active writer

def Unresolved (source : Source Payload Pool) : Prop :=
  ∀ intent, source.pending = some intent → source.settled intent.serial = none

inductive Step (limits : Kernel.Limits) (live : Receipt Pool → Prop) :
    Source Payload Pool → Source Payload Pool → Prop
  | plan {source} (intent : Intent Pool) (serves : Serving source.stream)
      (empty : source.pending = none) (next : intent.serial = source.issued + 1)
      (fresh : source.settled intent.serial = none) :
      Step limits live source {source with issued := intent.serial, pending := some intent}
  | abort {source} (intent : Intent Pool) (serves : Serving source.stream)
      (pending : source.pending = some intent) :
      Step limits live source (record source intent.serial (.aborted intent))
  | fundedSeal {source writer} (intent : Intent Pool) (authorized : source.stream.authority = .active writer)
      (advances : writer.placement.generation < intent.target.generation)
      (relocates : writer.placement.group ≠ intent.target.group)
      (pending : source.pending = some intent) (funded : FullVector live intent) :
      Step limits live source
        {record source intent.serial (.sealed intent) with
          stream := {source.stream with authority := .sealed intent.target writer}}
  | retireSource {source writer} (authorized : source.stream.authority = .active writer) :
      Step limits live source (retire source)
  | activate {source target writer} (installed : List (Kernel.Entry Payload))
      (sealed : source.stream.authority = .sealed target writer) (exact : installed = source.stream.history) :
      Step limits live source {source with stream :=
        {source.stream with history := installed, authority := .active {writer with placement := target}}}
  | stream {source next} (before : Serving source.stream) (after : Serving next)
      (transition : Kernel.Step limits source.stream next) :
      Step limits live source {source with stream := next}

inductive Trace (limits : Kernel.Limits) (live : Receipt Pool → Prop) :
    Source Payload Pool → Source Payload Pool → Prop
  | same (source) : Trace limits live source source
  | next {first before after} : Trace limits live first before → Step limits live before after →
      Trace limits live first after

theorem every_source_step_projects_to_the_stream
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {before after : Source Payload Pool}
    (step : Step limits live before after) :
    before.stream = after.stream ∨ Kernel.Step limits before.stream after.stream := by
  cases step with
  | plan => exact .inl rfl
  | abort => exact .inl rfl
  | fundedSeal intent authorized advances relocates _ _ =>
      exact .inr (.freeze intent.target authorized advances relocates)
  | retireSource authorized =>
      exact .inr (show Kernel.Step limits _ {before.stream with authority := .retired} from .retire (Or.inl authorized))
  | activate installed sealed exactCut => exact .inr (.activate installed sealed exactCut)
  | stream _ _ transition => exact .inr transition

theorem source_trace_refines_the_reference_stream
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {first last : Source Payload Pool}
    (trace : Trace limits live first last) : Kernel.Trace limits first.stream last.stream := by
  induction trace with
  | same => exact .same _
  | next _ step prior =>
      rcases every_source_step_projects_to_the_stream step with equal | transition
      · exact equal ▸ prior
      · exact .next prior transition

theorem every_step_preserves_unresolved_pending
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {before after : Source Payload Pool}
    (sound : Unresolved before) (step : Step limits live before after) : Unresolved after := by
  cases step with
  | plan intent _ _ _ fresh =>
      intro other pending
      have same := Option.some.inj pending
      subst other
      exact fresh
  | abort => simp [Unresolved, record]
  | fundedSeal => simp [Unresolved, record]
  | retireSource =>
      unfold retire
      cases pending : before.pending <;> simp [Unresolved, pending, record]
  | activate => exact sound
  | stream => exact sound

private theorem resolving_pending_preserves_earlier_choice
    {source : Source Payload Pool} {intent : Intent Pool} {id : Nat} {outcome : Outcome Pool}
    (fresh : Unresolved source) (pending : source.pending = some intent)
    (chosen : source.settled id = some outcome) (new : Outcome Pool) :
    (record source intent.serial new).settled id = some outcome := by
  have distinct : id ≠ intent.serial := by
    intro same
    subst id
    rw [fresh intent pending] at chosen
    cases chosen
  simpa [record, distinct] using chosen

theorem every_step_preserves_the_earlier_exact_outcome
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {before after : Source Payload Pool}
    {id : Nat} {outcome : Outcome Pool} (sound : Unresolved before)
    (chosen : before.settled id = some outcome) (step : Step limits live before after) :
    after.settled id = some outcome := by
  cases step with
  | plan => exact chosen
  | abort intent _ pending =>
      exact resolving_pending_preserves_earlier_choice sound pending chosen (.aborted intent)
  | fundedSeal intent _ _ _ pending _ =>
      exact resolving_pending_preserves_earlier_choice sound pending chosen (.sealed intent)
  | retireSource =>
      unfold retire
      cases pending : before.pending with
      | none => simpa [pending] using chosen
      | some intent =>
          simpa [pending] using resolving_pending_preserves_earlier_choice sound pending chosen (.aborted intent)
  | activate => exact chosen
  | stream => exact chosen

theorem a_chosen_seal_or_abort_survives_every_later_trace
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {first last : Source Payload Pool}
    {id : Nat} {outcome : Outcome Pool} (sound : Unresolved first)
    (chosen : first.settled id = some outcome) (trace : Trace limits live first last) :
    last.settled id = some outcome := by
  suffices Unresolved last ∧ last.settled id = some outcome from this.2
  induction trace with
  | same => exact ⟨sound, chosen⟩
  | next _ step prior =>
      exact ⟨every_step_preserves_unresolved_pending prior.1 step,
        every_step_preserves_the_earlier_exact_outcome prior.1 prior.2 step⟩

theorem retiring_a_prepared_stream_yields_its_exact_abort_without_pool_access
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {source : Source Payload Pool} {writer}
    {intent : Intent Pool} (authorized : source.stream.authority = .active writer)
    (prepared : source.pending = some intent) :
    ∃ closed, Step limits live source closed ∧ closed.stream.authority = .retired ∧
      closed.pending = none ∧ closed.settled intent.serial = some (.aborted intent) := by
  refine ⟨retire source, .retireSource authorized, rfl, ?_, ?_⟩
  · simp [retire, prepared, record]
  · simp [retire, prepared, record]

theorem committing_a_full_vector_freezes_the_reference_and_does_not_change_pool_usage
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {source : Source Payload Pool} {writer}
    {intent : Intent Pool} (authorized : source.stream.authority = .active writer)
    (advances : writer.placement.generation < intent.target.generation)
    (relocates : writer.placement.group ≠ intent.target.group)
    (pending : source.pending = some intent) (funded : FullVector live intent)
    (ledger : PreparedCapacity.Occupancy Pool) (owned : ∀ pool, intent.needs pool ≤ ledger.prepared pool) :
    ∃ sealed, Step limits live source sealed ∧ sealed.stream.authority = .sealed intent.target writer ∧
      sealed.settled intent.serial = some (.sealed intent) ∧
      ∀ pool, PreparedCapacity.usage (PreparedCapacity.attributeToSeal ledger intent.needs) pool =
        PreparedCapacity.usage ledger pool := by
  let next := {record source intent.serial (.sealed intent) with
    stream := {source.stream with authority := .sealed intent.target writer}}
  refine ⟨next, .fundedSeal intent authorized advances relocates pending funded, rfl, ?_, ?_⟩
  · simp [next, record]
  · exact PreparedCapacity.moving_owned_credit_to_sealed_accounting_preserves_usage owned

def CanRelease (source : Source Payload Pool) (intent : Intent Pool) : Prop :=
  source.settled intent.serial = some (.aborted intent)

theorem retirement_at_the_next_owner_cannot_release_a_sealed_attempt
    {limits : Kernel.Limits} {live : Receipt Pool → Prop} {first last : Source Payload Pool}
    {intent : Intent Pool} (sound : Unresolved first)
    (sealed : first.settled intent.serial = some (.sealed intent))
    (trace : Trace limits live first last) : ¬ CanRelease last intent := by
  intro releases
  have kept := a_chosen_seal_or_abort_survives_every_later_trace sound sealed trace
  have exactAbort : last.settled intent.serial = some (.aborted intent) := by
    exact releases
  have conflicting : Outcome.sealed intent = Outcome.aborted intent :=
    Option.some.inj (kept.symm.trans exactAbort)
  cases conflicting

structure System (Payload Pool : Type) where
  source : Source Payload Pool
  issued : Receipt Pool → Prop
  held : Receipt Pool → Prop
  fenced : Receipt Pool → Prop

structure Sound (system : System Payload Pool) : Prop where
  unresolved : Unresolved system.source
  heldWhileEligible : ∀ receipt, system.issued receipt → ¬ CanRelease system.source receipt.intent →
    system.held receipt

inductive SystemStep (limits : Kernel.Limits) : System Payload Pool → System Payload Pool → Prop
  | choose {system next} (transition : Step limits system.issued system.source next) :
      SystemStep limits system {system with source := next}
  | prepare {system} (receipt : Receipt Pool) (openKey : ¬ system.fenced receipt) :
      SystemStep limits system {system with
        issued := fun query => system.issued query ∨ query = receipt
        held := fun query => system.held query ∨ query = receipt}
  | returnHold {system} (receipt : Receipt Pool) (abortEvidence : CanRelease system.source receipt.intent) :
      SystemStep limits system {system with
        held := fun query => system.held query ∧ query ≠ receipt
        fenced := fun query => system.fenced query ∨ query = receipt}
  | replacePool {system} : SystemStep limits system system

theorem any_pool_keeps_an_issued_hold_until_its_exact_abort
    {limits : Kernel.Limits} {before after : System Payload Pool}
    (sound : Sound before) (step : SystemStep limits before after) : Sound after := by
  cases step with
  | choose transition =>
      refine ⟨every_step_preserves_unresolved_pending sound.unresolved transition, ?_⟩
      intro receipt issued live
      apply sound.heldWhileEligible receipt issued
      intro abortEvidence
      exact live (every_step_preserves_the_earlier_exact_outcome sound.unresolved abortEvidence transition)
  | prepare receipt _ =>
      refine ⟨sound.unresolved, ?_⟩
      intro query issued live
      rcases issued with older | fresh
      · exact .inl (sound.heldWhileEligible query older live)
      · exact .inr fresh
  | returnHold receipt handed =>
      have exactAbort : CanRelease before.source receipt.intent := handed
      refine ⟨sound.unresolved, ?_⟩
      intro query issued live
      change before.held query ∧ query ≠ receipt
      exact ⟨sound.heldWhileEligible query issued live, fun alias => live (alias ▸ exactAbort)⟩
  | replacePool => exact sound

inductive SystemTrace (limits : Kernel.Limits) : System Payload Pool → System Payload Pool → Prop
  | same (system) : SystemTrace limits system system
  | next {first before after} : SystemTrace limits first before → SystemStep limits before after →
      SystemTrace limits first after

theorem arbitrary_reconciliation_preserves_receipt_backing
    {limits : Kernel.Limits} {first last : System Payload Pool}
    (sound : Sound first) (trace : SystemTrace limits first last) : Sound last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact any_pool_keeps_an_issued_hold_until_its_exact_abort prior step

theorem source_can_validate_backing_from_issued_receipts_without_new_pool_reads
    {system : System Payload Pool} {intent : Intent Pool} (sound : Sound system)
    (pending : system.source.pending = some intent) (received : FullVector system.issued intent) :
    FullVector system.held intent := by
  intro pool nonzero
  obtain ⟨receipt, issued, matched⟩ := received pool nonzero
  have notAborted : ¬ CanRelease system.source receipt.intent := by
    rw [matches_intent matched, CanRelease, sound.unresolved intent pending]
    simp
  exact ⟨receipt, sound.heldWhileEligible receipt issued notAborted, matched⟩

#print axioms a_vector_uses_exact_live_receipts
#print axioms every_source_step_projects_to_the_stream
#print axioms source_trace_refines_the_reference_stream
#print axioms every_step_preserves_unresolved_pending
#print axioms every_step_preserves_the_earlier_exact_outcome
#print axioms a_chosen_seal_or_abort_survives_every_later_trace
#print axioms retiring_a_prepared_stream_yields_its_exact_abort_without_pool_access
#print axioms committing_a_full_vector_freezes_the_reference_and_does_not_change_pool_usage
#print axioms retirement_at_the_next_owner_cannot_release_a_sealed_attempt
#print axioms any_pool_keeps_an_issued_hold_until_its_exact_abort
#print axioms arbitrary_reconciliation_preserves_receipt_backing
#print axioms source_can_validate_backing_from_issued_receipts_without_new_pool_reads

end FundedSeal
