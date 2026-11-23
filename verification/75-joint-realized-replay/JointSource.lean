import WorkerRosterCodec
import CompleteSettlement
import ReceiptReplay

set_option warningAsError true

namespace JointSource

open ChosenReplay (Lineage)
open CompleteSettlement (Control Window)
open EnvelopeCodec (Bytes)
open RealizedSource (Install Vector)
open UnifiedSource (Reply)

variable {slots width : Nat} {Payload Ticket : Type}

structure SealEvidence where
  realization : Bytes
  eligibility : Bytes
  readControl : Bytes

structure Image (slots : Nat) (Payload : Type) where
  source : ChosenReplay.Image slots Payload
  plans : Fin slots → Option (AllocationVector.Plan slots)
  seals : Fin slots → Option SealEvidence
  windows : Nat → Option Window
  receipts : ReceiptReplay.Rows Payload
  workers : Workers

structure Rules (width slots : Nat) (Payload Ticket : Type) where
  source : ChosenReplay.Rules slots Payload Ticket
  atoms : SealBody.Atoms width
  maxExtents : Nat
  alias : RealizedSource.Alias
  plan : AllocationVector.Plan slots → UnifiedSource.Participants Nat → Ticket → Prop
  preparation : Ticket → AllocationVector.Receipt → Prop
  sealedReads : Lineage → Nat → Bytes → Prop
  installed : SealEvidence → Install slots Payload Ticket → Prop
  maxWorkers : Nat
  lastEnrollment : Nat
  enrollmentFits : lastEnrollment < EnvelopeCodec.wordLimit width
  changeWorkers : Lineage → WorkerChange → Ticket → Prop
  closeVacant : Lineage → Kernel.Writer → Ticket → Prop
  nomination : Lineage → Kernel.Writer → Kernel.Writer → Nat → Ticket → Prop
  checkpoint : Lineage → Kernel.Writer → Nat → Ticket → Prop
  ordinaryWindow : ChosenReplay.Grant Ticket → PoolState.Identity → Prop
  append : FundedAppend.Request Payload Ticket → PoolState.Identity → Prop
  settlement : Ticket → CompleteSettlement.Attestation slots
  authenticSettlement : Ticket → Prop
  targetSettlement : RealizedSource.Record slots → Ticket → Prop
  canceledSettlement : AllocationVector.Plan slots → UnifiedSource.Receipt slots Nat → Ticket → Prop

inductive Command (slots : Nat) (Payload Ticket : Type) where
  | reserve (plan : AllocationVector.Plan slots) (evidence : Ticket)
  | seal (writer : Kernel.Writer) (key : SourceOutcomes.Key slots) (vector : Vector) (body : SealEvidence) (evidence : Ticket)
  | activate (install : Install slots Payload Ticket)
  | replaceWriter (expected successor : Kernel.Writer) (evidence : Ticket)
  | changeWorkers (change : WorkerChange) (evidence : Ticket)
  | retireVacant (expected : Kernel.Writer) (evidence : Ticket)
  | publishCheckpoint (writer : Kernel.Writer) (cut : Nat) (evidence : Ticket)
  | install (grant : ChosenReplay.Grant Ticket) (extent : PoolState.Identity)
  | append (request : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity)
  | stream (command : OrderedApplication.Command Payload)
  | cancel (writer : Kernel.Writer) (key : SourceOutcomes.Key slots)
  | retire (writer : Kernel.Writer)
  | acknowledge (receipt : UnifiedSource.Receipt slots Nat) (evidence : Ticket)
  | compact (key : SourceOutcomes.Key slots)
  | prune (alias : Nat)

structure Frame (slots : Nat) (Payload Ticket : Type) where
  lineage : Lineage
  position : Nat
  command : Command slots Payload Ticket

def setCell [DecidableEq α] (cells : α → β) (key : α) (value : β) : α → β :=
  fun query => if query = key then value else cells query

def participants (plan : AllocationVector.Plan slots) : UnifiedSource.Participants Nat :=
  .target :: (plan.demands.map AllocationVector.Demand.pool).eraseDups.map SettlementComposition.Participant.pool

def usesHandoff (image : Image slots Payload) (key : SourceOutcomes.Key slots) : Prop :=
  ∃ anchor, image.source.source.core.handoff = some anchor ∧ anchor.decision.key = key

def control (image : Image slots Payload) (lineage : Lineage) : Control slots Payload :=
  ⟨image.source.source, (fun slot => (image.seals slot).map SealEvidence.realization),
    image.windows (image.source.book.latest lineage.stream)⟩

def eligible (lineage : Lineage) (image : Image slots Payload) (frame : Frame slots Payload Ticket) : Prop :=
  frame.lineage = lineage ∧ frame.position = image.source.source.position + 1

def wireRecord (rules : Rules width slots Payload Ticket) (wire : Bytes) :
    Option (RealizedSource.Record slots) :=
  (SealBody.decode width rules.maxExtents wire).bind (SealBody.decodeRecord rules.atoms slots)

noncomputable def openWorkers (rules : Rules width slots Payload Ticket) (body : Bytes) : Option Workers :=
  WorkerRosterCodec.decode width rules.maxWorkers rules.lastEnrollment body

noncomputable def openSeal (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (key : SourceOutcomes.Key slots) :
    Option (RealizedSource.Record slots × SealEvidence × Workers) := do
  let record ← CompleteSettlement.openSlot rules.atoms rules.maxExtents (control image lineage) lineage key
  let evidence ← image.seals key.slot
  let workers ← openWorkers rules evidence.eligibility
  pure (record, evidence, workers)

def refuses (image : Image slots Payload) : Image slots Payload × Reply Payload :=
  ({image with source := ChosenReplay.advancePosition image.source}, .refused)

noncomputable def runSource (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (command : ChosenReplay.Command slots Payload Ticket) : Image slots Payload × Reply Payload :=
  let frame : ChosenReplay.Frame slots Payload Ticket := ⟨lineage, image.source.source.position + 1, command⟩
  let outcome := ChosenReplay.decide rules.source lineage image.source frame
  let receipts := ReceiptReplay.record image.receipts ⟨frame, outcome.2⟩
  ({image with source := outcome.1, receipts := ReceiptReplay.retain receipts outcome.1.source.core.stream.firstRetained},
    outcome.2)

def CurrentNomination (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (expected successor : Kernel.Writer) (evidence : Ticket) : Prop :=
  ∃ enrollment, image.workers.enrollment successor.holder = some enrollment ∧
    rules.nomination lineage expected successor enrollment evidence

def workerAdmissionOpen : Kernel.Authority → Bool
  | .active _ | .vacant _ => true
  | .sealed _ _ | .retired => false

noncomputable def applyWorkerChange (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (change : WorkerChange) (workers : Workers) : Image slots Payload × Reply Payload :=
  let unchanged := ({image with source := ChosenReplay.advancePosition image.source}, .accepted)
  let effect := match change, image.source.source.core.stream.authority with
    | .withdraw holder _, .active writer =>
        if holder = writer.holder then
          runSource rules lineage image (.source (.stream (.withdraw writer)))
        else unchanged
    | _, _ => unchanged
  ({effect.1 with workers := workers}, effect.2)

noncomputable def runSettlement (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (receipt : UnifiedSource.Receipt slots Nat) (evidence : Ticket) :
    Image slots Payload × Reply Payload := by
  classical
  let base := rules.source.append.regional.source lineage.stream
  let limits := rules.source.append.regional.limits lineage.stream
  let command : UnifiedSource.Command slots Nat Payload Ticket := .acknowledge receipt (some evidence)
  let apply := fun localRules =>
    let result := UnifiedSource.decide limits localRules image.source.source.core (image.source.source.position + 1) command
    ({image with source := {image.source with source := ⟨result.1, image.source.source.position + 1⟩}}, result.2)
  let key := receipt.decision.key
  exact match receipt.decision.result with
  | .committed =>
      match CompleteSettlement.openSlot rules.atoms rules.maxExtents (control image lineage) lineage key with
      | none => refuses image
      | some record =>
          if receipt.decision = record.anchor.decision then
            let receiptAware := {base with settledReceipt := fun _ ticket => rules.targetSettlement record ticket}
            apply (CompleteSettlement.useAttestations receiptAware record rules.settlement rules.authenticSettlement)
          else refuses image
  | .canceled =>
      match image.plans key.slot with
      | none => refuses image
      | some plan =>
          if plan.move = key then
            apply {base with settledReceipt := fun claimed token => rules.canceledSettlement plan claimed token}
          else refuses image

noncomputable def decide (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) : Command slots Payload Ticket → Image slots Payload × Reply Payload := by
  classical
  exact fun command => match command with
  | .reserve plan evidence =>
      let required := participants plan
      match RealizedSource.reserve rules.source lineage image.source plan required
          (fun exactPlan => rules.plan exactPlan required evidence) with
      | some pending => ({image with source := pending.image, plans := setCell image.plans plan.move.slot (some plan)}, .accepted)
      | none => refuses image
  | .seal writer key vector body evidence =>
      match image.plans key.slot with
      | none => refuses image
      | some plan =>
          if plan.move = key then
            match RealizedSource.chooseSeal rules.source ⟨image.source, lineage, plan⟩ writer vector
                (rules.preparation evidence) with
            | some sealed =>
                if wireRecord rules body.realization = some sealed.record ∧
                    openWorkers rules body.eligibility = some image.workers ∧
                    rules.sealedReads lineage sealed.record.anchor.position body.readControl then
                  ({image with source := sealed.image, seals := setCell image.seals key.slot (some body)}, .accepted)
                else refuses image
            | none => refuses image
          else refuses image
  | .activate install =>
      let key := install.original.installation.anchor.decision.key
      match openSeal rules lineage image key with
      | none => refuses image
      | some (stored, evidence, workers) =>
          match RealizedSource.activate rules.source rules.alias ⟨image.source, stored⟩ install (rules.installed evidence) with
          | none => refuses image
          | some active =>
              let window : Window := ⟨lineage, active.image.source.position, active.physical⟩
              let updated := {image with
                source := active.image
                windows := setCell image.windows active.alias (some window)
                workers := workers}
              (updated, .accepted)
  | .replaceWriter expected successor evidence =>
      if CurrentNomination rules lineage image expected successor evidence then
        runSource rules lineage image (.source (.stream (.fence expected successor)))
      else refuses image
  | .changeWorkers change evidence =>
      if workerAdmissionOpen image.source.source.core.stream.authority = true ∧
          WorkerRosterCodec.FitsCommand width change ∧ rules.changeWorkers lineage change evidence then
        match image.workers.change rules.maxWorkers rules.lastEnrollment change with
        | some workers => applyWorkerChange rules lineage image change workers
        | none => refuses image
      else refuses image
  | .retireVacant expected evidence =>
      if image.source.source.core.stream.authority = .vacant expected ∧ rules.closeVacant lineage expected evidence then
        runSource rules lineage image (.source (.retire expected))
      else refuses image
  | .publishCheckpoint writer cut evidence =>
      if rules.checkpoint lineage writer cut evidence then
        runSource rules lineage image (.source (.stream (.checkpoint writer cut)))
      else refuses image
  | .install grant extent =>
      if rules.ordinaryWindow grant extent ∧ grant.version = rules.alias lineage (image.source.source.position + 1) then
        let result := runSource rules lineage image (.install grant)
        match result.2 with
        | .accepted =>
            let window : Window := ⟨lineage, result.1.source.source.position, extent⟩
            ({result.1 with windows := setCell image.windows grant.version (some window)}, .accepted)
        | _ => result
      else refuses image
  | .append request extent =>
      match image.windows request.version with
      | some window =>
          if window.lineage = lineage ∧ extent = window.physical ∧ rules.append request extent then
            runSource rules lineage image (.append request)
          else refuses image
      | none => refuses image
  | .stream (.fence _ _) | .stream (.withdraw _) | .stream (.checkpoint _ _) => refuses image
  | .stream command => runSource rules lineage image (.source (.stream command))
  | .cancel writer key => runSource rules lineage image (.source (.cancel writer key))
  | .retire writer =>
      if image.source.source.core.stream.authority = .active writer then
        runSource rules lineage image (.source (.retire writer))
      else refuses image
  | .acknowledge receipt evidence => runSettlement rules lineage image receipt evidence
  | .compact key =>
      if usesHandoff image key then refuses image else
        let result := runSource rules lineage image (.source (.compact key))
        match result.2 with
        | .accepted =>
            ({result.1 with plans := setCell image.plans key.slot none, seals := setCell image.seals key.slot none}, .accepted)
        | _ => result
  | .prune alias =>
      let result := runSource rules lineage image (.prune alias)
      match result.2 with
      | .accepted => ({result.1 with windows := setCell image.windows alias none}, .accepted)
      | _ => result

noncomputable def step (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (frame : Frame slots Payload Ticket) : Option (Image slots Payload) := by
  classical
  exact if eligible lineage image frame then some (decide rules lineage image frame.command).1 else none

noncomputable def replay (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (frames : List (Frame slots Payload Ticket)) : Option (Image slots Payload) :=
  frames.foldlM (step rules lineage) image

theorem replay_after_any_exact_prefix
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (initial base : Image slots Payload)
    (prefixFrames suffix : List (Frame slots Payload Ticket))
    (same : replay rules lineage initial prefixFrames = some base) :
    replay rules lineage initial (prefixFrames ++ suffix) = replay rules lineage base suffix := by
  simp only [replay] at same ⊢
  rw [List.foldlM_append, same]
  rfl

theorem a_rival_lineage_or_position_is_ineligible
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (frame : Frame slots Payload Ticket) (wrong : ¬ eligible lineage image frame) :
    step rules lineage image frame = none := by
  simp [step, wrong]

theorem an_append_request_for_a_different_physical_extent_is_refused
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (request : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity) (window : Window)
    (openWindow : image.windows request.version = some window) (wrong : extent ≠ window.physical) :
    decide rules lineage image (.append request extent) = refuses image := by
  simp [decide, openWindow, wrong]

theorem compacting_a_move_does_not_change_any_window_binding
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (key : SourceOutcomes.Key slots) :
    (decide rules lineage image (.compact key)).1.windows = image.windows := by
  simp only [decide]
  split
  · rfl
  · split <;> rfl

theorem a_live_handoff_refuses_compaction_even_after_all_participants_acknowledge
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (key : SourceOutcomes.Key slots) (referenced : usesHandoff image key) :
    decide rules lineage image (.compact key) = refuses image := by
  simp only [decide]
  exact ite_eq_left referenced

theorem an_exact_seal_atomically_retains_its_canonical_body
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key slots) (vector : Vector) (body : SealEvidence) (evidence : Ticket)
    (plan : AllocationVector.Plan slots) (stored : image.plans key.slot = some plan) (scope : plan.move = key)
    (sealed : RealizedSource.Sealed slots Payload)
    (chosen : RealizedSource.chooseSeal rules.source ⟨image.source, lineage, plan⟩ writer vector
      (rules.preparation evidence) = some sealed)
    (encoded : wireRecord rules body.realization = some sealed.record)
    (eligible : openWorkers rules body.eligibility = some image.workers)
    (readControl : rules.sealedReads lineage sealed.record.anchor.position body.readControl) :
    let applied := decide rules lineage image (.seal writer key vector body evidence)
    applied.2 = .accepted ∧ applied.1.source = sealed.image ∧ applied.1.seals key.slot = some body := by
  simp [decide, stored, scope, chosen, encoded, eligible, readControl, setCell]

#print axioms replay_after_any_exact_prefix
#print axioms a_rival_lineage_or_position_is_ineligible
#print axioms an_append_request_for_a_different_physical_extent_is_refused
#print axioms compacting_a_move_does_not_change_any_window_binding
#print axioms a_live_handoff_refuses_compaction_even_after_all_participants_acknowledge
#print axioms an_exact_seal_atomically_retains_its_canonical_body

end JointSource
