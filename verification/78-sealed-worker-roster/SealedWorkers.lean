import OrderedEligibility

set_option warningAsError true

namespace SealedWorkers

open ChosenReplay (Lineage)
open JointSource (Rules Image SealEvidence Workers)
open RealizedSource (Install Record)
open WorkerRosterCodec (WellFormed)

variable {width slots : Nat} {Payload Ticket Voter : Type}

theorem configured_worker_edits_preserve_the_wire_invariant
    (rules : Rules width slots Payload Ticket) (before next : Workers) (edit : JointSource.WorkerChange)
    (valid : WellFormed width rules.maxWorkers rules.lastEnrollment before)
    (holderFits : WorkerRosterCodec.FitsCommand width edit)
    (applied : before.change rules.maxWorkers rules.lastEnrollment edit = some next) :
    WellFormed width rules.maxWorkers rules.lastEnrollment next :=
  WorkerRosterCodec.accepted_edits_keep_the_roster_encodable valid rules.enrollmentFits holderFits applied

theorem the_roster_wire_has_an_exact_inverse_and_fits_its_reserved_bytes
    (rules : Rules width slots Payload Ticket) (workers : Workers) (positive : 0 < width)
    (valid : WellFormed width rules.maxWorkers rules.lastEnrollment workers) :
    let wire := WorkerRosterCodec.encode width workers
    JointSource.openWorkers rules wire = some workers ∧
      (∀ other, JointSource.openWorkers rules other = some workers → other = wire) ∧
      wire.length ≤ WorkerRosterCodec.maxBytes width rules.maxWorkers := by
  refine ⟨WorkerRosterCodec.a_valid_roster_roundtrips positive valid, ?_,
    WorkerRosterCodec.roster_bytes_have_a_bounded_footprint valid⟩
  intro other opened
  exact (WorkerRosterCodec.an_opened_roster_names_its_exact_bytes opened).1.symm

theorem the_live_roster_and_retained_seals_fit_their_control_image_reservation
    (rules : Rules width slots Payload Ticket) (current : Workers) (sealed : List Workers)
    (slotsFit : sealed.length ≤ slots)
    (valid : ∀ roster ∈ current :: sealed, WellFormed width rules.maxWorkers rules.lastEnrollment roster) :
    ((current :: sealed).map (fun roster => (WorkerRosterCodec.encode width roster).length)).sum ≤
      (slots + 1) * WorkerRosterCodec.maxBytes width rules.maxWorkers := by
  let sectionBudget := WorkerRosterCodec.maxBytes width rules.maxWorkers
  have combined (rosters : List Workers)
      (each : ∀ roster ∈ rosters, WellFormed width rules.maxWorkers rules.lastEnrollment roster) :
      (rosters.map (fun roster => (WorkerRosterCodec.encode width roster).length)).sum ≤ rosters.length * sectionBudget := by
    induction rosters with
    | nil => simp
    | cons roster rest prior =>
        have first : (WorkerRosterCodec.encode width roster).length ≤ sectionBudget :=
          WorkerRosterCodec.roster_bytes_have_a_bounded_footprint (each roster (by simp))
        have tail := prior (fun other member => each other (List.mem_cons_of_mem _ member))
        simpa [Nat.add_mul, Nat.add_comm] using Nat.add_le_add first tail
  exact Nat.le_trans (combined (current :: sealed) valid) (Nat.mul_le_mul_right sectionBudget (Nat.succ_le_succ slotsFit))

theorem a_seal_with_the_exact_vector_but_the_wrong_workers_is_refused
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key slots) (vector : RealizedSource.Vector)
    (body : SealEvidence) (ticket : Ticket) (wrong : JointSource.openWorkers rules body.eligibility ≠ some image.workers) :
    JointSource.decide rules lineage image (.seal writer key vector body ticket) = JointSource.refuses image := by
  cases sourcePlan : image.plans key.slot with
  | none => simp [JointSource.decide, sourcePlan]
  | some plan =>
      by_cases scope : plan.move = key
      · cases chosen : RealizedSource.chooseSeal rules.source ⟨image.source, lineage, plan⟩ writer vector
            (rules.preparation ticket) <;>
          simp [JointSource.decide, sourcePlan, scope, chosen, wrong]
      · simp [JointSource.decide, sourcePlan, scope]

theorem the_opened_seal_uses_the_exact_slot_and_canonical_roster
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (key : SourceOutcomes.Key slots) (record : Record slots) (body : SealEvidence) (workers : Workers)
    (opened : JointSource.openSeal rules lineage image key = some (record, body, workers)) :
    CompleteSettlement.openSlot rules.atoms rules.maxExtents (JointSource.control image lineage) lineage key = some record ∧
      image.seals key.slot = some body ∧ WorkerRosterCodec.encode width workers = body.eligibility := by
  cases allocation : CompleteSettlement.openSlot rules.atoms rules.maxExtents (JointSource.control image lineage) lineage key with
  | none => simp [JointSource.openSeal, allocation] at opened
  | some found =>
      cases retained : image.seals key.slot with
      | none => simp [JointSource.openSeal, allocation, retained] at opened
      | some attachment =>
          cases roster : JointSource.openWorkers rules attachment.eligibility with
          | none => simp [JointSource.openSeal, allocation, retained, roster] at opened
          | some decoded =>
              simp [JointSource.openSeal, allocation, retained, roster] at opened
              obtain ⟨rfl, rfl, rfl⟩ := opened
              exact ⟨rfl, rfl, (WorkerRosterCodec.an_opened_roster_names_its_exact_bytes roster).1⟩

theorem a_target_mount_must_attest_to_the_same_sealed_body
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (install : Install slots Payload Ticket) (record : Record slots) (body : SealEvidence) (workers : Workers)
    (opened : JointSource.openSeal rules lineage image install.original.installation.anchor.decision.key =
      some (record, body, workers))
    (wrongMount : ¬ rules.installed body install) :
    JointSource.decide rules lineage image (.activate install) = JointSource.refuses image := by
  simp [JointSource.decide, opened, RealizedSource.activate, wrongMount]

theorem exact_target_activation_installs_the_sealed_roster_and_refuses_the_old_enrollment
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (install : Install slots Payload Ticket) (record : Record slots) (body : SealEvidence) (workers : Workers)
    (opened : JointSource.openSeal rules lineage image install.original.installation.anchor.decision.key =
      some (record, body, workers))
    (active : RealizedSource.Activated slots Payload)
    (installed : RealizedSource.activate rules.source rules.alias ⟨image.source, record⟩ install (rules.installed body) = some active)
    (current candidate : Kernel.Writer) (ticket : Ticket) (oldEnrollment : Nat)
    (authenticatesOnlyOld : ∀ enrollment,
      rules.nomination lineage current candidate enrollment ticket → enrollment = oldEnrollment)
    (withdrawn : workers.enrollment candidate.holder ≠ some oldEnrollment) :
    let applied := JointSource.decide rules lineage image (.activate install)
    applied.2 = .accepted ∧ applied.1.workers = workers ∧ applied.1.source = active.image ∧
      applied.1.windows active.alias = some ⟨lineage, active.image.source.position, active.physical⟩ ∧
      JointSource.decide rules lineage applied.1 (.replaceWriter current candidate ticket) =
        JointSource.refuses applied.1 := by
  let applied := (JointSource.decide rules lineage image (.activate install)).1
  have selected : applied.workers = workers := by
    simp [applied, JointSource.decide, opened, installed]
  have rejects := OrderedEligibility.a_stored_nomination_cannot_be_used_without_its_exact_current_enrollment
    rules lineage applied current candidate ticket oldEnrollment authenticatesOnlyOld (selected.symm ▸ withdrawn)
  refine ⟨?_, selected, ?_, ?_, rejects⟩ <;>
    simp [JointSource.decide, opened, installed, JointSource.setCell]

theorem a_canonical_checkpoint_opens_the_same_worker_image
    (rules : Rules width slots Payload Ticket) (image : Image slots Payload) (positive : 0 < width)
    (valid : WellFormed width rules.maxWorkers rules.lastEnrollment image.workers) :
    RankedJointReplay.imageOf rules (RankedJointReplay.controlOf width image) image.source.source = some image := by
  have parsed : JointSource.openWorkers rules (WorkerRosterCodec.encode width image.workers) = some image.workers :=
    WorkerRosterCodec.a_valid_roster_roundtrips positive valid
  simp only [RankedJointReplay.imageOf, RankedJointReplay.controlOf, parsed]
  cases image with
  | mk source => cases source; rfl

theorem either_certified_base_recovers_one_exact_roster_wire
    {ledger : PrefixAgreement.Ledger Voter (JointSource.Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (chosen : RankedJointReplay.Cut ledger) (old new : RankedJointReplay.Base rules lineage origin chosen.frames)
    (olderFrames newerFrames : List (JointSource.Frame slots Payload Ticket)) (left right : Image slots Payload)
    (oldRead : RankedJointReplay.reopen rules lineage origin chosen old olderFrames = some left)
    (newRead : RankedJointReplay.reopen rules lineage origin chosen new newerFrames = some right) :
    WorkerRosterCodec.encode width left.workers = WorkerRosterCodec.encode width right.workers := by
  have recovered := RankedJointReplay.two_certified_bases_recover_the_same_complete_state rules lineage origin
    chosen old new olderFrames newerFrames left right oldRead newRead
  rw [recovered]

#print axioms configured_worker_edits_preserve_the_wire_invariant
#print axioms the_roster_wire_has_an_exact_inverse_and_fits_its_reserved_bytes
#print axioms the_live_roster_and_retained_seals_fit_their_control_image_reservation
#print axioms a_seal_with_the_exact_vector_but_the_wrong_workers_is_refused
#print axioms the_opened_seal_uses_the_exact_slot_and_canonical_roster
#print axioms a_target_mount_must_attest_to_the_same_sealed_body
#print axioms exact_target_activation_installs_the_sealed_roster_and_refuses_the_old_enrollment
#print axioms a_canonical_checkpoint_opens_the_same_worker_image
#print axioms either_certified_base_recovers_one_exact_roster_wire

end SealedWorkers
