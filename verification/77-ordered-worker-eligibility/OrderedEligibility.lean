import StableGrant
import RankedJointReplay

set_option warningAsError true

namespace OrderedEligibility

open JointSource (Image Rules WorkerChange Workers)
open ChosenReplay (Lineage)

variable {slots width : Nat} {Payload Ticket Voter : Type}

theorem accepted_edits_preserve_both_bounds
    (workers next : Workers) (capacity lastSerial : Nat) (change : WorkerChange)
    (bounded : workers.members.length ≤ capacity) (representable : workers.issuedThrough ≤ lastSerial)
    (chosen : workers.change capacity lastSerial change = some next) :
    workers.issuedThrough ≤ next.issuedThrough ∧ next.issuedThrough ≤ lastSerial ∧
      next.members.length ≤ capacity := by
  cases change with
  | enroll holder issued =>
      simp only [Workers.change] at chosen
      split at chosen
      · next allowed =>
          cases chosen
          exact ⟨Nat.le_succ _, Nat.succ_le_of_lt allowed.2.1, Nat.succ_le_of_lt allowed.2.2.2⟩
      · contradiction
  | withdraw holder binding =>
      simp only [Workers.change] at chosen
      split at chosen
      · cases chosen
        exact ⟨Nat.le_refl _, representable, Nat.le_trans (List.length_filter_le _ _) bounded⟩
      · contradiction

theorem withdrawal_removes_the_row_and_reenrollment_issues_a_new_binding
    (workers removed reenrolled : Workers) (capacity lastSerial holder old : Nat)
    (withdrawn : workers.change capacity lastSerial (.withdraw holder old) = some removed)
    (restored : removed.change capacity lastSerial (.enroll holder removed.issuedThrough) = some reenrolled) :
    removed.enrollment holder = none ∧ removed.issuedThrough = workers.issuedThrough ∧
      reenrolled.enrollment holder = some (workers.issuedThrough + 1) := by
  simp only [Workers.change] at withdrawn
  split at withdrawn
  · cases withdrawn
    simp only [Workers.change] at restored
    split at restored
    · cases restored
      refine ⟨?_, rfl, ?_⟩
      · simp [Workers.enrollment]
      · simp [Workers.enrollment]
    · contradiction
  · contradiction

theorem another_workers_edit_preserves_the_exact_binding
    (workers next : Workers) (capacity lastSerial edited holder binding : Nat) (change : WorkerChange)
    (scope : change = .enroll edited binding ∨ change = .withdraw edited binding) (different : edited ≠ holder)
    (chosen : workers.change capacity lastSerial change = some next) :
    next.enrollment holder = workers.enrollment holder := by
  rcases scope with rfl | rfl
  · simp only [Workers.change] at chosen
    split at chosen
    · cases chosen
      simp [Workers.enrollment, different]
    · contradiction
  · simp only [Workers.change] at chosen
    split at chosen
    · cases chosen
      have same : (fun member : Nat × Nat => (member.1 != edited) && (member.1 == holder)) =
          (fun member => member.1 == holder) := by
        funext member
        by_cases exactHolder : member.1 = holder
        · simp [exactHolder, Ne.symm different]
        · simp [exactHolder]
      simp only [Workers.enrollment, List.find?_filter]
      change (workers.members.find? (fun member => (member.1 != edited) && (member.1 == holder))).map
        Prod.snd = (workers.members.find? (fun member => member.1 == holder)).map Prod.snd
      rw [same]
    · contradiction

theorem stale_edits_are_refused_at_the_installed_source
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (holder priorIssue priorEnrollment : Nat) (ticket : Ticket)
    (staleIssue : priorIssue ≠ image.workers.issuedThrough)
    (staleEnrollment : image.workers.enrollment holder ≠ some priorEnrollment) :
    JointSource.decide rules lineage image (.changeWorkers (.enroll holder priorIssue) ticket) = JointSource.refuses image ∧
      JointSource.decide rules lineage image (.changeWorkers (.withdraw holder priorEnrollment) ticket) = JointSource.refuses image := by
  constructor <;> simp [JointSource.decide, Workers.change, staleIssue, staleEnrollment]

theorem enrollment_exhaustion_still_allows_exact_withdrawal
    (workers : Workers) (capacity lastSerial holder binding : Nat)
    (exhausted : workers.issuedThrough = lastSerial) (current : workers.enrollment holder = some binding) :
    workers.change capacity lastSerial (.enroll holder lastSerial) = none ∧
      workers.change capacity lastSerial (.withdraw holder binding) =
        some {workers with members := workers.members.filter (fun member => member.1 != holder)} := by
  simp [Workers.change, exhausted, current]

theorem withdrawing_the_current_holder_atomically_fences_it_and_preserves_funding
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (writer : Kernel.Writer) (binding : Nat) (ticket : Ticket) (next : Workers)
    (live : image.source.source.core.stream.authority = .active writer)
    (auth : rules.changeWorkers lineage (.withdraw writer.holder binding) ticket)
    (changed : image.workers.change rules.maxWorkers rules.lastEnrollment (.withdraw writer.holder binding) = some next) :
    let result := JointSource.decide rules lineage image
      (.changeWorkers (.withdraw writer.holder binding) ticket)
    result.2 = .stream (.installed image.source.source.core.stream.history.length) ∧
    result.1.source.source.core.stream.authority = .vacant writer ∧ result.1.workers = next ∧
    result.1.source.source.core.stream.history = image.source.source.core.stream.history ∧
    result.1.source.book = image.source.book ∧ result.1.source.source.core.book = image.source.source.core.book ∧
    result.1.windows = image.windows := by
  let previous := image.source.source.core.stream
  let fenced := {previous with authority := .vacant writer}
  have applied : OrderedApplication.decideCommand (rules.source.append.regional.limits lineage.stream)
      previous (.withdraw writer) = (fenced, .installed previous.history.length) := by
    simp [OrderedApplication.decideCommand, previous, fenced, live]
  have routine : UnifiedSource.Routine (.withdraw writer : OrderedApplication.Command Payload) := trivial
  have inner : UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) image.source.source.core (image.source.source.position + 1)
      (.stream (.withdraw writer)) = ({image.source.source.core with stream := fenced}, .stream (.installed previous.history.length)) := by
    simp only [previous] at applied
    simp only [UnifiedSource.decide, ite_eq_left routine, applied]
    rfl
  have exactHistory : (UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) image.source.source.core (image.source.source.position + 1)
      (.stream (.withdraw writer))).1.stream.history = image.source.source.core.stream.history := by rw [inner]
  have allowed : JointSource.workerAdmissionOpen image.source.source.core.stream.authority = true ∧
      WorkerRosterCodec.FitsCommand width (.withdraw writer.holder binding) ∧
      rules.changeWorkers lineage (.withdraw writer.holder binding) ticket := by
    simp [live, JointSource.workerAdmissionOpen, WorkerRosterCodec.FitsCommand, auth]
  simp only [JointSource.decide, ite_eq_left allowed, changed, JointSource.applyWorkerChange, live, ite_true,
    JointSource.runSource, ChosenReplay.decide, ite_eq_left exactHistory, inner]
  simp [previous, fenced]

theorem a_stored_nomination_cannot_be_used_without_its_exact_current_enrollment
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (expected candidate : Kernel.Writer) (ticket : Ticket) (oldEnrollment : Nat)
    (binds : ∀ enrollment, rules.nomination lineage expected candidate enrollment ticket → enrollment = oldEnrollment)
    (stale : image.workers.enrollment candidate.holder ≠ some oldEnrollment) :
    JointSource.decide rules lineage image (.replaceWriter expected candidate ticket) = JointSource.refuses image := by
  apply StableGrant.an_unverified_nomination_cannot_replace_the_installed_writer
  rintro ⟨binding, stored, authentic⟩
  exact stale (by simpa only [binds binding authentic] using stored)

theorem an_exact_current_nomination_can_fill_a_vacancy_without_a_new_window
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (previous successor : Kernel.Writer) (ticket : Ticket)
    (authorized : JointSource.CurrentNomination rules lineage image previous successor ticket)
    (vacant : image.source.source.core.stream.authority = .vacant previous)
    (location : successor.placement = previous.placement) (higher : previous.epoch < successor.epoch) :
    let outcome := JointSource.decide rules lineage image (.replaceWriter previous successor ticket)
    outcome.2 = .stream (.installed image.source.source.core.stream.history.length) ∧
      outcome.1.source.source.core.stream.authority = .active successor ∧ outcome.1.windows = image.windows := by
  change (JointSource.decide rules lineage image (.replaceWriter previous successor ticket)).2 = _ ∧ _ ∧ _
  rw [StableGrant.a_nominated_same_placement_writer_inherits_the_exact_cut_and_window rules lineage image
    previous successor ticket authorized (Or.inr vacant) location higher]
  exact ⟨rfl, rfl, rfl⟩

theorem a_vacancy_excludes_every_writer_append_and_barrier
    (limits : Kernel.Limits) (state : Kernel.State Payload)
    (previous writer : Kernel.Writer) (lsn : Nat) (vacant : state.authority = .vacant previous) :
    ¬ OrderedApplication.AppendAllowed limits state writer lsn ∧ Kernel.barrier state writer = none := by
  simp [OrderedApplication.AppendAllowed, Kernel.barrier, vacant]

theorem an_authenticated_vacant_retirement_needs_no_replacement
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (image : Image slots Payload)
    (previous : Kernel.Writer) (ticket : Ticket)
    (vacant : image.source.source.core.stream.authority = .vacant previous)
    (noPending : image.source.source.core.pending = none) (auth : rules.closeVacant lineage previous ticket) :
    let result := JointSource.decide rules lineage image (.retireVacant previous ticket)
    result.2 = .accepted ∧ result.1.source.source.core.stream.authority = .retired ∧
      result.1.source.source.core.stream.history = image.source.source.core.stream.history := by
  simp [JointSource.decide, vacant, auth, JointSource.runSource, ChosenReplay.decide, UnifiedSource.decide, noPending]

theorem generic_withdrawal_and_roster_edits_at_a_sealed_source_are_refused
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (before : Image slots Payload)
    (target : Kernel.Placement) (previous : Kernel.Writer)
    (sealed : before.source.source.core.stream.authority = .sealed target previous)
    (change : WorkerChange) (ticket : Ticket) :
    JointSource.decide rules lineage before (.stream (.withdraw previous)) = JointSource.refuses before ∧
      JointSource.decide rules lineage before (.changeWorkers change ticket) = JointSource.refuses before := by
  simp [JointSource.decide, sealed, JointSource.workerAdmissionOpen]

theorem exact_recovery_from_either_base_preserves_the_same_eligibility_and_authority
    {ledger : PrefixAgreement.Ledger Voter (JointSource.Frame slots Payload Ticket)}
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (origin : Image slots Payload)
    (cut : RankedJointReplay.Cut ledger)
    (before after : RankedJointReplay.Base rules lineage origin cut.frames)
    (oldPhysical newPhysical : List (JointSource.Frame slots Payload Ticket))
    (left right : Image slots Payload)
    (old : RankedJointReplay.reopen rules lineage origin cut before oldPhysical = some left)
    (new : RankedJointReplay.reopen rules lineage origin cut after newPhysical = some right) :
    left.workers = right.workers ∧ left.source.source.core.stream.authority = right.source.source.core.stream.authority := by
  have same := RankedJointReplay.two_certified_bases_recover_the_same_complete_state rules lineage origin
    cut before after oldPhysical newPhysical left right old new
  subst right
  exact ⟨rfl, rfl⟩

#print axioms accepted_edits_preserve_both_bounds
#print axioms withdrawal_removes_the_row_and_reenrollment_issues_a_new_binding
#print axioms another_workers_edit_preserves_the_exact_binding
#print axioms stale_edits_are_refused_at_the_installed_source
#print axioms enrollment_exhaustion_still_allows_exact_withdrawal
#print axioms withdrawing_the_current_holder_atomically_fences_it_and_preserves_funding
#print axioms a_stored_nomination_cannot_be_used_without_its_exact_current_enrollment
#print axioms an_exact_current_nomination_can_fill_a_vacancy_without_a_new_window
#print axioms a_vacancy_excludes_every_writer_append_and_barrier
#print axioms an_authenticated_vacant_retirement_needs_no_replacement
#print axioms generic_withdrawal_and_roster_edits_at_a_sealed_source_are_refused
#print axioms exact_recovery_from_either_base_preserves_the_same_eligibility_and_authority

end OrderedEligibility
