import JointSource

set_option warningAsError true

namespace StableGrant

open JointSource (Rules Image Command Frame)
open ChosenReplay (Lineage)

variable {slots width : Nat} {Payload Ticket : Type}

def installed (image : Image slots Payload) (successor : Kernel.Writer) : Image slots Payload :=
  let previous := image.source.source.core.stream
  let next := {image.source.source.core with stream := {previous with authority := .active successor}}
  {image with source := {image.source with source := ⟨next, image.source.source.position + 1⟩}
              receipts := ReceiptReplay.retain image.receipts previous.firstRetained}

theorem a_nominated_same_placement_writer_inherits_the_exact_cut_and_window
    (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (before : Image slots Payload) (expected successor : Kernel.Writer) (evidence : Ticket)
    (authorized : JointSource.CurrentNomination rules lineage before expected successor evidence)
    (current : Kernel.AtWriter before.source.source.core.stream.authority expected)
    (unchanged : successor.placement = expected.placement)
    (newer : expected.epoch < successor.epoch) :
    JointSource.decide rules lineage before (.replaceWriter expected successor evidence) =
      (installed before successor, .stream (.installed before.source.source.core.stream.history.length)) := by
  let old := before.source.source.core.stream
  let next := {old with authority := .active successor}
  have applied : OrderedApplication.decideCommand (rules.source.append.regional.limits lineage.stream) old
      (.fence expected successor) = (next, .installed old.history.length) := by
    simp [OrderedApplication.decideCommand, old, next, current, unchanged, newer]
  have routes : UnifiedSource.Routine (OrderedApplication.Command.fence expected successor : OrderedApplication.Command Payload) :=
    trivial
  have source : UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) before.source.source.core (before.source.source.position + 1)
      (.stream (.fence expected successor)) =
      ({before.source.source.core with stream := next}, .stream (.installed old.history.length)) := by
    simp only [old] at applied
    simp only [UnifiedSource.decide, ite_eq_left routes, applied]
    rfl
  have sameHistory : (UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) before.source.source.core (before.source.source.position + 1)
      (.stream (.fence expected successor))).1.stream.history = before.source.source.core.stream.history := by
    rw [source]
  simp only [JointSource.decide, ite_eq_left authorized, JointSource.runSource, ChosenReplay.decide,
    ite_eq_left sameHistory, source]
  rfl

theorem an_unverified_nomination_cannot_replace_the_installed_writer
    (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (before : Image slots Payload) (expected successor : Kernel.Writer) (evidence : Ticket)
    (denied : ¬ JointSource.CurrentNomination rules lineage before expected successor evidence) :
    JointSource.decide rules lineage before (.replaceWriter expected successor evidence) = JointSource.refuses before := by
  simp only [JointSource.decide]
  exact ite_eq_right denied

theorem generic_stream_commands_cannot_bypass_nomination
    (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (before : Image slots Payload) (expected successor : Kernel.Writer) :
    JointSource.decide rules lineage before (.stream (.fence expected successor)) = JointSource.refuses before := by
  rfl

theorem the_replacement_changes_no_part_of_the_paid_window_or_move_book
    (before : Image slots Payload) (successor : Kernel.Writer) :
    let after := installed before successor
    after.source.book = before.source.book ∧ after.windows = before.windows ∧
      after.source.source.core.stream.history = before.source.source.core.stream.history ∧
      after.plans = before.plans ∧ after.seals = before.seals ∧
      after.source.source.core.book = before.source.source.core.book ∧
      after.source.source.core.handoff = before.source.source.core.handoff :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem the_old_writer_cannot_append_with_the_still_paid_window
    (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (before : Image slots Payload) (successor : Kernel.Writer)
    (request : FundedAppend.Request Payload Ticket) (extent : PoolState.Identity)
    (window : CompleteSettlement.Window) (bound : before.windows request.version = some window)
    (valid : window.lineage = lineage ∧ extent = window.physical ∧ rules.append request extent)
    (stale : request.writer ≠ successor) :
    JointSource.decide rules lineage (installed before successor) (.append request extent) =
      JointSource.refuses (installed before successor) := by
  let current := installed before successor
  have known : current.windows request.version = some window := bound
  have command : JointSource.decide rules lineage current (.append request extent) =
      JointSource.runSource rules lineage current (.append request) := by
    simp only [JointSource.decide, known, ite_eq_left valid]
  change JointSource.decide rules lineage current (.append request extent) = _
  rw [command]
  let frame : ChosenReplay.Frame slots Payload Ticket :=
    ⟨lineage, current.source.source.position + 1, .append request⟩
  have rejects (live : FundedAppend.Window) :
      ¬ FundedAppend.LocalChecks (ChosenReplay.frameRules rules.source frame)
        lineage.stream current.source.source current.source.book live request := by
    intro attempted
    exact stale ((Kernel.Authority.active.inj attempted.streamAllowed.1).symm)
  have inner : ChosenReplay.decide rules.source lineage current.source frame =
      (ChosenReplay.advancePosition current.source, .refused) := by
    cases found : current.source.book.windows request.version with
    | none => simp [ChosenReplay.decide, frame, FundedAppend.decide, found, ChosenReplay.advancePosition]
    | some live =>
        have exactReject := rejects live
        simp only [frame] at exactReject
        simp [ChosenReplay.decide, frame, FundedAppend.decide, found, exactReject, ChosenReplay.advancePosition]
  simp only [JointSource.runSource, inner, frame, JointSource.refuses, ReceiptReplay.record]
  congr 1
  simp [current, installed, ChosenReplay.advancePosition]
  funext lsn
  by_cases trimmed : lsn < before.source.source.core.stream.firstRetained <;> simp [ReceiptReplay.retain, trimmed]

theorem a_stale_expected_holder_cannot_replace_its_successor
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (before : Image slots Payload)
    (expected first second : Kernel.Writer) (ticket : Ticket)
    (different : first ≠ expected)
    (authorized : JointSource.CurrentNomination rules lineage (installed before first) expected second ticket) :
    (JointSource.decide rules lineage (installed before first) (.replaceWriter expected second ticket)).1.source.source.core.stream.authority =
      .active first := by
  have mismatched : ¬ Kernel.AtWriter (installed before first).source.source.core.stream.authority expected := by
    intro same
    rcases same with active | vacant
    · exact different (Kernel.Authority.active.inj active)
    · cases vacant
  have stream : OrderedApplication.decideCommand (rules.source.append.regional.limits lineage.stream)
      (installed before first).source.source.core.stream (.fence expected second) =
      ((installed before first).source.source.core.stream, .refused) := by
    simp [OrderedApplication.decideCommand, mismatched]
  have routine : UnifiedSource.Routine (.fence expected second : OrderedApplication.Command Payload) := trivial
  let current := installed before first
  have refused : UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) current.source.source.core (current.source.source.position + 1)
      (.stream (.fence expected second)) = (current.source.source.core, .stream .refused) := by
    have exactStream : OrderedApplication.decideCommand (rules.source.append.regional.limits lineage.stream)
        current.source.source.core.stream (.fence expected second) = (current.source.source.core.stream, .refused) := stream
    simp only [UnifiedSource.decide, ite_eq_left routine, exactStream]
  have currentNomination : JointSource.CurrentNomination rules lineage current expected second ticket := authorized
  change (JointSource.decide rules lineage current (.replaceWriter expected second ticket)).1.source.source.core.stream.authority = _
  simp only [JointSource.decide, ite_eq_left currentNomination, JointSource.runSource, ChosenReplay.decide, refused]
  rfl

theorem the_new_holder_keeps_all_original_read_reservations
    (before : Image slots Payload) (successor : Kernel.Writer) :
    (installed before successor).source.source.core.stream.replays = before.source.source.core.stream.replays ∧
      (installed before successor).source.source.core.stream.firstRetained = before.source.source.core.stream.firstRetained ∧
      (installed before successor).source.source.core.stream.checkpointEnd = before.source.source.core.stream.checkpointEnd :=
  ⟨rfl, rfl, rfl⟩

theorem the_successor_spends_the_original_prepaid_window
    (rules : Rules width slots Payload Ticket) (lineage : Lineage) (before : Image slots Payload)
    (successor : Kernel.Writer) (request : FundedAppend.Request Payload Ticket)
    (extent : PoolState.Identity) (physical : CompleteSettlement.Window) (paid : FundedAppend.Window)
    (bound : before.windows request.version = some physical)
    (journal : before.source.book.windows request.version = some paid)
    (exactScope : physical.lineage = lineage ∧ extent = physical.physical ∧ rules.append request extent)
    (allowed : let current := installed before successor
      let frame : ChosenReplay.Frame slots Payload Ticket := ⟨lineage, current.source.source.position + 1, .append request⟩
      FundedAppend.LocalChecks (ChosenReplay.frameRules rules.source frame) lineage.stream
        current.source.source current.source.book paid request) :
    let result := JointSource.decide rules lineage (installed before successor) (.append request extent)
    result.2 = .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩) ∧
      result.1.windows = before.windows ∧
      result.1.source.book.windows request.version = some {paid with
        nextLsn := request.lsn + 1, spent := request.offset + rules.source.append.cost request.payload} := by
  let current := installed before successor
  let frame : ChosenReplay.Frame slots Payload Ticket := ⟨lineage, current.source.source.position + 1, .append request⟩
  have known : current.windows request.version = some physical := bound
  have exactPaid : current.source.book.windows request.version = some paid := journal
  have fits : FundedAppend.LocalChecks (ChosenReplay.frameRules rules.source frame) lineage.stream
      current.source.source current.source.book paid request := allowed
  have effect := FundedAppend.eligible_append_uses_the_original_ordered_reducer exactPaid fits
  simp only [frame] at effect
  have command : JointSource.decide rules lineage current (.append request extent) =
      JointSource.runSource rules lineage current (.append request) := by
    simp only [JointSource.decide, known, ite_eq_left exactScope]
  change let result := JointSource.decide rules lineage current (.append request extent); _
  rw [command]
  simp only [JointSource.runSource, ChosenReplay.decide, effect]
  simp [FundedAppend.advanceWindow, SnapshotAdmission.setSlot, ChosenReplay.frameRules, current, installed]

theorem an_unverified_checkpoint_cannot_use_the_source_publication_lane
    (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (writer : Kernel.Writer) (cut : Nat) (evidence : Ticket)
    (invalid : ¬ rules.checkpoint lineage writer cut evidence) :
    JointSource.decide rules lineage image (.publishCheckpoint writer cut evidence) = JointSource.refuses image ∧
      JointSource.decide rules lineage image (.stream (.checkpoint writer cut)) = JointSource.refuses image := by
  exact ⟨by simp only [JointSource.decide, ite_eq_right invalid], rfl⟩

theorem a_receipt_lookup_is_unchanged_by_the_worker_replacement
    (lineage : Lineage) (before : Image slots Payload) (successor : Kernel.Writer)
    (authorized : Prop) (request : ReceiptReplay.Key Payload) :
    ReceiptReplay.lookup lineage authorized ⟨(installed before successor).source, (installed before successor).receipts⟩ request =
      ReceiptReplay.lookup lineage authorized ⟨before.source, before.receipts⟩ request := by
  by_cases trimmed : request.lsn < before.source.source.core.stream.firstRetained <;>
    simp [ReceiptReplay.lookup, ReceiptReplay.retain, installed, CoreReference.stream, trimmed] <;> rfl

theorem the_installed_journal_can_publish_a_certified_checkpoint
    (rules : Rules width slots Payload Ticket) (lineage : Lineage)
    (before : Image slots Payload) (writer : Kernel.Writer) (cut : Nat) (evidence : Ticket)
    (certificate : rules.checkpoint lineage writer cut evidence)
    (current : before.source.source.core.stream.authority = .active writer)
    (advances : before.source.source.core.stream.checkpointEnd ≤ cut)
    (within : cut ≤ before.source.source.core.stream.history.length) :
    let result := JointSource.decide rules lineage before (.publishCheckpoint writer cut evidence)
    result.2 = .stream (.installed cut) ∧ result.1.source.source.core.stream.checkpointEnd = cut ∧
      result.1.source.source.core.stream.history = before.source.source.core.stream.history ∧
      result.1.windows = before.windows := by
  let previous := before.source.source.core.stream
  let replacement := {previous with checkpointEnd := cut}
  have effect : OrderedApplication.decideCommand (rules.source.append.regional.limits lineage.stream)
      before.source.source.core.stream (.checkpoint writer cut) = (replacement, .installed cut) := by
    simp [OrderedApplication.decideCommand, current, advances, within, replacement, previous]
  have routine : UnifiedSource.Routine (.checkpoint writer cut : OrderedApplication.Command Payload) := trivial
  have reduced : UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) before.source.source.core (before.source.source.position + 1)
      (.stream (.checkpoint writer cut)) =
      ({before.source.source.core with stream := replacement}, .stream (.installed cut)) := by
    simp only [UnifiedSource.decide, ite_eq_left routine, effect]
  have stable : (UnifiedSource.decide (rules.source.append.regional.limits lineage.stream)
      (rules.source.append.regional.source lineage.stream) before.source.source.core (before.source.source.position + 1)
      (.stream (.checkpoint writer cut))).1.stream.history = before.source.source.core.stream.history := by
    rw [reduced]
  simp only [JointSource.decide, ite_eq_left certificate, JointSource.runSource, ChosenReplay.decide,
    ite_eq_left stable, reduced]
  simp [replacement, previous]

#print axioms a_nominated_same_placement_writer_inherits_the_exact_cut_and_window
#print axioms an_unverified_nomination_cannot_replace_the_installed_writer
#print axioms generic_stream_commands_cannot_bypass_nomination
#print axioms the_replacement_changes_no_part_of_the_paid_window_or_move_book
#print axioms the_old_writer_cannot_append_with_the_still_paid_window
#print axioms a_stale_expected_holder_cannot_replace_its_successor
#print axioms the_new_holder_keeps_all_original_read_reservations
#print axioms the_successor_spends_the_original_prepaid_window
#print axioms an_unverified_checkpoint_cannot_use_the_source_publication_lane
#print axioms a_receipt_lookup_is_unchanged_by_the_worker_replacement
#print axioms the_installed_journal_can_publish_a_certified_checkpoint

end StableGrant
