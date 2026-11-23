import ReceiptReplay
import CorePrograms

set_option warningAsError true

namespace MoveProgram

open CoreReference (stream)
open CorePrograms (lineage first entry initial committed frame direct)
open ChosenReplay (Rules Image Frame Applied)

def earlier : ReceiptReplay.View 1 Nat := ⟨initial, fun _ => none⟩
def original : ReceiptReplay.Key Nat := ⟨lineage, first, 0, 42⟩
def changed : ReceiptReplay.Key Nat := {original with payload := 43}
def receipt : ReceiptReplay.Receipt Nat := ⟨original, 2, 1⟩
def retainedRows : ReceiptReplay.Rows Nat := fun lsn => if lsn = 0 then some receipt else none

theorem the_common_append_program_populates_its_exact_receipt_row
    (rules : Rules 1 Nat Unit) (paid : CorePrograms.PaidFixture rules) :
    ReceiptReplay.replay rules lineage earlier CorePrograms.start =
      some (⟨committed, retainedRows⟩, CorePrograms.bootReplies) := by
  simp only [ReceiptReplay.replay, earlier,
    CorePrograms.a_funded_install_and_append_return_the_exact_record rules paid]
  apply congrArg some
  apply Prod.ext _ rfl
  apply congrArg (ReceiptReplay.View.mk committed)
  funext index
  simp [CorePrograms.bootReplies, CorePrograms.append, frame,
    ReceiptReplay.retain, ReceiptReplay.record, stream, committed, SnapshotAdmission.setSlot]

theorem skipping_lookup_authorization_exposes_the_exact_retained_receipt :
    let view : ReceiptReplay.View 1 Nat := ⟨committed, retainedRows⟩
    ReceiptReplay.lookup lineage False view original = .refused ∧
      ReceiptReplay.lookup lineage True view original = .committed receipt := by
  constructor
  · simp [ReceiptReplay.lookup]
  · apply ReceiptReplay.the_exact_retained_receipt_is_available_without_appending
    · exact ⟨trivial, rfl⟩
    · decide
    · decide
    · rfl
    · rfl

private def recordAtChoice (rows : ReceiptReplay.Rows Nat) (chosen : Frame 1 Nat Unit) :
    ReceiptReplay.Rows Nat :=
  match chosen.command with
  | .append request =>
    ReceiptReplay.record rows
      ⟨chosen, .stream (.appended request.lsn ⟨request.writer.epoch, request.payload⟩)⟩
  | _ => rows

theorem accepting_choice_instead_of_success_records_a_refused_append (rules : Rules 1 Nat Unit) :
    let before := CorePrograms.fenced
    let chosen := frame 5 (CorePrograms.append first 1 1 43)
    let result := ChosenReplay.decide rules lineage before chosen
    ReceiptReplay.record retainedRows ⟨chosen, result.2⟩ 1 = none ∧
      recordAtChoice retainedRows chosen 1 =
        some ⟨⟨lineage, first, 1, 43⟩, 5, 2⟩ ∧
      (stream result.1).history[1]? = none := by
  dsimp only
  rw [CorePrograms.a_delayed_writer_is_refused_in_the_funded_window rules]
  exact ⟨rfl, rfl, rfl⟩

def target : Kernel.Placement := ⟨2, 2⟩
def nextWriter : Kernel.Writer := {first with placement := target}
def slot : SourceOutcomes.Key 1 := ⟨0, 1⟩
def intent : FundedSeal.Intent Nat := ⟨1, target, fun pool => if pool = 1 ∨ pool = 2 then 1 else 0⟩
def anchor : UnifiedSource.Anchor 1 Nat := ⟨⟨slot, intent, .committed⟩, 4⟩

def sealed : Image 1 Nat :=
  let core := {committed.source.core with
    stream := {stream committed with authority := .sealed target first}
    book := ⟨1, fun _ => some ⟨1, intent, some .committed, [.target, .pool 1, .pool 2]⟩⟩
    handoff := some anchor}
  {committed with source := ⟨core, 4⟩}

def installation : UnifiedSource.Installation 1 Nat Nat Unit := ⟨anchor, first, [entry], ()⟩
def newGrant : ChosenReplay.Grant Unit := ⟨10, nextWriter, ()⟩
def activation : ChosenReplay.Activation 1 Nat Unit := ⟨installation, newGrant⟩
def activationFrame : Frame 1 Nat Unit := frame 5 (.activate activation)

structure VerifiedMove (rules : Rules 1 Nat Unit) : Prop where
  installed : (rules.append.regional.source 7).installed installation
  authority : rules.activation lineage activation
  grant : rules.grant lineage newGrant
  owner : rules.append.owner 10 = 7

def targetBasis : Image 1 Nat :=
  let core := {sealed.source.core with
    handoff := none
    stream := {stream sealed with authority := .active nextWriter}}
  {sealed with source := {sealed.source with core}}

def activated : Image 1 Nat := ChosenReplay.installWindow lineage targetBasis newGrant

theorem the_funded_activation_moves_writer_and_window_with_the_same_exact_history
    (rules : Rules 1 Nat Unit) (verified : VerifiedMove rules) :
    ChosenReplay.decide rules lineage sealed activationFrame = (activated, .accepted) := by
  have matched : UnifiedSource.SameInstallation installation anchor := ⟨rfl, rfl⟩
  have auth : (rules.append.regional.source lineage.stream).installed installation := verified.installed
  have prior := show sealed.source.core.handoff = some anchor from rfl
  have exactTarget : UnifiedSource.SameInstallation installation anchor ∧
      (rules.append.regional.source lineage.stream).installed installation ∧
      sealed.source.core.stream.authority = .sealed anchor.decision.binding.target installation.writer ∧
      installation.history = sealed.source.core.stream.history :=
    ⟨matched, auth, rfl, rfl⟩
  have outcome : UnifiedSource.decide (rules.append.regional.limits lineage.stream)
      (rules.append.regional.source lineage.stream) sealed.source.core (sealed.source.position + 1)
      (.activate installation) = (targetBasis.source.core, .accepted) := by
    simp only [UnifiedSource.decide, prior]
    split
    · rfl
    · rename_i denied
      exact False.elim (denied exactTarget)
  have installed : ChosenReplay.applyActivation rules lineage sealed activation = (targetBasis, .accepted) := by
    simp only [ChosenReplay.applyActivation, activation, outcome]
    rfl
  have fits : ChosenReplay.AcceptsActivation rules lineage sealed activation := by
    unfold ChosenReplay.AcceptsActivation
    rw [installed]
    exact ⟨rfl, verified.authority, verified.grant, verified.owner, by decide, rfl, rfl⟩
  simp only [ChosenReplay.decide, activationFrame, frame, ite_eq_left fits, installed]
  rfl

theorem a_successor_recovers_the_original_reply_and_its_cut_without_another_append
    (rules : Rules 1 Nat Unit) (verified : VerifiedMove rules) :
    ∃ restored responses, ReceiptReplay.replay rules lineage ⟨sealed, retainedRows⟩ [activationFrame] =
      some (restored, responses) ∧
      (stream restored.image).authority = .active nextWriter ∧
      (stream restored.image).history = [entry] ∧
      restored.image.book.latest lineage.stream = 10 ∧
      Kernel.barrier (stream restored.image) nextWriter = some 1 ∧
      ReceiptReplay.lookup lineage True restored original = .committed receipt ∧
      ReceiptReplay.lookup lineage True restored changed = .conflict := by
  have chosen := the_funded_activation_moves_writer_and_window_with_the_same_exact_history rules verified
  have eligible : ChosenReplay.eligibleFrame lineage sealed activationFrame := ⟨rfl, rfl⟩
  have applied : ChosenReplay.replay rules lineage sealed [activationFrame] =
      some (activated, [⟨activationFrame, .accepted⟩]) := by
    simp only [ChosenReplay.replay, ite_eq_left eligible, chosen, Option.map_some]
  let restored := ReceiptReplay.useApplied retainedRows ((activated, [⟨activationFrame, .accepted⟩]) :
    ChosenReplay.Outcomes 1 Nat Unit)
  refine ⟨restored, [⟨activationFrame, .accepted⟩], ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [ReceiptReplay.replay, applied, restored]
  · have active : (stream restored.image).authority = .active nextWriter := rfl
    simp only [Kernel.barrier, active]
    rfl
  · exact ReceiptReplay.the_exact_retained_receipt_is_available_without_appending ⟨trivial, rfl⟩
      (by decide) (by decide) rfl rfl
  · have distinct : receipt.binding ≠ changed := by
      intro equal
      have bytes := congrArg ReceiptReplay.Key.payload equal
      change 42 = 43 at bytes
      contradiction
    have current : (stream restored.image).firstRetained = 0 := rfl
    have stored : restored.rows changed.lsn = some receipt := rfl
    have permitted : True ∧ changed.lineage = lineage := ⟨trivial, rfl⟩
    have permittedRange : ¬ changed.lsn < (stream restored.image).firstRetained := by rw [current]; omega
    have committedRange : ¬ (stream restored.image).history.length ≤ changed.lsn := by decide
    simp [ReceiptReplay.lookup, permitted, permittedRange, committedRange, stored, ReceiptReplay.Matches, distinct]

#print axioms the_common_append_program_populates_its_exact_receipt_row
#print axioms skipping_lookup_authorization_exposes_the_exact_retained_receipt
#print axioms accepting_choice_instead_of_success_records_a_refused_append
#print axioms the_funded_activation_moves_writer_and_window_with_the_same_exact_history
#print axioms a_successor_recovers_the_original_reply_and_its_cut_without_another_append

end MoveProgram
