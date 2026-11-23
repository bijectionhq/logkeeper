import FullAdmission

set_option warningAsError true

namespace CoreReference

open ChosenReplay (Image Rules Frame Lineage)

variable {slots : Nat} {Payload Ticket : Type}

def stream (image : Image slots Payload) : Kernel.State Payload :=
  image.source.core.stream

def limits (rules : Rules slots Payload Ticket) (lineage : Lineage) : Kernel.Limits :=
  rules.append.regional.limits lineage.stream

theorem funded_chosen_commands_refine_the_stream
    (rules : Rules slots Payload Ticket) (lineage : Lineage)
    (image : Image slots Payload) (frame : Frame slots Payload Ticket) :
    let next := stream (ChosenReplay.decide rules lineage image frame).1
    stream image = next ∨ Kernel.Step (limits rules lineage) (stream image) next := by
  cases command : frame.command with
  | append request =>
      simp only [ChosenReplay.decide, command, stream]
      cases stored : image.book.windows request.version with
      | none =>
          rw [FundedAppend.no_window_means_no_append_payment_or_receipt stored]
          exact .inl rfl
      | some window =>
          by_cases allowed : FundedAppend.LocalChecks (ChosenReplay.frameRules rules frame) lineage.stream
              image.source image.book window request
          · rw [FundedAppend.eligible_append_uses_the_original_ordered_reducer stored allowed]
            simpa [FundedAppend.appendCommand, UnifiedSource.replay, limits, ChosenReplay.frameRules] using
              UnifiedSource.a_joint_command_projects_to_the_stream
                (limits rules lineage) (rules.append.regional.source lineage.stream)
                image.source.core (image.source.position + 1)
                (FundedAppend.appendCommand (slots := slots) request)
          · simp [FundedAppend.decide, stored, allowed]
  | install grant =>
      simp only [ChosenReplay.decide, command]
      split <;> exact .inl rfl
  | activate activation =>
      simp only [ChosenReplay.decide, command]
      split
      · simpa [stream, limits, ChosenReplay.installWindow, ChosenReplay.advancePosition,
          ChosenReplay.applyActivation] using
          UnifiedSource.a_joint_command_projects_to_the_stream
            (limits rules lineage) (rules.append.regional.source lineage.stream)
            image.source.core (image.source.position + 1) (.activate activation.installation)
      · exact .inl rfl
  | prune version =>
      simp only [ChosenReplay.decide, command]
      split <;> exact .inl rfl
  | source sourceCommand =>
      cases sourceCommand <;>
        simp only [ChosenReplay.decide, command] <;>
        first
        | exact .inl rfl
        | (split
           · exact UnifiedSource.a_joint_command_projects_to_the_stream _ _ _ _ _
           · exact .inl rfl)

private theorem joinTraces {limits : Kernel.Limits} {first middle last : Kernel.State Payload}
    (start : Kernel.Trace limits first middle) (finish : Kernel.Trace limits middle last) :
    Kernel.Trace limits first last := by
  induction finish with
  | same => exact start
  | next _ next previous => exact .next previous next

theorem every_replayed_history_refines_one_logical_trace
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (initial final : Image slots Payload)
    (frames : List (Frame slots Payload Ticket)) (replies : List (ChosenReplay.Applied slots Payload Ticket))
    (success : ChosenReplay.replay rules lineage initial frames = some (final, replies)) :
    Kernel.Trace (limits rules lineage) (stream initial) (stream final) := by
  induction frames generalizing initial final replies with
  | nil =>
      simp [ChosenReplay.replay] at success
      exact success.1.symm ▸ .same _
  | cons frame tail prior =>
      simp only [ChosenReplay.replay] at success
      split at success
      · let next := (ChosenReplay.decide rules lineage initial frame).1
        cases rest : ChosenReplay.replay rules lineage next tail with
        | none =>
            change (ChosenReplay.replay rules lineage next tail).map _ = some _ at success
            simp [rest] at success
        | some result =>
            change (ChosenReplay.replay rules lineage next tail).map _ = some _ at success
            simp [rest] at success
            have tailTrace : Kernel.Trace (limits rules lineage) (stream next) (stream result.1) :=
              prior next result.1 result.2 (by cases result; exact rest)
            have first := funded_chosen_commands_refine_the_stream rules lineage initial frame
            have start : Kernel.Trace (limits rules lineage) (stream initial) (stream next) := by
              rcases first with same | step
              · exact same ▸ .same _
              · exact .next (.same _) step
            exact success.1 ▸ joinTraces start tailTrace
      · cases success

theorem the_funded_reference_preserves_logical_bounds_and_committed_prefix
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (initial final : Image slots Payload)
    (frames : List (Frame slots Payload Ticket)) (replies : List (ChosenReplay.Applied slots Payload Ticket))
    (valid : Kernel.Valid (limits rules lineage) (stream initial))
    (success : ChosenReplay.replay rules lineage initial frames = some (final, replies)) :
    Kernel.Valid (limits rules lineage) (stream final) ∧ (stream initial).history <+: (stream final).history := by
  have trace := every_replayed_history_refines_one_logical_trace rules lineage initial final frames replies success
  obtain ⟨suffix, appended⟩ := Kernel.trace_extends_history trace
  exact ⟨Kernel.every_trace_preserves_bounds valid trace, suffix, appended.symm⟩

theorem the_funded_reference_preserves_terminal_retirement
    (rules : Rules slots Payload Ticket) (lineage : Lineage) (initial final : Image slots Payload)
    (frames : List (Frame slots Payload Ticket)) (replies : List (ChosenReplay.Applied slots Payload Ticket))
    (closed : (stream initial).authority = .retired)
    (success : ChosenReplay.replay rules lineage initial frames = some (final, replies)) :
    (stream final).authority = .retired :=
  Kernel.retired_absorbs_trace closed
    (every_replayed_history_refines_one_logical_trace rules lineage initial final frames replies success)

#print axioms funded_chosen_commands_refine_the_stream
#print axioms every_replayed_history_refines_one_logical_trace
#print axioms the_funded_reference_preserves_logical_bounds_and_committed_prefix
#print axioms the_funded_reference_preserves_terminal_retirement

end CoreReference
