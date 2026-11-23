import CorePrograms

set_option warningAsError true

namespace Weakening

open CoreReference (stream)
open CorePrograms (first successor committed fenced held)

inductive Removed where
  | writer
  | checkpoint
  | replayHold
  | recoveryRoom
  | retainedRoom

abbrev Stream := Kernel.State Nat

def append (state : Stream) (writer : Kernel.Writer) (payload : Nat) : Stream :=
  {state with history := state.history ++ [⟨writer.epoch, payload⟩]}

inductive Step (removed : Removed) (limits : Kernel.Limits) : Stream → Stream → Prop
  | original {state next} (step : Kernel.Step limits state next) : Step removed limits state next
  | withoutWriter {state} (omitted : removed = .writer) (writer : Kernel.Writer) (lsn payload : Nat)
      (head : lsn = state.history.length)
      (recover : state.history.length + 1 - state.checkpointEnd ≤ limits.recovery)
      (retain : state.history.length + 1 - state.firstRetained ≤ limits.retained) :
      Step removed limits state (append state writer payload)
  | withoutCheckpoint {state} (omitted : removed = .checkpoint) (writer : Kernel.Writer) (cut : Nat)
      (authorized : state.authority = .active writer) (advances : state.firstRetained ≤ cut)
      (protects : ∀ id lsn, state.replays id = .holding lsn → cut ≤ lsn) :
      Step removed limits state {state with firstRetained := cut}
  | withoutHold {state} (omitted : removed = .replayHold) (writer : Kernel.Writer) (cut : Nat)
      (authorized : state.authority = .active writer) (advances : state.firstRetained ≤ cut)
      (published : cut ≤ state.checkpointEnd) :
      Step removed limits state {state with firstRetained := cut}
  | withoutRecoveryRoom {state} (omitted : removed = .recoveryRoom) (writer : Kernel.Writer) (lsn payload : Nat)
      (authorized : state.authority = .active writer) (head : lsn = state.history.length)
      (retain : state.history.length + 1 - state.firstRetained ≤ limits.retained) :
      Step removed limits state (append state writer payload)
  | withoutRetainedRoom {state} (omitted : removed = .retainedRoom) (writer : Kernel.Writer) (lsn payload : Nat)
      (authorized : state.authority = .active writer) (head : lsn = state.history.length)
      (recover : state.history.length + 1 - state.checkpointEnd ≤ limits.recovery) :
      Step removed limits state (append state writer payload)

theorem removing_the_writer_check_admits_the_stale_append_at_the_valid_head :
    let before := stream fenced
    let budget : Kernel.Limits := ⟨2, 2⟩
    let after := append before first 43
    Step .writer budget before after ∧ before.authority = .active successor ∧
      ¬ Kernel.AppendAdmissible budget before first 1 ∧
      after.history[1]? = some ⟨first.epoch, 43⟩ := by
  refine ⟨.withoutWriter rfl first 1 43 rfl (by decide) (by decide), rfl, ?_, rfl⟩
  apply Kernel.stale_writer_refused
  change Kernel.Authority.active successor ≠ Kernel.Authority.active first
  decide

theorem removing_the_checkpoint_guard_admits_trim_without_a_certified_replacement :
    let before := stream committed
    let after := {before with firstRetained := 1}
    Step .checkpoint ⟨2, 2⟩ before after ∧
      (OrderedApplication.decideCommand ⟨2, 2⟩ before (.trim first 1)).2 = .refused ∧
      ¬ Kernel.Valid ⟨2, 2⟩ after := by
  have noHold : ∀ id lsn, (stream committed).replays id = .holding lsn → 1 ≤ lsn := by
    intro _ _ impossible
    cases impossible
  refine ⟨.withoutCheckpoint rfl first 1 rfl (by decide) noHold, ?_, ?_⟩
  · simp only [OrderedApplication.decideCommand]
    split
    · rename_i allowed
      exact False.elim (Nat.not_succ_le_zero 0 allowed.2.2.1)
    · rfl
  · intro valid
    exact Nat.not_succ_le_zero 0 valid.trimCertified

theorem removing_the_replay_guard_invalidates_a_live_hold :
    let before := stream held
    let after := {before with firstRetained := 1}
    Step .replayHold ⟨2, 2⟩ before after ∧
      (OrderedApplication.decideCommand ⟨2, 2⟩ before (.trim first 1)).2 = .refused ∧
      ¬ Kernel.Valid ⟨2, 2⟩ after := by
  refine ⟨.withoutHold rfl first 1 rfl (by decide) (by decide), ?_, ?_⟩
  · simp only [OrderedApplication.decideCommand]
    split
    · rename_i allowed
      exact False.elim (Nat.not_succ_le_zero 0 (allowed.2.2.2 1 0 rfl))
    · rfl
  · intro valid
    exact Nat.not_succ_le_zero 0 (valid.replaySafe 1 0 rfl)

theorem removing_recovery_room_exceeds_only_the_recovery_limit :
    let before := stream committed
    let after := append before first 43
    Step .recoveryRoom ⟨1, 2⟩ before after ∧
      ¬ Kernel.AppendAdmissible ⟨1, 2⟩ before first 1 ∧
      after.history.length - after.checkpointEnd > 1 ∧
      after.history.length - after.firstRetained ≤ 2 := by
  refine ⟨.withoutRecoveryRoom rfl first 1 43 rfl rfl (by decide), ?_, by decide, by decide⟩
  intro permitted
  exact (by decide : ¬ 2 ≤ 1) permitted.recoveryRoom

theorem removing_retained_room_exceeds_only_the_retained_limit :
    let before := stream committed
    let after := append before first 43
    Step .retainedRoom ⟨2, 1⟩ before after ∧
      ¬ Kernel.AppendAdmissible ⟨2, 1⟩ before first 1 ∧
      after.history.length - after.firstRetained > 1 ∧
      after.history.length - after.checkpointEnd ≤ 2 := by
  refine ⟨.withoutRetainedRoom rfl first 1 43 rfl rfl (by decide), ?_, by decide, by decide⟩
  intro permitted
  exact (by decide : ¬ 2 ≤ 1) permitted.retainedRoom

#print axioms removing_the_writer_check_admits_the_stale_append_at_the_valid_head
#print axioms removing_the_checkpoint_guard_admits_trim_without_a_certified_replacement
#print axioms removing_the_replay_guard_invalidates_a_live_hold
#print axioms removing_recovery_room_exceeds_only_the_recovery_limit
#print axioms removing_retained_room_exceeds_only_the_retained_limit

end Weakening
