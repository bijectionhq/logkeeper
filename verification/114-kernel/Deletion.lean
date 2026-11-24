import Refinement

set_option warningAsError true

namespace Logkeeper.DecisionKernel

open Reducer (Command AppliedOutcome Writes)

def HolderEnrolled (s : Reducer.State) : Prop :=
  ∀ owner, s.authority.holder = some owner → s.roster owner.1 = some owner

private theorem framed_holder {s t : Reducer.State} {w : Writes}
    (inv : HolderEnrolled s) (frame : Reducer.frame w s t)
    (writer : w.writer = false) (roster : w.roster = false) : HolderEnrolled t := by
  rw [HolderEnrolled, (frame.1 writer).2, (frame.2.2.2.2.2.1 roster).1]
  exact inv

private theorem holder_of_effect {s t : Reducer.State} {r : Reducer.Request} {out : AppliedOutcome}
    (inv : HolderEnrolled s) (effect : Reducer.effect limits s r out t) : HolderEnrolled t := by
  cases command : r.command <;> cases out <;> simp only [Reducer.effect, command] at effect
  case enroll.enrolled worker expected newOwner =>
    obtain ⟨_, _, _, _, _, _, roster, writer, _⟩ := effect
    unfold Reducer.writerUpdate at writer
    split at writer
    · simp [HolderEnrolled, writer.2, Reducer.vacate, ErasureCommit.vacate]
    · intro owner present
      rw [writer.2] at present
      have old := inv owner present
      have different : owner.1 ≠ worker := by
        intro same
        simp_all
      simp [roster, Reducer.replace, different, old]
  case withdraw.withdrawn removed =>
    obtain ⟨_, _, old, _, roster, writer, _⟩ := effect
    unfold Reducer.writerUpdate at writer
    split at writer
    · simp [HolderEnrolled, writer.2, Reducer.vacate, ErasureCommit.vacate]
    · intro owner present
      rw [writer.2] at present
      have current := inv owner present
      have different : owner.1 ≠ removed.1 := by
        intro same
        rw [same, old] at current
        obtain rfl := Option.some.inj current
        simp_all
      simp [roster, Reducer.replace, different, current]
  case grant.granted epoch expected owner writer recovery =>
    obtain ⟨framed, _, enrolled, _, _, _, _, _, _, _, _, _, update⟩ := effect
    intro holder present
    rw [update.2.2.2] at present
    obtain rfl := Option.some.inj present
    rw [(framed.2.2.2.2.2.1 rfl).1]
    exact enrolled
  case publishAndRotate.granted grant checkpoint writer recovery =>
    obtain ⟨framed, _, _, _, _, _, _, _, _, _, _, _, _, update, _, _⟩ := effect
    intro holder present
    rw [update.2.2.2] at present
    rw [(framed.2.2.2.2.2.1 rfl).1]
    exact inv holder present
  case append.appended grant expected lane payload bytes refs cut =>
    obtain ⟨framed, _, _, _, ⟨_, _, _, authority, _⟩, _⟩ := effect
    rw [HolderEnrolled, authority, (framed.2.2.2.2.2.1 rfl).1]
    exact inv
  case vacate.vacated grant =>
    obtain ⟨_, _, _, authority⟩ := effect
    simp [HolderEnrolled, authority, Reducer.vacate, ErasureCommit.vacate]
  case trim.trimmed selected through cut credit =>
    obtain ⟨framed, _, _, _, _, _, _, _, _, _, authority, _⟩ := effect
    rw [HolderEnrolled, authority, (framed.2.2.2.2.2.1 rfl).1]
    exact inv
  all_goals exact framed_holder inv effect.1 rfl rfl

theorem enrolled_holder_is_preserved
    (inv : HolderEnrolled s) (step : Reducer.Step limits position time r s out t) :
    HolderEnrolled t := by
  cases step with
  | rejected => exact inv
  | chosen _ request =>
    cases request with
    | @applied target _ _ applied =>
      exact holder_of_effect (s := Reducer.advance limits s position time r) (t := target)
        inv applied.commandEffect
    | _ => exact inv

def asRange (s : Reducer.State) (r : Reducer.Request) (through : Reducer.Cut) : Reducer.Request :=
  { r with command := .protectRange s.checkpoints.selected.cut.nextLsn through.nextLsn }

private theorem protect_effect_as_range
    (holder : HolderEnrolled s) (command : r.command = .protect grant through)
    (effect : Reducer.effect limits s r out t) :
    Reducer.effect limits s (asRange s r through) out t := by
  cases out <;> simp only [Reducer.effect, command] at effect
  case protectedHold hold =>
    obtain ⟨framed, _, _, owner, principal, kind, root, start, ends, exactRange, inserted⟩ := effect
    exact ⟨framed, principal, holder hold.owner owner, kind, root,
      congrArg Reducer.Cut.nextLsn start, congrArg Reducer.Cut.nextLsn ends, exactRange, inserted⟩

private theorem protect_request_as_range
    (holder : HolderEnrolled s) (command : r.command = .protect grant through)
    (step : Reducer.RequestStep limits r s receipt t) :
    Reducer.RequestStep limits (asRange s r through) s receipt t := by
  have cached (entry) :
      Reducer.cachedReceipt s (asRange s r through) entry = Reducer.cachedReceipt s r entry := by
    simp [Reducer.cachedReceipt, asRange, command, Command.isBarrier, Reducer.currentReceipt, Reducer.Request.key]
  have recorded (out book) :
      Reducer.recordReceipt s.placement s.position (asRange s r through) out book =
        Reducer.recordReceipt s.placement s.position r out book := by
    simp [Reducer.recordReceipt, asRange, command, Command.isBarrier, Reducer.currentReceipt, Reducer.Request.key] <;> rfl
  cases step with
  | early refusal rejected => exact .early refusal rejected
  | cached entry placed found =>
    rw [← cached entry]
    exact .cached entry placed found
  | late refusal placed unused rejected => exact .late refusal placed unused rejected
  | refused refusal admitted =>
    have replacement := Reducer.RequestStep.refused (r := asRange s r through) (s := s)
      refusal admitted
    rw [recorded] at replacement
    exact replacement
  | applied admitted applied =>
    have replacement : Reducer.Applied limits s (asRange s r through) _ _ :=
      ⟨protect_effect_as_range holder command applied.commandEffect, applied.history,
        applied.authority, applied.budget, applied.objects, applied.holds, applied.leases,
        applied.time, applied.position, applied.rotationIncumbent⟩
    have normalized := Reducer.RequestStep.applied (s := s) (r := asRange s r through)
      admitted replacement
    rw [recorded] at normalized
    exact normalized

def withoutProtect : Command → Prop
  | .protect .. => False
  | _ => True

/-- One range request replaces a writer-prefix request with the same
coordinates, fingerprint, receipt and whole final image. -/
theorem protect_step_is_range
    (inv : HolderEnrolled s) (command : r.command = .protect grant through)
    (step : Reducer.Step limits position time r s out t) :
    Reducer.Step limits position time (asRange s r through) s out t := by
  cases step with
  | rejected error invalid => exact .rejected error invalid
  | chosen valid request =>
    exact .chosen valid (protect_request_as_range (s := Reducer.advance limits s position time r)
      inv command request)

inductive TraceWithoutProtect (limits : Reducer.Limits) : Reducer.State → Reducer.State → Prop
  | same (s) : TraceWithoutProtect limits s s
  | next (prior : TraceWithoutProtect limits s m) (allowed : withoutProtect r.command)
      (step : Reducer.Step limits position time r m out t) : TraceWithoutProtect limits s t

theorem deletion_preserves_reachable_states (inv : HolderEnrolled s) :
    Reducer.Trace limits s t ↔ TraceWithoutProtect limits s t := by
  constructor
  · intro trace
    have proof : HolderEnrolled t ∧ TraceWithoutProtect limits s t := by
      induction trace with
      | same => exact ⟨inv, .same _⟩
      | @next _ _ _ _ r _ _ step prior =>
        refine ⟨enrolled_holder_is_preserved prior.1 step, ?_⟩
        cases command : r.command
        case protect grant through =>
          exact .next prior.2 (by trivial) (protect_step_is_range prior.1 command step)
        all_goals exact .next prior.2 (by simp [withoutProtect, command]) step
    exact proof.2
  · intro trace
    induction trace with
    | same => exact .same _
    | next _ _ step prior => exact .next prior step

end Logkeeper.DecisionKernel
