import DecisionKernel

set_option warningAsError true

namespace Logkeeper.DecisionKernel

/-- Preserve all ordered observations, including refusals, held receipts, and
opaque reference evidence. The reduction is of operations. -/
def abstract (s : Reducer.State) : State :=
  ⟨s.placement, s.position, s.time, s.commandHistory, s.voterScope, s.successor,
    s.history, s.authority, s.budget, s.window, s.floor, s.head, s.checkpoints,
    s.roster, s.lastSerial, s.holds, s.leases, s.objects, s.book⟩

def image : Reducer.Command → Action
  | .enroll worker expected => .reconfigure (.enroll worker expected)
  | .withdraw owner => .reconfigure (.withdraw owner)
  | .grant epoch expected owner => .reconfigure (.transfer epoch expected owner)
  | .publishAndRotate grant checkpoint => .reconfigure (.rotate grant checkpoint)
  | .append grant expected lane payload bytes references =>
    .append grant expected lane payload bytes references
  | .barrier => .lease (.acquire .read)
  | .prepareCheckpoint pending references => .checkpoint (.prepare pending references)
  | .withdrawObject name version => .fence name version
  | .closeCheckpoint checkpoint => .checkpoint (.close checkpoint)
  | .settleCheckpoint checkpoint disposition floor => .collect (.root checkpoint disposition floor)
  | .disposeWorker owner disposition => .dispose owner (.certified disposition)
  | .publish checkpoint => .checkpoint (.select checkpoint)
  | .fundWindow window => .fund window
  | .protect grant through => .lease (.acquire (.writer grant through))
  | .protectRange start through => .lease (.acquire (.range start through))
  | .protectCheckpoint root start through => .lease (.acquire (.checkpoint root start through))
  | .protectRoot source => .lease (.acquire (.recoveryRoot source))
  | .vacate grant => .reconfigure (.vacate grant)
  | .sealCohort expected successor => .reconfigure (.seal expected successor)
  | .release hold id => .lease (.release (.exact hold id))
  | .releaseRead id => .lease (.release (.read id))
  | .lease grant => .lease (.renew (.writer grant))
  | .leaseRead hold id => .lease (.renew (.read hold id))
  | .disposeExpired owner => .dispose owner .expired
  | .trim selected through => .collect (.prefix selected through)

def requestImage (r : Reducer.Request) : Request :=
  ⟨r.placement, r.principal, r.id, image r.command, r.fingerprint⟩

@[simp] theorem read_image (r : Reducer.Request) :
    (requestImage r).action.isRead = r.command.isBarrier := by
  cases command : r.command <;> simp [requestImage, command, image, Action.isRead, Reducer.Command.isBarrier]

private theorem acquire_refines {s t : Reducer.State} {r : Reducer.Request}
    {basis : Basis} {hold : Reducer.Hold}
    (mapped : (requestImage r).action = .lease (.acquire basis))
    (framed : Reducer.frame { holds := true } s t)
    (principal : r.principal = .worker hold.owner)
    (basisValid : admitsHold (abstract s) basis hold)
    (inserted : Reducer.insertsHold s r hold t.holds) :
    effect limits (abstract s) (requestImage r) (basis.outcome hold) (abstract t) := by
  simp only [effect, mapped]
  exact ⟨hold, rfl, framed, principal, basisValid, inserted⟩

/-- Exhaustive over the 25 source constructors and all success outcomes.
The five hold selectors share the same acquisition rule. -/
theorem effect_refines {s t : Reducer.State} {r : Reducer.Request} {out : Reducer.AppliedOutcome}
    (applied : Reducer.effect limits s r out t) :
    effect limits (abstract s) (requestImage r) out (abstract t) := by
  cases command : r.command with
  | barrier =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case barrier hold =>
      obtain ⟨f, p, roster, kind, root, start, through, range, inserted⟩ := applied
      exact acquire_refines (basis := .read) (by simp [requestImage, command, image]) f p
        ⟨roster, kind, root, start, through, range⟩ inserted
  | protect grant through =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case protectedHold hold =>
      obtain ⟨f, active, writer, owner, principal, kind, root, start, endCut, range, inserted⟩ := applied
      exact acquire_refines (basis := (.writer grant through)) (by simp [requestImage, command, image]) f principal
        ⟨kind, active, writer, owner, root, start, endCut, range⟩ inserted
  | protectRange start through =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case protectedHold hold =>
      obtain ⟨f, p, roster, kind, root, startCut, endCut, range, inserted⟩ := applied
      exact acquire_refines (basis := (.range start through)) (by simp [requestImage, command, image]) f p
        ⟨roster, kind, root, startCut, endCut, range⟩ inserted
  | protectCheckpoint root start through =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case protectedHold hold =>
      obtain ⟨f, p, roster, kind, name, base, startCut, endCut, opened, range, inserted⟩ := applied
      exact acquire_refines (basis := (.checkpoint root start through)) (by simp [requestImage, command, image]) f p
        ⟨roster, kind, name, base, startCut, endCut, opened, range⟩ inserted
  | protectRoot source =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case protectedHold hold =>
      obtain ⟨f, p, kind, recovery, opened, fresh, start, through, inserted⟩ := applied
      exact acquire_refines (basis := (.recoveryRoot source)) (by simp [requestImage, command, image]) f p
        ⟨kind, recovery, opened, fresh, start, through⟩ inserted
  | disposeWorker owner disposition =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case workerDisposed result =>
      obtain ⟨f, p, same, evidence, withdrawn, holds, leases⟩ := applied
      simp only [effect, requestImage, command, image]
      exact ⟨f, same, ⟨p, evidence, withdrawn⟩, holds, leases⟩
  | disposeExpired owner =>
    cases out <;> simp only [Reducer.effect, command] at applied
    case workerDisposed result =>
      obtain ⟨f, same, due, holds, leases⟩ := applied
      simp only [effect, requestImage, command, image]
      exact ⟨f, same, due, holds, leases⟩
  | _ =>
    -- Each remaining row has definitionally identical guards and writes.
    cases out <;> simp only [Reducer.effect, command] at applied <;>
      simp only [effect, requestImage, command, image] <;> exact applied

theorem applied_refines {s t : Reducer.State} {r : Reducer.Request} {out : Reducer.AppliedOutcome}
    (applied : Reducer.Applied limits s r out t) :
    Applied limits (abstract s) (requestImage r) out (abstract t) :=
  ⟨effect_refines applied.commandEffect, applied.history, applied.authority, applied.budget,
    applied.objects, applied.holds, applied.leases, applied.time, applied.position,
    applied.rotationIncumbent⟩

private theorem cached_image (s : Reducer.State) (r : Reducer.Request) (entry) :
    cachedReceipt (abstract s) (requestImage r) entry = Reducer.cachedReceipt s r entry := by
  simp only [cachedReceipt, Reducer.cachedReceipt, read_image]
  rfl

private theorem record_image (s : Reducer.State) (r : Reducer.Request) (out) (book) :
    recordReceipt s.placement s.position (requestImage r) out book =
      Reducer.recordReceipt s.placement s.position r out book := by
  simp only [recordReceipt, Reducer.recordReceipt, read_image]
  rfl

theorem request_refines {s t : Reducer.State} {r : Reducer.Request} {receipt : Reducer.Receipt}
    (step : Reducer.RequestStep limits r s receipt t) :
    RequestStep limits (requestImage r) (abstract s) receipt (abstract t) := by
  cases step with
  | early refusal rejected => exact .early refusal rejected
  | cached entry placed found =>
    rw [← cached_image s r entry]
    exact .cached entry placed found
  | late refusal placed unused rejected => exact .late refusal placed unused rejected
  | refused refusal admitted =>
    have target := RequestStep.refused (r := requestImage r) (s := abstract s) refusal admitted
    simp only [abstract, record_image] at target ⊢
    exact target
  | applied admitted effects =>
    have target := RequestStep.applied (s := abstract s) (r := requestImage r) admitted (applied_refines effects)
    simp only [abstract, record_image] at target ⊢
    exact target

/-- A bad outer coordinate stutters, and every chosen decision has its
receipt and abstract post-state in a single kernel step. -/
theorem step_refines {s t : Reducer.State} {r : Reducer.Request}
    (step : Reducer.Step limits position time r s out t) :
    (∃ error, out = .error error ∧ abstract s = abstract t) ∨
    (∃ receipt, out = .ok receipt ∧
      Step limits position time (requestImage r) (abstract s) (.ok receipt) (abstract t)) := by
  cases step with
  | rejected error _ => exact Or.inl ⟨error, rfl, rfl⟩
  | chosen valid request =>
    exact Or.inr ⟨_, rfl, .chosen valid (request_refines request)⟩

theorem inv_image {s : Reducer.State} (inv : Reducer.ReducerInv limits s) :
    Inv limits (abstract s) :=
  ⟨inv.image, inv.kernel, inv.budget, inv.generation, inv.references, inv.holds, inv.leases⟩

theorem trace_refines {s t : Reducer.State} (trace : Reducer.Trace limits s t) :
    Trace limits (abstract s) (abstract t) := by
  induction trace with
  | same => exact .same _
  | next _ step earlier =>
    rcases step_refines step with ⟨_, _, same⟩ | ⟨_, _, next⟩
    · exact same ▸ earlier
    · exact .next earlier next

end Logkeeper.DecisionKernel
