import Logkeeper.LeaderJournal.ReplicaGate

namespace Logkeeper.LeaderJournal.Retirement

set_option warningAsError true

structure Scope where
  stream : Nat
  incarnation : KeeperId
  deriving DecidableEq, Repr

inductive Phase where
  | staged
  | installed
  deriving DecidableEq, Repr

structure Copy where
  generation : Nat
  revision : Nat
  phase : Phase
  deriving DecidableEq, Repr

structure Ticket where
  scope : Scope
  revision : Nat
  generation : Nat
  deriving DecidableEq, Repr

structure Local where
  scope : Scope
  revision : Nat
  nextGeneration : Nat
  current : Option Copy
  detached : List Nat
  hard : Installation.HardState
  trusted : Bool
  deriving DecidableEq

/-- A verifier must bind the core to the same stream incarnation before
    supplying this evidence. Joint containment includes both rosters. -/
def Authorized (core : State Application) (stream : Nat) (ticket : Ticket) : Prop :=
  ticket.scope.stream = stream ∧ ticket.revision = configurationVersion core.committed ∧
    core.configuration.contains ticket.scope.incarnation = false

theorem active_incarnation_cannot_retire {core : State Application} {stream : Nat} {ticket : Ticket}
    (active : core.configuration.contains ticket.scope.incarnation = true) :
    ¬ Authorized core stream ticket := by
  simp [Authorized, active]

def Local.stage (localState : Local) (revision : Nat) : Local :=
  { localState with
    revision
    nextGeneration := localState.nextGeneration + 1
    current := some ⟨localState.nextGeneration, revision, .staged⟩
    detached := match localState.current with
      | none => localState.detached
      | some copy => copy.generation :: localState.detached }

def Local.install (localState : Local) (copy : Copy) : Local :=
  { localState with current := some { copy with phase := .installed } }

def Local.detach (localState : Local) (ticket : Ticket) : Local :=
  { localState with
    revision := ticket.revision
    current := none
    detached := ticket.generation :: localState.detached }

def Local.unlink (localState : Local) (generation : Nat) : Local :=
  { localState with detached := localState.detached.erase generation }

def CanStage (localState : Local) (revision : Nat) : Prop :=
  localState.trusted = true ∧ localState.revision ≤ revision

def Matches (localState : Local) (ticket : Ticket) (copy : Copy) : Prop :=
  localState.scope = ticket.scope ∧ localState.revision ≤ ticket.revision ∧
    copy.revision ≤ ticket.revision ∧ copy.generation = ticket.generation

instance (localState : Local) (ticket : Ticket) (copy : Copy) :
    Decidable (Matches localState ticket copy) := by
  unfold Matches
  infer_instance

/-- This function accepts only checked evidence; unknown authorization is
    represented by none at the adapter. A successful return is a durable
    detach and queues physical removal. -/
def request (localState : Local) (evidence : Option Ticket) : Local × Option Nat :=
  match evidence, localState.current with
  | some ticket, some copy =>
      if Matches localState ticket copy then (localState.detach ticket, some ticket.generation)
      else (localState, none)
  | _, _ => (localState, none)

inductive Step : Local → Local → Prop
  | stage {s} (revision : Nat) (eligible : CanStage s revision) :
    Step s (s.stage revision)
  | install {s} (copy : Copy) (checked : s.trusted = true)
      (same : s.current = some copy) (staged : copy.phase = .staged) :
    Step s (s.install copy)
  | detach {s} (ticket : Ticket) (copy : Copy) (same : s.current = some copy)
      (matched : Matches s ticket copy) :
    Step s (s.detach ticket)
  | unlink {s} (generation : Nat) (queued : generation ∈ s.detached) :
    Step s (s.unlink generation)
  | crash {s} : Step s s
  | loseTrust {s} : Step s { s with trusted := false }

inductive Trace : Local → Local → Prop
  | refl (s : Local) : Trace s s
  | next {a b c} : Trace a b → Step b c → Trace a c

def Valid (s : Local) : Prop :=
  (∀ generation ∈ s.detached, generation < s.nextGeneration) ∧
    ∀ copy, s.current = some copy →
      copy.generation < s.nextGeneration ∧ copy.generation ∉ s.detached

theorem step_preserves_ownership {s t : Local} (valid : Valid s) (step : Step s t) :
    Valid t := by
  cases step with
  | stage revision eligible =>
    rcases present : s.current with _ | prior
    · constructor
      · intro g member
        exact Nat.lt_succ_of_lt (valid.1 g (by simpa [Local.stage, present] using member))
      · intro copy equal
        have same : ⟨s.nextGeneration, revision, Phase.staged⟩ = copy :=
          Option.some.inj equal
        subst copy
        exact ⟨Nat.lt_succ_self _, fun held => by
          have small := valid.1 _ (by simpa [Local.stage, present] using held)
          omega⟩
    · constructor
      · intro g member
        have queued : g = prior.generation ∨ g ∈ s.detached := by simpa [Local.stage, present] using member
        rcases queued with rfl | held
        · exact Nat.lt_succ_of_lt (valid.2 _ present).1
        · exact Nat.lt_succ_of_lt (valid.1 _ held)
      · intro copy equal
        have same : ⟨s.nextGeneration, revision, Phase.staged⟩ = copy :=
          Option.some.inj equal
        subst copy
        refine ⟨Nat.lt_succ_self _, fun held => ?_⟩
        have queued : s.nextGeneration = prior.generation ∨ s.nextGeneration ∈ s.detached :=
          by simpa [Local.stage, present] using held
        rcases queued with same | queued
        · have := (valid.2 _ present).1
          omega
        · have := valid.1 _ queued
          omega
  | install copy trusted present staged =>
    refine ⟨valid.1, fun next equal => ?_⟩
    have same : { copy with phase := .installed } = next := Option.some.inj equal
    subst next
    exact valid.2 copy present
  | detach ticket copy present matched =>
    refine ⟨?_, by simp [Local.detach]⟩
    intro g member
    rcases List.mem_cons.mp member with rfl | old
    · exact matched.2.2.2 ▸ (valid.2 _ present).1
    · exact valid.1 _ old
  | unlink generation queued =>
    have remains : ∀ g ∈ (s.unlink generation).detached, g ∈ s.detached :=
      fun _ member => List.mem_of_mem_erase member
    exact ⟨fun g member => valid.1 _ (remains g member),
      fun copy present => ⟨(valid.2 _ present).1, (valid.2 _ present).2 ∘ remains _⟩⟩
  | crash | loseTrust => exact valid

theorem trace_preserves_ownership {s t : Local} (valid : Valid s) (trace : Trace s t) :
    Valid t := by
  induction trace with
  | refl => exact valid
  | next _ step prior => exact step_preserves_ownership prior step

theorem generations_never_reused {s t : Local} (trace : Trace s t) :
    s.nextGeneration ≤ t.nextGeneration := by
  induction trace with
  | refl => exact Nat.le_refl _
  | next _ step prior =>
    cases step with
    | stage => exact Nat.le_trans prior (Nat.le_succ _)
    | _ => exact prior

theorem stage_after_detach_uses_fresh_handle {s : Local} {ticket : Ticket} {copy : Copy}
    (valid : Valid s) (present : s.current = some copy) (matched : Matches s ticket copy) :
    ticket.generation < ((s.detach ticket).stage revision).nextGeneration - 1 := by
  have smaller := (valid.2 copy present).1
  change ticket.generation < s.nextGeneration + 1 - 1
  rw [← matched.2.2.2]
  omega

theorem unknown_retirement_retains_copy (s : Local) : request s none = (s, none) := by
  cases s.current <;> simp [request, *]

theorem retirement_after_new_stage_is_ineffective {s : Local} (ticket : Ticket)
    (later : ticket.revision < revision) :
    request (s.stage revision) (some ticket) = (s.stage revision, none) := by
  simp [request, Local.stage, Matches, Nat.not_le.mpr later]

theorem delayed_unlink_targets_only_detached {s : Local} (valid : Valid s) {generation : Nat}
    (queued : generation ∈ s.detached) :
    (s.unlink generation).current = s.current ∧
      ∀ copy, s.current = some copy → copy.generation ≠ generation := by
  refine ⟨rfl, fun copy present same => ?_⟩
  exact (valid.2 copy present).2 (same.symm ▸ queued)

theorem retirement_keeps_hard_state {s t : Local} (trace : Trace s t) :
    t.hard = s.hard ∧ (s.trusted = false → t.trusted = false) := by
  induction trace with
  | refl => exact ⟨rfl, id⟩
  | next _ step prior =>
    cases step with
    | loseTrust => exact ⟨prior.1, fun _ => rfl⟩
    | _ => exact prior

theorem lost_media_requires_fresh_incarnation {s t : Local} (trace : Trace s t)
    (lost : s.trusted = false) : ¬ CanStage t revision := by
  intro allowed
  have bad := (retirement_keeps_hard_state trace).2 lost
  have healthy := allowed.1
  rw [bad] at healthy
  cases healthy

/-- A staged contact authorizes an ownership claim only with the checked move
    receipt for this stream and incarnation. The fence is the target revision. -/
theorem checked_staging_fences_old_retirement {registry : Placement.Registry} {directory : Bootstrap.Directory}
    {core : State Application} {s : Local} {route : Bootstrap.StagedRoute}
    (reachable : Bootstrap.CatalogReachable registry directory)
    (receipt : directory.cachedStage s.scope.stream = some route)
    (current : route.version = configurationVersion core.committed)
    (target : s.scope.incarnation ∈ route.newMembers)
    (allowed : CanStage s (route.version + 1)) :
    directory.staged s.scope.stream = some route ∧ s.scope.incarnation ∈ route.newMembers ∧
      Step s (s.stage (route.version + 1)) ∧
      ∀ ticket, Authorized core s.scope.stream ticket →
        request (s.stage (route.version + 1)) (some ticket) = (s.stage (route.version + 1), none) := by
  refine ⟨Bootstrap.cached_staging_was_published reachable receipt, target, .stage _ allowed, ?_⟩
  intro ticket authority
  exact retirement_after_new_stage_is_ineffective ticket (by rw [current, authority.2.1]; omega)

/-- Checked detachment refines a local disconnect. Consensus membership,
    logical data and trim are represented by the unchanged committed log. -/
theorem checked_detach_refines [DecidableEq Application] {core : State Application}
    {s : Local} {ticket : Ticket} {copy : Copy} (same : s.current = some copy)
    (matched : Matches s ticket copy) (_authority : Authorized core s.scope.stream ticket) :
    request s (some ticket) = (s.detach ticket, some ticket.generation) ∧
      Step s (s.detach ticket) ∧
      LeaderJournal.Step core (Installation.disconnect core s.scope.incarnation) ∧
      (Installation.disconnect core s.scope.incarnation).committed = core.committed := by
  refine ⟨by simp [request, same, matched], .detach ticket copy same matched, .fail _, rfl⟩

private def at12 : Local :=
  ⟨⟨4, 9⟩, 12, 8, some ⟨7, 12, .installed⟩, [], ⟨6, some 2⟩, true⟩

private def retire12 : Ticket := ⟨at12.scope, 12, 7⟩

theorem revision_12_13_races :
    request at12 (some retire12) = (at12.detach retire12, some 7) ∧
    request (at12.stage 13) (some retire12) = (at12.stage 13, none) ∧
    request ((at12.detach retire12).stage 13) (some retire12) =
      ((at12.detach retire12).stage 13, none) ∧
    (((at12.detach retire12).stage 13).unlink 7).current = some ⟨8, 13, .staged⟩ := by
  decide

theorem detach_crash_stage_then_cleanup :
    let detached := at12.detach retire12
    let staged := detached.stage 13
    let cleaned := staged.unlink 7
    Trace at12 cleaned ∧ cleaned.current = some ⟨8, 13, .staged⟩ ∧ cleaned.hard = at12.hard := by
  dsimp only
  have detach : Step at12 (at12.detach retire12) :=
    .detach retire12 ⟨7, 12, .installed⟩ rfl (by decide)
  have stage : Step (at12.detach retire12) ((at12.detach retire12).stage 13) := .stage 13 (by unfold CanStage; decide)
  have unlink : Step ((at12.detach retire12).stage 13)
      (((at12.detach retire12).stage 13).unlink 7) := .unlink 7 (by decide)
  exact ⟨.next (.next (.next (.next (.refl _) detach) .crash) stage) unlink, rfl, rfl⟩

#print axioms trace_preserves_ownership
#print axioms generations_never_reused
#print axioms stage_after_detach_uses_fresh_handle
#print axioms checked_detach_refines
#print axioms retirement_after_new_stage_is_ineffective
#print axioms delayed_unlink_targets_only_detached
#print axioms retirement_keeps_hard_state
#print axioms revision_12_13_races
#print axioms detach_crash_stage_then_cleanup

end Logkeeper.LeaderJournal.Retirement
