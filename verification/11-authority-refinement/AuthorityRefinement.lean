import Kernel
import Reservation

set_option warningAsError true

namespace AuthorityRefinement

open Kernel

def replace (rows : Nat → Value) (key : Nat) (value : Value) : Nat → Value :=
  fun found => if found = key then value else rows found

def localAt (stream : State Payload) (group : Nat) : Option (State Payload) :=
  match stream.authority with
  | .active writer => if group = writer.placement.group then some stream else none
  | _ => none

structure Seal (Payload : Type) where
  source : Writer
  target : Placement
  nonce : Nat
  cut : State Payload

def frozen (certificate : Seal Payload) : State Payload :=
  {certificate.cut with authority := .sealed certificate.target certificate.source}

def carriedWriter (certificate : Seal Payload) : Writer :=
  {certificate.source with placement := certificate.target}

def installed (certificate : Seal Payload) : State Payload :=
  {certificate.cut with authority := .active (carriedWriter certificate)}

structure World (Payload : Type) where
  rows : Nat → Option (State Payload)
  slots : Nat → Reservation.Slot
  seals : List (Seal Payload)

def prepared (slot : Reservation.Slot) : Reservation.Slot :=
  ⟨slot.issuedThrough + 1, some (slot.issuedThrough + 1)⟩

def consumed (slot : Reservation.Slot) : Reservation.Slot :=
  {slot with live := none}

def prepareAt (world : World Payload) (target : Nat) : World Payload :=
  {world with slots := replace world.slots target (prepared (world.slots target))}

def sealAt (world : World Payload) (certificate : Seal Payload) : World Payload :=
  {world with rows := replace world.rows certificate.source.placement.group none,
              seals := certificate :: world.seals}

def installAt (world : World Payload) (certificate : Seal Payload) : World Payload :=
  {world with
    rows := replace world.rows certificate.target.group (some (installed certificate))
    slots := replace world.slots certificate.target.group (consumed (world.slots certificate.target.group))}

def applyAt (world : World Payload) (group : Nat) (stream : State Payload) : World Payload :=
  {world with rows := replace world.rows group (localAt stream group)}

inductive Step (limits : Limits) : World Payload → World Payload → Prop
  | prepare {world target} (empty : (world.slots target).live = none) :
      Step limits world (prepareAt world target)
  | ownerAction {world group before after nextWriter}
      (row : world.rows group = some before) (current : Kernel.Step limits before after)
      (stillServing : after.authority = .active nextWriter)
      (sameGroup : nextWriter.placement.group = group) :
      Step limits world (applyAt world group after)
  | retire {world before writer} (row : world.rows writer.placement.group = some before)
      (current : before.authority = .active writer) :
      Step limits world (applyAt world writer.placement.group {before with authority := .retired})
  | commitSeal {world current source} (target : Placement) (nonce : Nat)
      (row : world.rows source.placement.group = some current)
      (grant : current.authority = .active source)
      (advances : source.placement.generation < target.generation)
      (relocates : source.placement.group ≠ target.group)
      (live : (world.slots target.group).live = some nonce) :
      Step limits world (sealAt world ⟨source, target, nonce, current⟩)
  | install {world} (certificate : Seal Payload) (authentic : certificate ∈ world.seals)
      (live : (world.slots certificate.target.group).live = some certificate.nonce) :
      Step limits world (installAt world certificate)

def Phase (world : World Payload) (stream : State Payload) (pending : Option (Seal Payload)) : Prop :=
  match pending with
  | none => ∀ target prior, stream.authority ≠ .sealed target prior
  | some certificate => certificate ∈ world.seals ∧ stream = frozen certificate ∧
      (world.slots certificate.target.group).live = some certificate.nonce

def Issued (slots : Nat → Reservation.Slot) : Prop :=
  ∀ group nonce, (slots group).live = some nonce → nonce ≤ (slots group).issuedThrough

structure Refines (world : World Payload) (stream : State Payload)
    (pending : Option (Seal Payload)) : Prop where
  rows : world.rows = localAt stream
  phase : Phase world stream pending
  issued : Issued world.slots
  spent : ∀ certificate ∈ world.seals, some certificate ≠ pending →
    Reservation.Stale certificate.nonce (world.slots certificate.target.group)

def initialWorld (writer : Writer) : World Payload :=
  ⟨localAt (Kernel.initial writer), fun _ => ⟨0, none⟩, []⟩

theorem initial_refines (writer : Writer) :
    Refines (initialWorld writer : World Payload) (Kernel.initial writer) none := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [Phase, Kernel.initial]
  · intro group nonce live
    simp [initialWorld] at live
  · simp [initialWorld]

private theorem row_shape {world : World Payload} {stream before : State Payload}
    {pending : Option (Seal Payload)} {group : Nat}
    (known : Refines world stream pending) (row : world.rows group = some before) :
    before = stream ∧ ∃ current, stream.authority = .active current ∧ current.placement.group = group := by
  rw [known.rows] at row
  unfold localAt at row
  split at row
  next writer active =>
    split at row
    next groupMatch => exact ⟨(Option.some.inj row).symm, writer, active, groupMatch.symm⟩
    next => simp at row
  next => simp at row

private theorem active_has_no_pending {world : World Payload} {stream : State Payload}
    {pending : Option (Seal Payload)} {writer : Writer}
    (known : Refines world stream pending) (active : stream.authority = .active writer) :
    pending = none := by
  cases pending with
  | none => rfl
  | some certificate =>
      have shape := known.phase.2.1
      rw [shape] at active
      simp [frozen] at active

private theorem change_active_row {before after : State Payload} {source target : Writer}
    {group : Nat} (beforeActive : before.authority = .active source)
    (sourceGroup : source.placement.group = group) (afterActive : after.authority = .active target)
    (targetGroup : target.placement.group = group) :
    replace (localAt before) group (some after) = localAt after := by
  funext found
  by_cases matchesGroup : found = group
  · simp [replace, localAt, afterActive, targetGroup, matchesGroup]
  · simp [replace, localAt, beforeActive, afterActive, sourceGroup, targetGroup, matchesGroup]

private theorem clear_active_row {before after : State Payload} {writer : Writer}
    (beforeActive : before.authority = .active writer) (noActive : ∀ grant, after.authority ≠ .active grant) :
    replace (localAt before) writer.placement.group none = localAt after := by
  funext found
  have noRow : localAt after found = none := by
    unfold localAt
    split
    next writer active => exact False.elim (noActive writer active)
    next => rfl
  rw [noRow]
  by_cases matchesGroup : found = writer.placement.group
  · simp [replace, matchesGroup]
  · simp [replace, localAt, beforeActive, matchesGroup]

private theorem issued_after_slot_step {slots : Nat → Reservation.Slot} {changed : Nat}
    {next : Reservation.Slot} (valid : Issued slots) (step : Reservation.Step (slots changed) next) :
    Issued (replace slots changed next) := by
  intro group nonce present
  by_cases located : group = changed
  · subst group
    simp [replace] at present ⊢
    cases step with
    | prepare _ => exact Nat.le_of_eq (Option.some.inj present).symm
    | consume _ => simp at present
  · simpa [replace, located] using valid group nonce (by simpa [replace, located] using present)

private theorem spent_after_slot_step {slots : Nat → Reservation.Slot} {changed group nonce : Nat}
    {next : Reservation.Slot} (alreadySpent : Reservation.Stale nonce (slots group))
    (step : Reservation.Step (slots changed) next) :
    Reservation.Stale nonce (replace slots changed next group) := by
  by_cases located : group = changed
  · subst group
    simpa [replace] using Reservation.stale_preserved alreadySpent step
  · simpa [replace, located] using alreadySpent

theorem step_refines {limits : Limits} {before after : World Payload} {stream : State Payload}
    {pending : Option (Seal Payload)} (known : Refines before stream pending)
    (step : Step limits before after) :
    ∃ next nextPending, (next = stream ∨ Kernel.Step limits stream next) ∧
      Refines after next nextPending := by
  cases step with
  | @prepare target empty =>
      let newSlot := prepared (before.slots target)
      have updated : Reservation.Step (before.slots target) newSlot := .prepare empty
      refine ⟨stream, pending, Or.inl rfl, known.rows, ?_,
        issued_after_slot_step known.issued updated, ?_⟩
      · cases pending with
        | none => exact known.phase
        | some certificate =>
            obtain ⟨authentic, exactCut, live⟩ := known.phase
            have another : certificate.target.group ≠ target := by
              intro sameGroup
              rw [sameGroup, empty] at live
              simp at live
            exact ⟨authentic, exactCut, by simpa [prepareAt, replace, another] using live⟩
      · intro certificate authentic spent
        exact spent_after_slot_step (known.spent certificate authentic spent) updated
  | ownerAction row current nextActive sameGroup =>
      obtain ⟨rfl, source, sourceActive, sourceGroup⟩ := row_shape known row
      have noPending := active_has_no_pending known sourceActive
      subst pending
      refine ⟨_, none, Or.inr current, ?_, ?_, known.issued, known.spent⟩
      · rw [show (applyAt before _ _).rows = replace before.rows _ (localAt _ _) from rfl, known.rows]
        simpa [localAt, nextActive, sameGroup] using
          change_active_row sourceActive sourceGroup nextActive sameGroup
      · intro target prior bad
        rw [nextActive] at bad
        contradiction
  | retire row current =>
      obtain ⟨rfl, _, _, _⟩ := row_shape known row
      have noPending := active_has_no_pending known current
      subst pending
      refine ⟨_, none, Or.inr (.retire (Or.inl current)), ?_, ?_, known.issued, known.spent⟩
      · simp only [applyAt, known.rows]
        exact clear_active_row current (by intro grant; simp)
      · simp [Phase]
  | commitSeal target nonce row grant advances relocates live =>
      rename_i current source
      obtain ⟨rfl, _, _, _⟩ := row_shape known row
      have noPending := active_has_no_pending known grant
      subst pending
      let issued : Seal Payload := ⟨source, target, nonce, current⟩
      refine ⟨frozen issued, some issued, Or.inr (.freeze target grant advances relocates),
        ?_, ?_, known.issued, ?_⟩
      · simp only [sealAt, known.rows]
        exact clear_active_row (after := frozen issued) grant (by intro writer; simp [frozen])
      · refine ⟨by simp [sealAt, issued], rfl, live⟩
      · intro certificate authentic notCurrent
        rcases List.mem_cons.mp authentic with rfl | earlier
        · exact False.elim (notCurrent rfl)
        · exact known.spent certificate earlier (by simp)
  | install certificate authentic live =>
      have matchesPending : pending = some certificate := by
        classical
        by_cases same : pending = some certificate
        · exact same
        · exact False.elim ((known.spent certificate authentic (Ne.symm same)).2 live)
      subst pending
      have oldCut := known.phase.2.1
      have nextStep : Kernel.Step limits stream (installed certificate) := by
        rw [oldCut]
        exact .activate certificate.cut.history rfl rfl
      let newSlot := consumed (before.slots certificate.target.group)
      have updated : Reservation.Step (before.slots certificate.target.group) newSlot := .consume live
      refine ⟨installed certificate, none, Or.inr nextStep, ?_, ?_,
        issued_after_slot_step known.issued updated, ?_⟩
      · funext group
        simp [installAt, known.rows, oldCut, replace, localAt, frozen, installed, carriedWriter]
      · simp [Phase, installed]
      · intro earlier member _
        classical
        by_cases same : earlier = certificate
        · subst earlier
          exact ⟨by simpa [installAt, replace, consumed] using
                   known.issued certificate.target.group certificate.nonce live,
                 by simp [installAt, replace, consumed]⟩
        · exact spent_after_slot_step (known.spent earlier member (fun eq => same (Option.some.inj eq))) updated

inductive Trace (limits : Limits) : World Payload → World Payload → Prop
  | same (world : World Payload) : Trace limits world world
  | next {first before after} : Trace limits first before → Step limits before after →
      Trace limits first after

theorem traces_refine {limits : Limits} {before after : World Payload} {stream : State Payload}
    {pending : Option (Seal Payload)} (known : Refines before stream pending)
    (trace : Trace limits before after) :
    ∃ next nextPending, Kernel.Trace limits stream next ∧ Refines after next nextPending := by
  induction trace with
  | same => exact ⟨stream, pending, .same stream, known⟩
  | next _ step prior =>
      obtain ⟨mid, midPending, abstractTrace, relation⟩ := prior
      obtain ⟨next, nextPending, stutters | abstractStep, refined⟩ := step_refines relation step
      · subst next
        exact ⟨mid, nextPending, abstractTrace, refined⟩
      · exact ⟨next, nextPending, .next abstractTrace abstractStep, refined⟩

theorem reachable_writer_is_unique {limits : Limits} {world : World Payload}
    {creator : Writer} (trace : Trace limits (initialWorld creator) world)
    {group other : Nat} {one two : State Payload}
    (first : world.rows group = some one) (second : world.rows other = some two) :
    group = other := by
  obtain ⟨stream, pending, _, relation⟩ := traces_refine (initial_refines creator) trace
  obtain ⟨_, holder, active, here⟩ := row_shape relation first
  obtain ⟨_, another, activeAlso, there⟩ := row_shape relation second
  have same := Authority.active.inj (active.symm.trans activeAlso)
  rw [← here, ← there, same]

theorem reachable_rows_preserve_logical_bounds {limits : Limits} {world : World Payload}
    {creator : Writer} (trace : Trace limits (initialWorld creator) world)
    {group : Nat} {view : State Payload} (row : world.rows group = some view) :
    Kernel.Valid limits view := by
  obtain ⟨state, _, abstractTrace, relation⟩ := traces_refine (initial_refines creator) trace
  obtain ⟨rfl, _⟩ := row_shape relation row
  exact Kernel.every_trace_preserves_bounds (Kernel.initial_valid limits creator) abstractTrace

theorem observed_history_survives_move {limits : Limits} {first last : World Payload}
    {creator : Writer} (reachable : Trace limits (initialWorld creator) first)
    (later : Trace limits first last)
    {source target : Nat} {oldView newView : State Payload}
    (oldRow : first.rows source = some oldView) (newRow : last.rows target = some newView) :
    ∃ suffix, newView.history = oldView.history ++ suffix := by
  obtain ⟨_, _, _, oldRelation⟩ := traces_refine (initial_refines creator) reachable
  obtain ⟨next, _, abstractTrace, newRelation⟩ := traces_refine oldRelation later
  obtain ⟨rfl, _⟩ := row_shape oldRelation oldRow
  obtain ⟨rfl, _⟩ := row_shape newRelation newRow
  exact Kernel.trace_extends_history abstractTrace

theorem retired_world_cannot_reopen {limits : Limits}
    {before after : World Payload} {creator writer : Writer} {view : State Payload}
    (reachable : Trace limits (initialWorld creator) before)
    (row : before.rows writer.placement.group = some view)
    (active : view.authority = .active writer)
    (trace : Trace limits (applyAt before writer.placement.group {view with authority := .retired}) after) :
    ∀ group, after.rows group = none := by
  obtain ⟨_, _, _, known⟩ := traces_refine (initial_refines creator) reachable
  obtain ⟨rfl, _⟩ := row_shape known row
  have noPending := active_has_no_pending known active
  have atRetire : Refines (applyAt before writer.placement.group {view with authority := .retired})
      {view with authority := .retired} none := by
    rw [noPending] at known
    refine ⟨?_, by simp [Phase], known.issued, known.spent⟩
    simp only [applyAt, known.rows]
    exact clear_active_row active (by intro grant; simp)
  obtain ⟨latest, _, reachableAfterClose, final⟩ := traces_refine atRetire trace
  have closed := Kernel.retired_absorbs_trace rfl reachableAfterClose
  intro group
  simp [final.rows, localAt, closed]

theorem old_placement_grant_refused {limits : Limits} (certificate : Seal Payload) (lsn : Nat)
    (relocates : certificate.source.placement.group ≠ certificate.target.group) :
    ¬ AppendAdmissible limits (installed certificate) certificate.source lsn := by
  apply Kernel.stale_writer_refused
  intro same
  have equal := Authority.active.inj same
  exact relocates (congrArg (fun writer : Writer => writer.placement.group) equal).symm

theorem previous_generation_refused {limits : Limits} {state : State Payload}
    {current previous : Writer} (active : state.authority = .active current) (lsn : Nat)
    (older : previous.placement.generation < current.placement.generation) :
    ¬ AppendAdmissible limits state previous lsn := by
  apply Kernel.stale_writer_refused
  intro reuse
  have same := Authority.active.inj (active.symm.trans reuse)
  have equalGeneration := congrArg (fun writer : Writer => writer.placement.generation) same
  exact (Nat.ne_of_lt older) equalGeneration.symm

theorem prepared_move_is_executable {limits : Limits} {world : World Payload}
    (certificate : Seal Payload)
    (sourceRow : world.rows certificate.source.placement.group = some certificate.cut)
    (sourceGrant : certificate.cut.authority = .active certificate.source)
    (advances : certificate.source.placement.generation < certificate.target.generation)
    (relocates : certificate.source.placement.group ≠ certificate.target.group)
    (live : (world.slots certificate.target.group).live = some certificate.nonce) :
    ∃ targetWorld, Trace limits world targetWorld ∧
      targetWorld.rows certificate.target.group = some (installed certificate) := by
  refine ⟨installAt (sealAt world certificate) certificate, ?_, by simp [installAt, replace]⟩
  have seals : Step limits world (sealAt world certificate) :=
    .commitSeal certificate.target certificate.nonce sourceRow sourceGrant advances relocates live
  exact .next (.next (.same world) seals) (.install certificate (by simp [sealAt]) live)

#print axioms step_refines
#print axioms traces_refine
#print axioms reachable_writer_is_unique
#print axioms reachable_rows_preserve_logical_bounds
#print axioms observed_history_survives_move
#print axioms retired_world_cannot_reopen
#print axioms old_placement_grant_refused
#print axioms previous_generation_refused
#print axioms prepared_move_is_executable

end AuthorityRefinement
