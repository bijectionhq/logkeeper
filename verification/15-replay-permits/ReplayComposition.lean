import Kernel
import ReadCustody

set_option warningAsError true

namespace ReplayComposition

structure Snapshot (Request Extent Payload : Type) where
  stream : Kernel.State Payload
  storage : ReadCustody.Store Request Extent Payload

def BoundRead (stream : Kernel.State Payload) (permit : Nat) (image : ReadCustody.Image Extent Payload) : Prop :=
  ∃ (first lsn : Nat) (entry : Kernel.Entry Payload), stream.replays permit = .holding first ∧ first ≤ lsn ∧
    stream.history[lsn]? = some entry ∧ image.bytes = entry.bytes

def InHistory (stream : Kernel.State Payload) (image : ReadCustody.Image Extent Payload) : Prop :=
  ∃ (lsn : Nat) (entry : Kernel.Entry Payload), stream.history[lsn]? = some entry ∧ image.bytes = entry.bytes

def Valid (limits : Kernel.Limits) (snapshot : Snapshot Request Extent Payload) : Prop :=
  Kernel.Valid limits snapshot.stream ∧ ReadCustody.Covered snapshot.storage ∧
    ∀ request image, snapshot.storage.operations request = .borrowing image →
      InHistory snapshot.stream image

inductive Step {Request Extent Payload : Type} [DecidableEq Request] [DecidableEq Extent]
    (limits : Kernel.Limits) (effectiveStop : Request → Prop) (permit : Nat) :
    Snapshot Request Extent Payload → Snapshot Request Extent Payload → Prop
  | physical {before} (storage : ReadCustody.Store Request Extent Payload)
      (action : ReadCustody.Step effectiveStop before.storage storage)
      (checked : ∀ request image, before.storage.operations request ≠ .borrowing image →
        storage.operations request = .borrowing image → BoundRead before.stream permit image) :
      Step limits effectiveStop permit before {before with storage := storage}
  | logical {before} (stream : Kernel.State Payload) (action : Kernel.Step limits before.stream stream)
      (preservesOpen : before.storage.admitting = true → ∀ first,
          before.stream.replays permit = .holding first → stream.replays permit = .holding first) :
      Step limits effectiveStop permit before {before with stream := stream}

private theorem history_witness_survives {Extent Payload : Type}
    {before after : Kernel.State Payload} {limits : Kernel.Limits}
    (action : Kernel.Step limits before after) {image : ReadCustody.Image Extent Payload}
    (witness : InHistory before image) : InHistory after image := by
  obtain ⟨lsn, entry, exactEntry, exactImage⟩ := witness
  obtain ⟨tail, keeps⟩ := Kernel.step_extends_history action
  obtain ⟨beforeEnd, _⟩ := List.getElem?_eq_some_iff.mp exactEntry
  refine ⟨lsn, entry, ?_, exactImage⟩
  rw [keeps, List.getElem?_append_left beforeEnd]
  exact exactEntry

theorem step_preserves_exact_snapshot {Request Extent Payload : Type}
    [DecidableEq Request] [DecidableEq Extent] {limits : Kernel.Limits}
    {effectiveStop : Request → Prop} {permit : Nat} {before after : Snapshot Request Extent Payload}
    (prior : Valid limits before) (step : Step limits effectiveStop permit before after) :
    Valid limits after := by
  obtain ⟨logical, physical, existing⟩ := prior
  cases step with
  | physical storage action checked =>
      refine ⟨logical, ReadCustody.step_preserves_exact_borrows physical action, ?_⟩
      intro request image borrowing
      by_cases remains : before.storage.operations request = .borrowing image
      · exact existing request image remains
      · obtain ⟨_, lsn, entry, _, _, chosen, same⟩ := checked request image remains borrowing
        exact ⟨lsn, entry, chosen, same⟩
  | logical _ action _ =>
      refine ⟨Kernel.step_preserves_valid logical action, physical, ?_⟩
      intro request image borrowing
      exact history_witness_survives action (existing request image borrowing)

inductive Trace {Request Extent Payload : Type} [DecidableEq Request] [DecidableEq Extent]
    (limits : Kernel.Limits) (effectiveStop : Request → Prop) (permit : Nat) :
    Snapshot Request Extent Payload → Snapshot Request Extent Payload → Prop
  | same (snapshot : Snapshot Request Extent Payload) : Trace limits effectiveStop permit snapshot snapshot
  | next {origin before after} : Trace limits effectiveStop permit origin before →
      Step limits effectiveStop permit before after → Trace limits effectiveStop permit origin after

theorem trace_refines_both_boundaries {Request Extent Payload : Type}
    [DecidableEq Request] [DecidableEq Extent] {limits : Kernel.Limits}
    {effectiveStop : Request → Prop} {permit : Nat} {first last : Snapshot Request Extent Payload}
    (trace : Trace limits effectiveStop permit first last) :
    Kernel.Trace limits first.stream last.stream ∧
      ReadCustody.Trace effectiveStop first.storage last.storage := by
  induction trace with
  | same => exact ⟨.same _, .same _⟩
  | next _ step prior =>
      cases step with
      | physical _ motion _ => exact ⟨prior.1, .next prior.2 motion⟩
      | logical _ decision _ => exact ⟨.next prior.1 decision, prior.2⟩

theorem active_borrows_keep_original_bytes {Request Extent Payload : Type}
    [DecidableEq Request] [DecidableEq Extent] {limits : Kernel.Limits}
    {effectiveStop : Request → Prop} {permit : Nat} {first last : Snapshot Request Extent Payload}
    (valid : Valid limits first) (trace : Trace limits effectiveStop permit first last)
    (request : Request) (image : ReadCustody.Image Extent Payload)
    (borrowing : last.storage.operations request = .borrowing image) :
    last.storage.physical image.extent = some image.bytes ∧ InHistory last.stream image := by
  have known : Valid limits last := by
    clear borrowing
    induction trace with
    | same => exact valid
    | next _ step prior => exact step_preserves_exact_snapshot prior step
  exact ⟨known.2.1 request image borrowing, known.2.2 request image borrowing⟩

theorem open_gate_preserves_its_permit {Request Extent Payload : Type}
    [DecidableEq Request] [DecidableEq Extent] {limits : Kernel.Limits}
    {effectiveStop : Request → Prop} {permit firstLsn : Nat}
    {first last : Snapshot Request Extent Payload}
    (admitted : first.stream.replays permit = .holding firstLsn)
    (trace : Trace limits effectiveStop permit first last) :
    last.storage.admitting = true → last.stream.replays permit = .holding firstLsn := by
  induction trace with
  | same => exact fun _ => admitted
  | next _ step prior =>
      intro openAfter
      cases step with
      | physical _ action _ =>
          exact prior (ReadCustody.admission_was_open action openAfter)
      | logical _ _ preserves =>
          exact preserves openAfter firstLsn (prior openAfter)

theorem closed_replay_can_trim_before_its_last_borrow_completes
    {Request Extent Payload : Type} [DecidableEq Request] [DecidableEq Extent]
    {limits : Kernel.Limits} {effectiveStop : Request → Prop}
    {before : Snapshot Request Extent Payload} {writer : Kernel.Writer}
    (permit cut : Nat) (issued : permit ≤ before.stream.replayIssued)
    (authority : before.stream.authority = .active writer)
    (advances : before.stream.firstRetained ≤ cut) (published : cut ≤ before.stream.checkpointEnd)
    (otherHolds : ∀ id lsn, id ≠ permit → before.stream.replays id = .holding lsn → cut ≤ lsn)
    (request : Request) (image : ReadCustody.Image Extent Payload)
    (borrowing : before.storage.operations request = .borrowing image) :
    ∃ after, Trace limits effectiveStop permit before after ∧
      after.stream.firstRetained = cut ∧ after.stream.replays permit = .unused ∧
      after.storage.admitting = false ∧ after.storage.operations request = .completed image.bytes := by
  let closed : Snapshot Request Extent Payload := {before with storage := {before.storage with admitting := false}}
  have closeGate : Step limits effectiveStop permit before closed :=
    .physical closed.storage .closeAdmission (by intro _ _ changed now; exact False.elim (changed now))
  let released : Snapshot Request Extent Payload := {closed with
    stream := {closed.stream with replays := Kernel.replaceReplay closed.stream.replays permit .unused}}
  have closeHold : Step limits effectiveStop permit closed released :=
    .logical released.stream (.releaseReplay permit issued) (by intro gate; simp [closed] at gate)
  let trimmed : Snapshot Request Extent Payload := {released with stream := {released.stream with firstRetained := cut}}
  have canTrim : ∀ id lsn, released.stream.replays id = .holding lsn → cut ≤ lsn := by
    intro id lsn held
    by_cases sameId : id = permit
    · simp [released, Kernel.replaceReplay, sameId] at held
    · exact otherHolds id lsn sameId (by simpa [released, Kernel.replaceReplay, sameId] using held)
  have trim : Step limits effectiveStop permit released trimmed :=
    .logical trimmed.stream (.trim cut authority advances published canTrim) (by intro _ _ same; exact same)
  let complete : Snapshot Request Extent Payload := {trimmed with storage := {trimmed.storage with
    operations := ReadCustody.replace trimmed.storage.operations request (.completed image.bytes)}}
  have finish : Step limits effectiveStop permit trimmed complete := by
    have priorBorrow : trimmed.storage.operations request = .borrowing image := borrowing
    refine Step.physical (before := trimmed) complete.storage (.finish request image priorBorrow) ?_
    intro other observed changed now
    by_cases sameId : other = request
    · simp [complete, ReadCustody.replace, sameId] at now
    · exact False.elim (changed (by simpa [complete, ReadCustody.replace, sameId] using now))
  exact ⟨complete, .next (.next (.next (.next (.same before) closeGate) closeHold) trim) finish,
    rfl, by simp [complete, trimmed, released, Kernel.replaceReplay],
    rfl, by simp [complete, ReadCustody.replace]⟩

#print axioms step_preserves_exact_snapshot
#print axioms trace_refines_both_boundaries
#print axioms active_borrows_keep_original_bytes
#print axioms open_gate_preserves_its_permit
#print axioms closed_replay_can_trim_before_its_last_borrow_completes

end ReplayComposition
