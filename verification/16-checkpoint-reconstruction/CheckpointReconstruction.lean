import Kernel

set_option warningAsError true

namespace CheckpointReconstruction

structure StreamKey where
  deployment : Nat
  incarnation : Nat
  deriving DecidableEq

structure Cut where
  stream : StreamKey
  next : Nat

structure Engine (Db Payload Root : Type) where
  stream : StreamKey
  format : Nat
  origin : Db
  apply : Db → Kernel.Entry Payload → Db
  openRoot : Root → Option Db
  durableClosure : Root → Prop

structure Image (Db Payload Root : Type) where
  cut : Cut
  format : Nat
  root : Root
  committedPrefix : List (Kernel.Entry Payload)
  decoded : Db

def stateAt (engine : Engine Db Payload Root) (history : List (Kernel.Entry Payload)) (ending : Nat) :
    Db :=
  (history.take ending).foldl engine.apply engine.origin

structure Certified (engine : Engine Db Payload Root) (stream : Kernel.State Payload)
    (image : Image Db Payload Root) : Prop where
  scope : image.cut.stream = engine.stream
  format : image.format = engine.format
  withinHistory : image.cut.next ≤ stream.history.length
  exactPrefix : image.committedPrefix = stream.history.take image.cut.next
  durable : engine.durableClosure image.root
  rootMatches : engine.openRoot image.root = some image.decoded
  decodedAtCut : image.decoded = stateAt engine image.committedPrefix image.cut.next

structure Admitted (engine : Engine Db Payload Root) (stream : Kernel.State Payload)
    (image : Image Db Payload Root) (target : Cut) (records : List (Kernel.Entry Payload)) : Prop where
  live : stream.authority ≠ .retired
  scope : target.stream = engine.stream
  anchored : stream.firstRetained ≤ image.cut.next
  imageAtOrBefore : image.cut.next ≤ target.next
  boundedAtHead : target.next ≤ stream.history.length
  orderedExact : records = (stream.history.take target.next).drop image.cut.next

def replay (engine : Engine Db Payload Root) (root : Root) (records : List (Kernel.Entry Payload)) :
    Option Db :=
  (engine.openRoot root).map (fun start => records.foldl engine.apply start)

theorem admitted_replay_recovers_exact_cut {engine : Engine Db Payload Root}
    {stream : Kernel.State Payload} {image : Image Db Payload Root} {target : Cut}
    {records : List (Kernel.Entry Payload)}
    (certified : Certified engine stream image) (admitted : Admitted engine stream image target records) :
    replay engine image.root records = some (stateAt engine stream.history target.next) := by
  have exactTail : records = (stream.history.take target.next).drop image.cut.next :=
    admitted.orderedExact
  rw [replay, certified.rootMatches, Option.map_some, exactTail, certified.decodedAtCut]
  simp only [stateAt, certified.exactPrefix, List.take_take, Nat.min_self]
  rw [← List.foldl_append]
  have prefixAtImage : (stream.history.take target.next).take image.cut.next =
      stream.history.take image.cut.next := by
    rw [List.take_take, Nat.min_eq_left admitted.imageAtOrBefore]
  rw [← prefixAtImage, List.take_append_drop]

theorem later_commits_cannot_change_captured_cut {limits : Kernel.Limits}
    {before after : Kernel.State Payload} (moves : Kernel.Trace limits before after)
    (cut : Nat) (captured : cut ≤ before.history.length) :
    after.history.take cut = before.history.take cut := by
  obtain ⟨added, history⟩ := Kernel.trace_extends_history moves
  rw [history, List.take_append_of_le_length captured]

theorem exact_checkpoint_survives_logical_trace {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {before after : Kernel.State Payload}
    {image : Image Db Payload Root} (certificate : Certified engine before image)
    (moves : Kernel.Trace limits before after) :
    Certified engine after image := by
  obtain ⟨added, history⟩ := Kernel.trace_extends_history moves
  have stableCut := later_commits_cannot_change_captured_cut moves image.cut.next certificate.withinHistory
  refine ⟨certificate.scope, certificate.format, ?_, certificate.exactPrefix.trans stableCut.symm,
    certificate.durable, certificate.rootMatches, certificate.decodedAtCut⟩
  rw [history, List.length_append]
  exact Nat.le_trans certificate.withinHistory (Nat.le_add_right _ _)

theorem foreign_receipt_refused {engine : Engine Db Payload Root}
    {stream : Kernel.State Payload} {image : Image Db Payload Root}
    (foreign : image.cut.stream ≠ engine.stream) : ¬ Certified engine stream image :=
  fun signed => foreign signed.scope

theorem cannot_cross_unprotected_gap {engine : Engine Db Payload Root}
    {stream : Kernel.State Payload} {image : Image Db Payload Root} {target : Cut}
    {records : List (Kernel.Entry Payload)}
    (gap : image.cut.next < stream.firstRetained) :
    ¬ Admitted engine stream image target records :=
  fun admitted => Nat.not_le_of_lt gap admitted.anchored

theorem recovers_at_captured_cut_after_append {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {before after : Kernel.State Payload}
    {image : Image Db Payload Root} {target : Cut} {records : List (Kernel.Entry Payload)}
    (moves : Kernel.Trace limits before after) (captured : target.next ≤ before.history.length)
    (certified : Certified engine after image) (admitted : Admitted engine after image target records) :
    replay engine image.root records = some (stateAt engine before.history target.next) := by
  rw [admitted_replay_recovers_exact_cut certified admitted, stateAt,
    later_commits_cannot_change_captured_cut moves target.next captured]
  rfl

theorem fork_root_can_be_reissued_at_child_genesis {parent child : Engine Db Payload Root}
    {base : Kernel.State Payload} {image : Image Db Payload Root}
    (source : Certified parent base image)
    (origin : child.origin = image.decoded)
    (childReads : child.openRoot image.root = some image.decoded)
    (childCustody : child.durableClosure image.root) (distinct : child.stream ≠ parent.stream)
    (writer : Kernel.Writer) :
    Certified child (Kernel.initial writer)
      {cut := ⟨child.stream, 0⟩, format := child.format, root := image.root,
       committedPrefix := [], decoded := image.decoded} ∧
      child.stream ≠ parent.stream ∧ child.origin = stateAt parent base.history image.cut.next := by
  refine ⟨⟨rfl, rfl, Nat.zero_le _, rfl, childCustody, childReads, origin.symm⟩, distinct, ?_⟩
  rw [origin, source.decodedAtCut, stateAt, source.exactPrefix, List.take_take, Nat.min_self]
  rfl

theorem publish_certified_checkpoint_program {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {stream : Kernel.State Payload} {writer : Kernel.Writer}
    {image : Image Db Payload Root} (certificate : Certified engine stream image)
    (authorized : stream.authority = .active writer)
    (advances : stream.checkpointEnd ≤ image.cut.next) :
    ∃ published, Kernel.Step limits stream published ∧
      published.checkpointEnd = image.cut.next ∧ Certified engine published image := by
  let published := {stream with checkpointEnd := image.cut.next}
  have publishStep : Kernel.Step limits stream published :=
    .publish image.cut.next authorized advances certificate.withinHistory
  exact ⟨published, publishStep, rfl,
    exact_checkpoint_survives_logical_trace certificate (.next (.same _) publishStep)⟩

theorem trim_certified_checkpoint_program {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {stream : Kernel.State Payload} {writer : Kernel.Writer}
    {image : Image Db Payload Root} (certificate : Certified engine stream image) (cut : Nat)
    (authorized : stream.authority = .active writer)
    (adopted : stream.checkpointEnd = image.cut.next)
    (advances : stream.firstRetained ≤ cut) (withinImage : cut ≤ image.cut.next)
    (preservesHolds : ∀ id lsn, stream.replays id = .holding lsn → cut ≤ lsn) :
    ∃ trimmed, Kernel.Step limits stream trimmed ∧
      trimmed.firstRetained = cut ∧ trimmed.firstRetained ≤ image.cut.next ∧ Certified engine trimmed image := by
  let trimmed := {stream with firstRetained := cut}
  have trimStep : Kernel.Step limits stream trimmed :=
    .trim cut authorized advances (adopted.symm ▸ withinImage) preservesHolds
  exact ⟨trimmed, trimStep, rfl, withinImage,
    exact_checkpoint_survives_logical_trace certificate (.next (.same _) trimStep)⟩

structure Catalog (Db Payload Root : Type) where
  stream : Kernel.State Payload
  image : Image Db Payload Root

def CatalogSound (engine : Engine Db Payload Root) (limits : Kernel.Limits)
    (catalog : Catalog Db Payload Root) : Prop :=
  Kernel.Valid limits catalog.stream ∧ Certified engine catalog.stream catalog.image ∧
    catalog.stream.checkpointEnd = catalog.image.cut.next

inductive CatalogStep {Db Payload Root : Type} (engine : Engine Db Payload Root)
    (limits : Kernel.Limits) : Catalog Db Payload Root → Catalog Db Payload Root → Prop
  | ordered {catalog} (stream : Kernel.State Payload)
      (decision : Kernel.Step limits catalog.stream stream)
      (samePublishedCut : stream.checkpointEnd = catalog.stream.checkpointEnd) :
      CatalogStep engine limits catalog {catalog with stream := stream}
  | adopt {catalog writer} (image : Image Db Payload Root)
      (receipt : Certified engine catalog.stream image)
      (authorized : catalog.stream.authority = .active writer)
      (advances : catalog.stream.checkpointEnd ≤ image.cut.next) :
      CatalogStep engine limits catalog
        ⟨{catalog.stream with checkpointEnd := image.cut.next}, image⟩

theorem adopted_steps_preserve_certified_cut {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {before after : Catalog Db Payload Root}
    (sound : CatalogSound engine limits before) (step : CatalogStep engine limits before after) :
    Kernel.Step limits before.stream after.stream ∧ CatalogSound engine limits after := by
  cases step with
  | ordered _ decision same =>
      have unchanged : _ = before.stream.checkpointEnd := same
      exact ⟨decision, Kernel.step_preserves_valid sound.1 decision,
        exact_checkpoint_survives_logical_trace sound.2.1 (.next (.same _) decision),
        unchanged.trans sound.2.2⟩
  | adopt image receipt authorized advances =>
      have effect := Kernel.Step.publish (limits := limits) image.cut.next authorized advances receipt.withinHistory
      exact ⟨effect, Kernel.step_preserves_valid sound.1 effect,
        exact_checkpoint_survives_logical_trace receipt (.next (.same _) effect), rfl⟩

inductive CatalogTrace {Db Payload Root : Type} (engine : Engine Db Payload Root)
    (limits : Kernel.Limits) : Catalog Db Payload Root → Catalog Db Payload Root → Prop
  | same (catalog : Catalog Db Payload Root) : CatalogTrace engine limits catalog catalog
  | next {first before after} : CatalogTrace engine limits first before →
      CatalogStep engine limits before after → CatalogTrace engine limits first after

theorem certified_catalog_refines_kernel {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {first last : Catalog Db Payload Root}
    (sound : CatalogSound engine limits first) (trace : CatalogTrace engine limits first last) :
    Kernel.Trace limits first.stream last.stream ∧ CatalogSound engine limits last := by
  induction trace with
  | same => exact ⟨.same _, sound⟩
  | next _ step prior =>
      obtain ⟨decision, safe⟩ := adopted_steps_preserve_certified_cut prior.2 step
      exact ⟨.next prior.1 decision, safe⟩

theorem recovery_from_published_image_is_executable {engine : Engine Db Payload Root}
    {limits : Kernel.Limits} {catalog : Catalog Db Payload Root}
    (sound : CatalogSound engine limits catalog) (target : Cut)
    (live : catalog.stream.authority ≠ .retired)
    (scope : target.stream = engine.stream)
    (fromCheckpoint : catalog.image.cut.next ≤ target.next)
    (committed : target.next ≤ catalog.stream.history.length) :
    ∃ records, Admitted engine catalog.stream catalog.image target records ∧
      replay engine catalog.image.root records = some (stateAt engine catalog.stream.history target.next) := by
  let records := (catalog.stream.history.take target.next).drop catalog.image.cut.next
  have floor : catalog.stream.firstRetained ≤ catalog.image.cut.next :=
    sound.2.2 ▸ sound.1.trimCertified
  have grant : Admitted engine catalog.stream catalog.image target records :=
    ⟨live, scope, floor, fromCheckpoint, committed, rfl⟩
  exact ⟨records, grant, admitted_replay_recovers_exact_cut sound.2.1 grant⟩

#print axioms admitted_replay_recovers_exact_cut
#print axioms later_commits_cannot_change_captured_cut
#print axioms exact_checkpoint_survives_logical_trace
#print axioms foreign_receipt_refused
#print axioms cannot_cross_unprotected_gap
#print axioms recovers_at_captured_cut_after_append
#print axioms fork_root_can_be_reissued_at_child_genesis
#print axioms publish_certified_checkpoint_program
#print axioms trim_certified_checkpoint_program
#print axioms adopted_steps_preserve_certified_cut
#print axioms certified_catalog_refines_kernel
#print axioms recovery_from_published_image_is_executable

end CheckpointReconstruction
