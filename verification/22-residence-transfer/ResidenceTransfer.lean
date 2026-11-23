import CheckpointReconstruction
import SharedCustody

set_option warningAsError true

namespace ResidenceTransfer

structure Slice where
  version : Nat
  offset : Nat
  length : Nat

structure Manifest (Object Byte : Type) where
  member : Object → Option Slice
  readVersion : Nat → Option (List Byte)

def readMember (root : Manifest Object Byte) (object : Object) : Option (List Byte) := do
  let slice ← root.member object
  let pack ← root.readVersion slice.version
  if slice.offset + slice.length ≤ pack.length then
    some ((pack.drop slice.offset).take slice.length)
  else none

def readInputs (root : Manifest Object Byte) : List Object → Option (List (List Byte))
  | [] => some []
  | object :: remaining => do
      let bytes ← readMember root object
      let inputs ← readInputs root remaining
      pure (bytes :: inputs)

def EquivalentClosure (required : Object → Prop) (origin replacement : Manifest Object Byte) : Prop :=
  ∀ object, required object →
    ∃ bytes, readMember origin object = some bytes ∧ readMember replacement object = some bytes

theorem range_validator_returns_full_member {root : Manifest Object Byte} {object : Object}
    {slice : Slice} {pack : List Byte} (member : root.member object = some slice)
    (body : root.readVersion slice.version = some pack)
    (withinPack : slice.offset + slice.length ≤ pack.length) :
    readMember root object = some ((pack.drop slice.offset).take slice.length) ∧
      ((pack.drop slice.offset).take slice.length).length = slice.length := by
  constructor
  · simp [readMember, member, body, withinPack]
  · rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]

theorem out_of_range_member_cannot_be_read {root : Manifest Object Byte} {object : Object}
    {slice : Slice} {pack : List Byte} (member : root.member object = some slice)
    (body : root.readVersion slice.version = some pack)
    (truncated : pack.length < slice.offset + slice.length) :
    readMember root object = none := by
  simp [readMember, member, body, Nat.not_le_of_lt truncated]

theorem equivalent_closure_preserves_every_declared_read_sequence
    {required : Object → Prop} {origin replacement : Manifest Object Byte}
    (same : EquivalentClosure required origin replacement) (reads : List Object)
    (declared : ∀ object, object ∈ reads → required object) :
    readInputs origin reads = readInputs replacement reads := by
  induction reads with
  | nil => rfl
  | cons object rest prior =>
      have needed := declared object List.mem_cons_self
      obtain ⟨_, originalBody, replacementBody⟩ := same object needed
      have tail := prior (fun item member => declared item (List.mem_cons_of_mem _ member))
      simp [readInputs, originalBody, replacementBody, tail]

private def originalPack : Manifest Bool Nat :=
  ⟨fun object => some ⟨10, if object then 0 else 1, 1⟩,
    fun version => if version = 10 then some [1, 4] else none⟩

private def reversedPack (reindexed : Bool) : Manifest Bool Nat :=
  ⟨fun object => some ⟨20, if object = reindexed then 1 else 0, 1⟩,
    fun version => if version = 20 then some [4, 1] else none⟩

theorem repacked_members_can_preserve_the_image_with_different_carrier_bytes :
    EquivalentClosure (fun _ => True) originalPack (reversedPack true) ∧
      originalPack.readVersion 10 ≠ (reversedPack true).readVersion 20 := by
  refine ⟨?_, by decide⟩
  intro object _
  cases object
  · exact ⟨[4], rfl, rfl⟩
  · exact ⟨[1], rfl, rfl⟩

theorem wrong_pack_index_fails_even_with_the_same_carrier_bytes :
    (reversedPack true).readVersion 20 = (reversedPack false).readVersion 20 ∧
      ¬ EquivalentClosure (fun _ => True) originalPack (reversedPack false) := by
  refine ⟨rfl, ?_⟩
  intro accepts
  obtain ⟨bytes, origin, replacement⟩ := accepts true True.intro
  change some [1] = some bytes at origin
  change some [4] = some bytes at replacement
  exact (show ([1] : List Nat) ≠ [4] by decide) (Option.some.inj (origin.trans replacement.symm))

structure Origin where
  referrer : CheckpointReconstruction.StreamKey
  revision : Nat
  cut : Nat
  root : Nat
  deriving DecidableEq

structure PhysicalRoot where
  residence : Nat
  version : Nat
  deriving DecidableEq

structure Plan where
  origin : Origin
  destination : PhysicalRoot

structure Prepared (Object Byte : Type) where
  plan : Plan
  sourceManifest : Manifest Object Byte
  targetManifest : Manifest Object Byte

structure Manifests (Object Byte : Type) where
  captured : Origin → Manifest Object Byte
  installed : PhysicalRoot → Manifest Object Byte

structure LiveVerification (required : Object → Prop) (manifests : Manifests Object Byte)
    (holds : PhysicalRoot → Prop) (prepared : Prepared Object Byte) : Prop where
  captured : prepared.sourceManifest = manifests.captured prepared.plan.origin
  installed : prepared.targetManifest = manifests.installed prepared.plan.destination
  exact : EquivalentClosure required prepared.sourceManifest prepared.targetManifest
  registered : holds prepared.plan.destination

structure Publication (required : Object → Prop) (manifests : Manifests Object Byte) (holds : PhysicalRoot → Prop)
    (current : Origin) (target : PhysicalRoot) (prepared : Prepared Object Byte) : Prop where
  origin : prepared.plan.origin = current
  destination : prepared.plan.destination = target
  verification : LiveVerification required manifests holds prepared

theorem stale_origin_cannot_publish
    {required : Object → Prop} {manifests : Manifests Object Byte} {holds : PhysicalRoot → Prop}
    {current : Origin} {target : PhysicalRoot} {prepared : Prepared Object Byte}
    (changed : prepared.plan.origin ≠ current) :
    ¬ Publication required manifests holds current target prepared :=
  fun admitted => changed admitted.origin

theorem preparation_cannot_publish_to_a_replacement_incarnation
    {required : Object → Prop} {manifests : Manifests Object Byte} {holds : PhysicalRoot → Prop}
    {current : Origin} {target : PhysicalRoot} {prepared : Prepared Object Byte}
    (changed : prepared.plan.destination.residence ≠ target.residence) :
    ¬ Publication required manifests holds current target prepared :=
  fun admitted => changed (congrArg PhysicalRoot.residence admitted.destination)

theorem verified_publication_has_live_target_registration
    {required : Object → Prop} {manifests : Manifests Object Byte} {holds : PhysicalRoot → Prop}
    {current : Origin} {target : PhysicalRoot} {prepared : Prepared Object Byte}
    (publish : Publication required manifests holds current target prepared) :
    holds target := by
  have liveGrant : holds prepared.plan.destination := publish.verification.registered
  exact publish.destination ▸ liveGrant

theorem committed_checkpoint_rehomes_with_identical_replay
    {engine : CheckpointReconstruction.Engine Db Payload Root} {stream : Kernel.State Payload}
    {image : CheckpointReconstruction.Image Db Payload Root} (destinationRoot : Root)
    {required : Object → Prop} {origin replacement : Manifest Object Byte}
    (source : CheckpointReconstruction.Certified engine stream image)
    (same : EquivalentClosure required origin replacement)
    (inputs : List Object) (declared : ∀ object, object ∈ inputs → required object)
    (decode : List (List Byte) → Db)
    (sourceCodec : engine.openRoot image.root = (readInputs origin inputs).map decode)
    (replacementCodec : engine.openRoot destinationRoot = (readInputs replacement inputs).map decode)
    (custody : engine.durableClosure destinationRoot) :
    CheckpointReconstruction.Certified engine stream {image with root := destinationRoot} ∧
      ∀ tail, CheckpointReconstruction.replay engine destinationRoot tail =
        CheckpointReconstruction.replay engine image.root tail := by
  have identicalOpen : engine.openRoot destinationRoot = engine.openRoot image.root := by
    rw [sourceCodec, replacementCodec, equivalent_closure_preserves_every_declared_read_sequence same inputs declared]
  refine ⟨⟨source.scope, source.format, source.withinHistory, source.exactPrefix,
    custody, identicalOpen.trans source.rootMatches, source.decodedAtCut⟩, ?_⟩
  intro tail
  simp [CheckpointReconstruction.replay, identicalOpen]

theorem verified_root_offline_publication_has_same_read_inputs
    {required : Object → Prop} {manifests : Manifests Object Byte} {holds : PhysicalRoot → Prop}
    {current : Origin} {target : PhysicalRoot} {prepared : Prepared Object Byte}
    (publish : Publication required manifests holds current target prepared)
    (reads : List Object) (declared : ∀ object, object ∈ reads → required object) :
    holds target ∧ readInputs (manifests.installed target) reads = readInputs (manifests.captured current) reads := by
  have captured : prepared.sourceManifest = manifests.captured prepared.plan.origin := publish.verification.captured
  have installed : prepared.targetManifest = manifests.installed prepared.plan.destination := publish.verification.installed
  have same : EquivalentClosure required prepared.sourceManifest prepared.targetManifest := publish.verification.exact
  rw [publish.origin] at captured
  rw [publish.destination] at installed
  rw [← captured, ← installed]
  exact ⟨verified_publication_has_live_target_registration publish,
    (equivalent_closure_preserves_every_declared_read_sequence same reads declared).symm⟩

theorem adopting_rehomed_root_preserves_catalog_and_exact_cut
    {engine : CheckpointReconstruction.Engine Db Payload Root} {limits : Kernel.Limits}
    {catalog : CheckpointReconstruction.Catalog Db Payload Root} {writer : Kernel.Writer}
    (sound : CheckpointReconstruction.CatalogSound engine limits catalog)
    (active : catalog.stream.authority = .active writer)
    (destinationRoot : Root)
    (verified : CheckpointReconstruction.Certified engine catalog.stream
      {catalog.image with root := destinationRoot}) :
    ∃ installed, CheckpointReconstruction.CatalogStep engine limits catalog installed ∧
      CheckpointReconstruction.CatalogSound engine limits installed ∧
      installed.image.root = destinationRoot ∧ installed.stream = catalog.stream := by
  let image := {catalog.image with root := destinationRoot}
  let installed : CheckpointReconstruction.Catalog Db Payload Root :=
    ⟨{catalog.stream with checkpointEnd := image.cut.next}, image⟩
  have advances : catalog.stream.checkpointEnd ≤ image.cut.next :=
    Nat.le_of_eq sound.2.2
  have adopt : CheckpointReconstruction.CatalogStep engine limits catalog installed :=
    .adopt image verified active advances
  have unchanged : installed.stream = catalog.stream := by
    have boundary : image.cut.next = catalog.stream.checkpointEnd := sound.2.2.symm
    simp [installed, boundary]
  exact ⟨installed, adopt, (CheckpointReconstruction.adopted_steps_preserve_certified_cut sound adopt).2,
    rfl, unchanged⟩

theorem only_unshared_unborrowed_source_is_eligible_for_disposal
    {needs : SharedCustody.Dependencies} {store : SharedCustody.Store}
    {closeAllowed : Nat → Prop} {version : Nat}
    (covered : SharedCustody.Covered needs store)
    (fence : SharedCustody.Step needs closeAllowed store
      {store with gates := SnapshotAdmission.setSlot store.gates version .deleting}) :
    (∀ root, store.refs root version ≠ .held) ∧ store.borrows version = 0 := by
  have afterward := SharedCustody.every_step_keeps_dependencies covered fence
  have closed : SnapshotAdmission.setSlot store.gates version .deleting version = .deleting := by
    simp [SnapshotAdmission.setSlot]
  constructor
  · intro root held
    have impossible : SharedCustody.VersionPhase.deleting = .open :=
      closed.symm.trans (afterward.referenceGate root version held)
    cases impossible
  · by_cases empty : store.borrows version = 0
    · exact empty
    · have impossible : SharedCustody.VersionPhase.deleting = .open :=
        closed.symm.trans (afterward.borrowGate version (Nat.pos_of_ne_zero empty))
      cases impossible

theorem exact_source_disposal_preserves_every_live_root
    {needs : SharedCustody.Dependencies} {store : SharedCustody.Store}
    {closeAllowed : Nat → Prop} {old : Nat}
    (covered : SharedCustody.Covered needs store)
    (openGate : store.gates old = .open)
    (unreferenced : ∀ root, store.refs root old ≠ .held) (idle : store.borrows old = 0) :
    ∃ after, SharedCustody.Trace needs closeAllowed store after ∧ after.physical old = false ∧
      ∀ root version, store.roots root = .live → needs root version → after.physical version = true := by
  obtain ⟨after, history, erased, unchanged⟩ :=
    SharedCustody.unshared_unborrowed_version_can_be_erased (closeAllowed := closeAllowed) old
      openGate unreferenced idle
  refine ⟨after, history, erased, ?_⟩
  intro root version live needed
  have exactBytes := SharedCustody.live_manifest_has_exact_version covered live needed
  have distinct : version ≠ old := by
    intro same
    subst version
    exact unreferenced root (covered.complete root old live needed)
  exact (unchanged version distinct).trans exactBytes

theorem held_old_snapshot_rejects_disposition_even_before_first_borrow
    {environment : SnapshotAdmission.Environment} {edge contains : Nat → Nat → Prop}
    {first last : SharedCustody.Product} {closeAllowed : Nat → Prop}
    (sound : SharedCustody.ProductSound environment (SharedCustody.transitiveDependencies edge contains) first)
    (trace : SharedCustody.ProductTrace environment (SharedCustody.transitiveDependencies edge contains) first last)
    {id : Nat} {basis : SnapshotAdmission.Basis} (snapshot : last.catalog.snapshots id = some basis)
    {node version : Nat} (reachable : SharedCustody.Path edge basis.root node) (containsVersion : contains node version) :
    ¬ SharedCustody.Step (SharedCustody.transitiveDependencies edge contains) closeAllowed last.store
        {last.store with gates := SnapshotAdmission.setSlot last.store.gates version .deleting} := by
  intro fence
  have current := SharedCustody.product_trace_preserves_checkpoint_dependencies sound trace
  have owner := (current.catalog.live id basis snapshot).rootPresent
  have live := current.backed basis.root basis.start owner
  have pin := current.storage.complete basis.root version live ⟨node, reachable, containsVersion⟩
  have unused := (only_unshared_unborrowed_source_is_eligible_for_disposal current.storage fence).1
  exact unused basis.root pin

#print axioms range_validator_returns_full_member
#print axioms out_of_range_member_cannot_be_read
#print axioms equivalent_closure_preserves_every_declared_read_sequence
#print axioms repacked_members_can_preserve_the_image_with_different_carrier_bytes
#print axioms wrong_pack_index_fails_even_with_the_same_carrier_bytes
#print axioms stale_origin_cannot_publish
#print axioms preparation_cannot_publish_to_a_replacement_incarnation
#print axioms verified_publication_has_live_target_registration
#print axioms committed_checkpoint_rehomes_with_identical_replay
#print axioms verified_root_offline_publication_has_same_read_inputs
#print axioms adopting_rehomed_root_preserves_catalog_and_exact_cut
#print axioms only_unshared_unborrowed_source_is_eligible_for_disposal
#print axioms exact_source_disposal_preserves_every_live_root
#print axioms held_old_snapshot_rejects_disposition_even_before_first_borrow

end ResidenceTransfer
