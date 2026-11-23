import SnapshotAdmission

set_option warningAsError true

namespace SharedCustody

open SnapshotAdmission (setSlot)

inductive RootPhase where
  | fresh
  | preparing
  | live
  | closed
  deriving DecidableEq

inductive Reference where
  | unused
  | held
  | closed
  deriving DecidableEq

inductive VersionPhase where
  | open
  | deleting
  | gone
  deriving DecidableEq

structure Store where
  roots : Nat → RootPhase
  gates : Nat → VersionPhase
  physical : Nat → Bool
  refs : Nat → Nat → Reference
  borrows : Nat → Nat

abbrev Dependencies := Nat → Nat → Prop

def setReference (refs : Nat → Nat → Reference) (root version : Nat) (value : Reference) :
    Nat → Nat → Reference :=
  setSlot refs root (setSlot (refs root) version value)

structure Covered (needs : Dependencies) (store : Store) : Prop where
  complete : ∀ root version, store.roots root = .live → needs root version → store.refs root version = .held
  referenceGate : ∀ root version, store.refs root version = .held → store.gates version = .open
  borrowGate : ∀ version, 0 < store.borrows version → store.gates version = .open
  bytes : ∀ version, store.gates version ≠ .gone → store.physical version = true

inductive Step (needs : Dependencies) (closeAllowed : Nat → Prop) : Store → Store → Prop
  | begin {store} (root : Nat) (fresh : store.roots root = .fresh) :
      Step needs closeAllowed store {store with roots := setSlot store.roots root .preparing}
  | acquire {store} (root version : Nat) (dependency : needs root version)
      (prepared : store.roots root ≠ .fresh) (unused : store.refs root version = .unused)
      (admitting : store.gates version = .open) :
      Step needs closeAllowed store {store with refs := setReference store.refs root version .held}
  | admit {store} (root : Nat) (preparing : store.roots root = .preparing)
      (complete : ∀ version, needs root version → store.refs root version = .held) :
      Step needs closeAllowed store {store with roots := setSlot store.roots root .live}
  | close {store} (root : Nat) (issued : store.roots root ≠ .fresh) (allowed : closeAllowed root) :
      Step needs closeAllowed store {store with roots := setSlot store.roots root .closed}
  | release {store} (root version : Nat) (closed : store.roots root = .closed) :
      Step needs closeAllowed store {store with refs := setReference store.refs root version .closed}
  | borrow {store} (root version : Nat) (live : store.roots root = .live)
      (registered : store.refs root version = .held) :
      Step needs closeAllowed store {store with borrows := setSlot store.borrows version (store.borrows version + 1)}
  | finish {store} (version : Nat) (present : 0 < store.borrows version) :
      Step needs closeAllowed store {store with borrows := setSlot store.borrows version (store.borrows version - 1)}
  | fenceDisposal {store} (version : Nat) (openGate : store.gates version = .open)
      (unreferenced : ∀ root, store.refs root version ≠ .held) (idle : store.borrows version = 0) :
      Step needs closeAllowed store {store with gates := setSlot store.gates version .deleting}
  | erase {store} (version : Nat) (fenced : store.gates version = .deleting) :
      Step needs closeAllowed store {store with
        gates := setSlot store.gates version .gone
        physical := setSlot store.physical version false}

private theorem different_pair {root version changedRoot changedVersion : Nat}
    (distinct : ¬ (root = changedRoot ∧ version = changedVersion)) :
    root ≠ changedRoot ∨ version ≠ changedVersion :=
  if same : root = changedRoot then .inr (fun sameVersion => distinct ⟨same, sameVersion⟩) else .inl same

private theorem reference_unchanged {refs : Nat → Nat → Reference} {root version changedRoot changedVersion : Nat}
    {value : Reference} (other : root ≠ changedRoot ∨ version ≠ changedVersion) :
    setReference refs changedRoot changedVersion value root version = refs root version := by
  by_cases sameRoot : root = changedRoot
  · have otherVersion := other.resolve_left (fun unequal => unequal sameRoot)
    subst root
    simp [setReference, setSlot, otherVersion]
  · simp [setReference, setSlot, sameRoot]

private theorem reference_replaced (refs : Nat → Nat → Reference) (root version : Nat) (value : Reference) :
    setReference refs root version value root version = value := by
  simp [setReference, setSlot]

private theorem past_live_of_inactive_update {store : Store} {root changed : Nat} {phase : RootPhase}
    (inactive : phase ≠ .live) (live : setSlot store.roots changed phase root = .live) :
    store.roots root = .live := by
  by_cases same : root = changed
  · exact False.elim (inactive (by simpa [setSlot, same] using live))
  · simpa [setSlot, same] using live

theorem every_step_keeps_dependencies {needs : Dependencies} {closeAllowed : Nat → Prop}
    {before after : Store} (covered : Covered needs before) (step : Step needs closeAllowed before after) :
    Covered needs after := by
  cases step with
  | begin _ _ =>
      exact ⟨fun root version live dep =>
        covered.complete root version (past_live_of_inactive_update (by decide) live) dep,
        covered.referenceGate, covered.borrowGate, covered.bytes⟩
  | acquire registeredRoot registeredVersion _ _ _ admitting =>
      refine ⟨?_, ?_, covered.borrowGate, covered.bytes⟩
      · intro root version live dep
        by_cases aliases : root = registeredRoot ∧ version = registeredVersion
        · obtain ⟨rfl, rfl⟩ := aliases
          exact reference_replaced _ _ _ _
        · change setReference before.refs registeredRoot registeredVersion .held root version = .held
          rw [reference_unchanged (different_pair aliases)]
          exact covered.complete root version live dep
      · intro root version held
        by_cases aliases : root = registeredRoot ∧ version = registeredVersion
        · obtain ⟨_, rfl⟩ := aliases
          exact admitting
        · have unchanged := reference_unchanged (refs := before.refs) (value := .held)
            (different_pair aliases)
          exact covered.referenceGate root version (unchanged ▸ held)
  | admit admitted _ allHeld =>
      refine ⟨?_, covered.referenceGate, covered.borrowGate, covered.bytes⟩
      intro root version live dep
      by_cases same : root = admitted
      · subst root
        exact allHeld version dep
      · exact covered.complete root version (by simpa [setSlot, same] using live) dep
  | close _ _ _ =>
      exact ⟨fun root version live dep =>
        covered.complete root version (past_live_of_inactive_update (by decide) live) dep,
        covered.referenceGate, covered.borrowGate, covered.bytes⟩
  | release releasingRoot releasedVersion closed =>
      refine ⟨?_, ?_, covered.borrowGate, covered.bytes⟩
      · intro root version live dep
        have other : root ≠ releasingRoot := by
          intro same
          subst root
          have incompatible : RootPhase.closed = .live := closed.symm.trans live
          cases incompatible
        change setReference before.refs releasingRoot releasedVersion .closed root version = .held
        rw [reference_unchanged (.inl other)]
        exact covered.complete root version live dep
      · intro root version held
        by_cases aliases : root = releasingRoot ∧ version = releasedVersion
        · obtain ⟨rfl, rfl⟩ := aliases
          change setReference before.refs root version .closed root version = .held at held
          rw [reference_replaced] at held
          cases held
        · have unchanged := reference_unchanged (refs := before.refs) (value := .closed)
            (different_pair aliases)
          exact covered.referenceGate root version (unchanged ▸ held)
  | borrow root taking _ registered =>
      refine ⟨covered.complete, covered.referenceGate, ?_, covered.bytes⟩
      intro version active
      by_cases same : version = taking
      · subst version
        exact covered.referenceGate root taking registered
      · exact covered.borrowGate version (by simpa [setSlot, same] using active)
  | finish finishing _ =>
      refine ⟨covered.complete, covered.referenceGate, ?_, covered.bytes⟩
      intro version active
      by_cases same : version = finishing
      · subst version
        have remaining : 0 < before.borrows finishing - 1 := by simpa [setSlot] using active
        exact covered.borrowGate finishing (by omega)
      · exact covered.borrowGate version (by simpa [setSlot, same] using active)
  | fenceDisposal deleting openGate unreferenced idle =>
      refine ⟨covered.complete, ?_, ?_, ?_⟩
      · intro root version held
        have unrelated : version ≠ deleting := by
          intro same
          subst version
          exact unreferenced root held
        simpa [setSlot, unrelated] using covered.referenceGate root version held
      · intro version active
        have unrelated : version ≠ deleting := by
          intro same
          subst version
          exact (Nat.ne_of_gt active) idle
        simpa [setSlot, unrelated] using covered.borrowGate version active
      · intro version present
        have formerlyPresent : before.gates version ≠ .gone := by
          by_cases same : version = deleting
          · subst version
            rw [openGate]
            decide
          · simpa [setSlot, same] using present
        exact covered.bytes version formerlyPresent
  | erase deleted fenced =>
      have other : ∀ version, before.gates version = .open → version ≠ deleted := by
        intro version openGate same
        subst version
        have incompatible : VersionPhase.deleting = .open := fenced.symm.trans openGate
        cases incompatible
      refine ⟨covered.complete, ?_, ?_, ?_⟩
      · intro root version held
        have prior := covered.referenceGate root version held
        simpa [setSlot, other version prior] using prior
      · intro version active
        have prior := covered.borrowGate version active
        simpa [setSlot, other version prior] using prior
      · intro version present
        have different : version ≠ deleted := by
          intro same
          subst version
          simp [setSlot] at present
        have prior : before.gates version ≠ .gone := by simpa [setSlot, different] using present
        have physical : before.physical version = true := covered.bytes version prior
        simpa [setSlot, different] using physical

inductive Trace (needs : Dependencies) (closeAllowed : Nat → Prop) : Store → Store → Prop
  | same (store : Store) : Trace needs closeAllowed store store
  | next {first before after} : Trace needs closeAllowed first before →
      Step needs closeAllowed before after → Trace needs closeAllowed first after

theorem every_trace_keeps_dependencies {needs : Dependencies} {closeAllowed : Nat → Prop}
    {first last : Store} (covered : Covered needs first) (history : Trace needs closeAllowed first last) :
    Covered needs last := by
  induction history with
  | same => exact covered
  | next _ step prior => exact every_step_keeps_dependencies prior step

theorem live_manifest_has_exact_version {needs : Dependencies} {store : Store}
    (covered : Covered needs store) {root version : Nat}
    (live : store.roots root = .live) (dep : needs root version) :
    store.physical version = true := by
  have registered := covered.complete root version live dep
  have openGate := covered.referenceGate root version registered
  exact covered.bytes version (by rw [openGate]; decide)

theorem retained_borrow_has_exact_version {needs : Dependencies} {store : Store}
    (covered : Covered needs store) {version : Nat} (active : 0 < store.borrows version) :
    store.physical version = true := by
  have openGate := covered.borrowGate version active
  exact covered.bytes version (by rw [openGate]; decide)

theorem released_reference_is_terminal {needs : Dependencies} {closeAllowed : Nat → Prop}
    {before after : Store} (step : Step needs closeAllowed before after)
    (root version : Nat) (closed : before.refs root version = .closed) :
    after.refs root version = .closed := by
  cases step with
  | acquire addedRoot addedVersion _ _ unused _ =>
      by_cases aliases : root = addedRoot ∧ version = addedVersion
      · obtain ⟨rfl, rfl⟩ := aliases
        have priorUnused : before.refs root version = .unused := unused
        have incompatible : Reference.closed = .unused := closed.symm.trans priorUnused
        cases incompatible
      · change setReference before.refs addedRoot addedVersion .held root version = .closed
        rw [reference_unchanged (different_pair aliases)]
        exact closed
  | release otherRoot otherVersion _ =>
      by_cases aliases : root = otherRoot ∧ version = otherVersion
      · obtain ⟨rfl, rfl⟩ := aliases
        exact reference_replaced _ _ _ _
      · change setReference before.refs otherRoot otherVersion .closed root version = .closed
        rw [reference_unchanged (different_pair aliases)]
        exact closed
  | _ => exact closed

theorem released_reference_refuses_arbitrarily_delayed_acquire {needs : Dependencies}
    {closeAllowed : Nat → Prop} {first last : Store} (history : Trace needs closeAllowed first last)
    (root version : Nat) (closed : first.refs root version = .closed) :
    last.refs root version = .closed := by
  induction history with
  | same => exact closed
  | next _ step prior => exact released_reference_is_terminal step root version prior

theorem unshared_unborrowed_version_can_be_erased {needs : Dependencies} {closeAllowed : Nat → Prop}
    {store : Store} (version : Nat) (openGate : store.gates version = .open)
    (unreferenced : ∀ root, store.refs root version ≠ .held) (idle : store.borrows version = 0) :
    ∃ erased, Trace needs closeAllowed store erased ∧ erased.physical version = false ∧
      ∀ other, other ≠ version → erased.physical other = store.physical other := by
  let fenced := {store with gates := setSlot store.gates version .deleting}
  let erased := {fenced with
    gates := setSlot fenced.gates version .gone
    physical := setSlot fenced.physical version false}
  have fence : Step needs closeAllowed store fenced := .fenceDisposal version openGate unreferenced idle
  have removal : Step needs closeAllowed fenced erased := .erase version (by simp [fenced, setSlot])
  exact ⟨erased, .next (.next (.same _) fence) removal, by simp [erased, setSlot],
    by intro other distinct; simp [erased, fenced, setSlot, distinct]⟩

theorem fenced_version_never_readmits {needs : Dependencies} {closeAllowed : Nat → Prop}
    {first last : Store} (history : Trace needs closeAllowed first last)
    (version : Nat) (closed : first.gates version ≠ .open) :
    last.gates version ≠ .open := by
  induction history with
  | same => exact closed
  | next _ effect prior =>
      cases effect with
      | fenceDisposal chosen _ _ _ =>
          by_cases same : version = chosen
          · simp [setSlot, same]
          · simpa [setSlot, same] using prior
      | erase chosen _ =>
          by_cases same : version = chosen
          · simp [setSlot, same]
          · simpa [setSlot, same] using prior
      | _ => exact prior

theorem live_fork_conflicts_with_erasing_its_only_version {needs : Dependencies}
    {store : Store} (covered : Covered needs store) {fork version : Nat}
    (live : store.roots fork = .live) (dep : needs fork version) :
    ¬ store.physical version = false := by
  rw [live_manifest_has_exact_version covered live dep]
  decide

inductive Path (edge : Nat → Nat → Prop) : Nat → Nat → Prop
  | origin (node : Nat) : Path edge node node
  | next {root parent child : Nat} : Path edge root parent → edge parent child → Path edge root child

def transitiveDependencies (edge contains : Nat → Nat → Prop) : Dependencies :=
  fun root version => ∃ node, Path edge root node ∧ contains node version

structure Product where
  catalog : SnapshotAdmission.View
  store : Store

def LogicalRelease (catalog : SnapshotAdmission.View) (root : Nat) : Prop :=
  ∀ start, catalog.custody root ≠ .ready start

structure ProductSound (environment : SnapshotAdmission.Environment)
    (needs : Dependencies) (view : Product) : Prop where
  catalog : SnapshotAdmission.Sound environment view.catalog
  storage : Covered needs view.store
  backed : ∀ root start, view.catalog.custody root = .ready start → view.store.roots root = .live

inductive ProductStep (environment : SnapshotAdmission.Environment)
    (needs : Dependencies) : Product → Product → Prop
  | ordered {view} (catalog : SnapshotAdmission.View)
      (effect : SnapshotAdmission.Step environment view.catalog catalog)
      (existing : ∀ root start, catalog.custody root = .ready start → view.catalog.custody root = .ready start) :
      ProductStep environment needs view {view with catalog := catalog}
  | register {view} (root start : Nat)
      (coveredManifest : view.store.roots root = .live)
      (fresh : view.catalog.custody root = .missing) :
      ProductStep environment needs view {view with
        catalog := {view.catalog with custody := setSlot view.catalog.custody root (.ready start)}}
  | physical {view} (store : Store) (effect : Step needs (LogicalRelease view.catalog) view.store store) :
      ProductStep environment needs view {view with store := store}

private theorem physically_live_while_logical_custody_held {needs : Dependencies}
    {catalog : SnapshotAdmission.View} {before after : Store}
    (effect : Step needs (LogicalRelease catalog) before after)
    {root start : Nat} (logical : catalog.custody root = .ready start) (live : before.roots root = .live) :
    after.roots root = .live := by
  cases effect with
  | begin added fresh =>
      have other : root ≠ added := by
        intro same
        subst root
        have incompatible : RootPhase.fresh = .live := fresh.symm.trans live
        cases incompatible
      simpa [setSlot, other] using live
  | admit adopted _ _ =>
      by_cases same : root = adopted
      · simp [setSlot, same]
      · simpa [setSlot, same] using live
  | close closing _ released =>
      have other : root ≠ closing := by
        intro same
        subst root
        have allowed : LogicalRelease catalog closing := released
        exact allowed start logical
      simpa [setSlot, other] using live
  | _ => exact live

theorem product_steps_preserve_checkpoint_dependencies {environment : SnapshotAdmission.Environment}
    {needs : Dependencies} {before after : Product}
    (sound : ProductSound environment needs before) (step : ProductStep environment needs before after) :
    ProductSound environment needs after := by
  cases step with
  | ordered _ effect existing =>
      exact ⟨SnapshotAdmission.step_preserves_admitted_basis sound.catalog effect, sound.storage,
        fun root start ready => sound.backed root start (existing root start ready)⟩
  | register registered position manifest fresh =>
      refine ⟨SnapshotAdmission.step_preserves_admitted_basis sound.catalog (.register registered position fresh),
        sound.storage, ?_⟩
      intro root start ready
      by_cases same : root = registered
      · exact same.symm ▸ manifest
      · exact sound.backed root start (by simpa [setSlot, same] using ready)
  | physical _ effect =>
      exact ⟨sound.catalog, every_step_keeps_dependencies sound.storage effect,
        fun root start ready => physically_live_while_logical_custody_held effect ready
          (sound.backed root start ready)⟩

inductive ProductTrace (environment : SnapshotAdmission.Environment)
    (needs : Dependencies) : Product → Product → Prop
  | same (view : Product) : ProductTrace environment needs view view
  | next {first before after} : ProductTrace environment needs first before →
      ProductStep environment needs before after → ProductTrace environment needs first after

theorem product_trace_preserves_checkpoint_dependencies {environment : SnapshotAdmission.Environment}
    {needs : Dependencies} {first last : Product}
    (sound : ProductSound environment needs first) (trace : ProductTrace environment needs first last) :
    ProductSound environment needs last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact product_steps_preserve_checkpoint_dependencies prior step

theorem product_projects_to_logical_snapshot_machine {environment : SnapshotAdmission.Environment}
    {needs : Dependencies} {first last : Product} (history : ProductTrace environment needs first last) :
    SnapshotAdmission.Trace environment first.catalog last.catalog := by
  induction history with
  | same => exact .same _
  | next _ step prior =>
      cases step with
      | ordered _ effect _ => exact .next prior effect
      | register root start _ fresh => exact .next prior (.register root start fresh)
      | physical _ _ => exact prior

theorem admitted_snapshot_keeps_every_reachable_version {environment : SnapshotAdmission.Environment}
    {edge contains : Nat → Nat → Prop} {first last : Product}
    (sound : ProductSound environment (transitiveDependencies edge contains) first)
    (trace : ProductTrace environment (transitiveDependencies edge contains) first last)
    {id : Nat} {basis : SnapshotAdmission.Basis} (held : last.catalog.snapshots id = some basis)
    {node version : Nat} (reachable : Path edge basis.root node) (physical : contains node version) :
    last.store.physical version = true := by
  have current := product_trace_preserves_checkpoint_dependencies sound trace
  have protectedRoot := (current.catalog.live id basis held).rootPresent
  exact live_manifest_has_exact_version current.storage (current.backed basis.root basis.start protectedRoot)
    ⟨node, reachable, physical⟩

#print axioms every_step_keeps_dependencies
#print axioms every_trace_keeps_dependencies
#print axioms live_manifest_has_exact_version
#print axioms retained_borrow_has_exact_version
#print axioms released_reference_is_terminal
#print axioms released_reference_refuses_arbitrarily_delayed_acquire
#print axioms unshared_unborrowed_version_can_be_erased
#print axioms fenced_version_never_readmits
#print axioms live_fork_conflicts_with_erasing_its_only_version
#print axioms product_steps_preserve_checkpoint_dependencies
#print axioms product_trace_preserves_checkpoint_dependencies
#print axioms product_projects_to_logical_snapshot_machine
#print axioms admitted_snapshot_keeps_every_reachable_version

end SharedCustody
