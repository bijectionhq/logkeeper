import CheckpointReconstruction

set_option warningAsError true

namespace SnapshotAdmission

inductive Custody where
  | missing
  | ready (start : Nat)
  | disposing
  | gone

structure Basis where
  root : Nat
  start : Nat
  stop : Nat

structure View where
  head : Nat
  floor : Nat
  root : Nat
  restart : Nat
  placement : Nat
  custody : Nat → Custody
  snapshots : Nat → Option Basis
  issued : Nat

structure Environment where
  capacity : Nat
  canReserve : View → Prop
  drained : View → Nat → Prop

def setSlot {Value : Type} (table : Nat → Value) (id : Nat) (value : Value) :
    Nat → Value :=
  fun item => if item = id then value else table item

def currentBasis (view : View) : Basis :=
  ⟨view.root, view.restart, view.head⟩

def snapshotView (view : View) : View :=
  {view with
    issued := view.issued + 1
    snapshots := setSlot view.snapshots (view.issued + 1) (some (currentBasis view))}

structure Protected (view : View) (basis : Basis) : Prop where
  rootPresent : view.custody basis.root = .ready basis.start
  ordered : basis.start ≤ basis.stop
  committed : basis.stop ≤ view.head
  tailPresent : basis.start < basis.stop → view.floor ≤ basis.start

structure Sound (environment : Environment) (view : View) : Prop where
  headRoot : view.restart ≤ view.head
  floorRoot : view.floor ≤ view.restart
  currentReady : view.custody view.root = .ready view.restart
  retained : view.head - view.floor ≤ environment.capacity
  issued : ∀ id basis, view.snapshots id = some basis → id ≤ view.issued
  live : ∀ id basis, view.snapshots id = some basis → Protected view basis

inductive Step (environment : Environment) : View → View → Prop
  | append {view} (room : view.head + 1 - view.floor ≤ environment.capacity) :
      Step environment view {view with head := view.head + 1}
  | register {view} (root start : Nat) (fresh : view.custody root = .missing) :
      Step environment view {view with custody := setSlot view.custody root (.ready start)}
  | publish {view} (root start : Nat)
      (registered : view.custody root = .ready start)
      (advances : view.restart ≤ start) (committed : start ≤ view.head) :
      Step environment view {view with root := root, restart := start}
  | reserve {view} (room : environment.canReserve view) :
      Step environment view (snapshotView view)
  | release {view} (id : Nat) (safe : environment.drained view id) :
      Step environment view {view with snapshots := setSlot view.snapshots id none}
  | trim {view} (floor : Nat) (advances : view.floor ≤ floor)
      (checkpoint : floor ≤ view.restart)
      (keeps : ∀ id basis, view.snapshots id = some basis → basis.start < basis.stop → floor ≤ basis.start) :
      Step environment view {view with floor := floor}
  | authorizeDisposal {view} (root start : Nat)
      (ready : view.custody root = .ready start) (notCurrent : root ≠ view.root)
      (unheld : ∀ id basis, view.snapshots id = some basis → root ≠ basis.root) :
      Step environment view {view with custody := setSlot view.custody root .disposing}
  | finishDisposal {view} (root : Nat) (authorized : view.custody root = .disposing) :
      Step environment view {view with custody := setSlot view.custody root .gone}
  | install {view} (placement : Nat) (advances : view.placement < placement) :
      Step environment view {view with placement := placement}

theorem current_basis_is_protected {environment : Environment} {view : View}
    (sound : Sound environment view) : Protected view (currentBasis view) :=
  ⟨sound.currentReady, sound.headRoot, Nat.le_refl _, fun _ => sound.floorRoot⟩

private theorem existing_root_rejects_nonready {view : View} {root start : Nat} {status : Custody}
    (ready : view.custody root = .ready start) (statusAt : view.custody root = status)
    (nonready : ∀ start, status ≠ .ready start) : False :=
  nonready start (statusAt.symm.trans ready)

private theorem unchanged_inputs_keep_protection {before after : View} {basis : Basis}
    (prior : Protected before basis) (head : after.head = before.head)
    (floor : after.floor = before.floor) (custody : after.custody = before.custody) :
    Protected after basis :=
  ⟨by simpa only [custody] using prior.rootPresent, prior.ordered,
    by simpa only [head] using prior.committed, by simpa only [floor] using prior.tailPresent⟩

theorem step_preserves_admitted_basis {environment : Environment} {before after : View}
    (sound : Sound environment before) (step : Step environment before after) :
    Sound environment after := by
  cases step with
  | append room =>
      refine ⟨Nat.le_trans sound.headRoot (Nat.le_succ _), sound.floorRoot, sound.currentReady,
        room, sound.issued, ?_⟩
      intro id basis held
      have prior := sound.live id basis held
      exact ⟨prior.rootPresent, prior.ordered, Nat.le_trans prior.committed (Nat.le_succ _), prior.tailPresent⟩
  | register root start fresh =>
      have untouched : ∀ id cut, before.custody id = .ready cut → id ≠ root := by
        intro id cut ready aliases
        subst id
        exact existing_root_rejects_nonready ready fresh (by intro _ impossible; cases impossible)
      refine ⟨sound.headRoot, sound.floorRoot, ?_, sound.retained, sound.issued, ?_⟩
      · simpa [setSlot, untouched _ _ sound.currentReady] using sound.currentReady
      · intro id basis held
        have prior := sound.live id basis held
        exact ⟨by simpa [setSlot, untouched _ _ prior.rootPresent] using prior.rootPresent,
          prior.ordered, prior.committed, prior.tailPresent⟩
  | publish root start registered advances committed =>
      have backed : before.custody root = .ready start := registered
      exact ⟨committed, Nat.le_trans sound.floorRoot advances, backed,
        sound.retained, sound.issued, fun id basis held =>
          unchanged_inputs_keep_protection (sound.live id basis held) rfl rfl rfl⟩
  | reserve _ =>
      have split : ∀ id basis, (snapshotView before).snapshots id = some basis →
          (id = before.issued + 1 ∧ basis = currentBasis before) ∨
            before.snapshots id = some basis := by
        intro id basis installed
        by_cases chosen : id = before.issued + 1
        · exact .inl ⟨chosen, (by simpa [snapshotView, setSlot, chosen] using installed.symm)⟩
        · exact .inr (by simpa [snapshotView, setSlot, chosen] using installed)
      refine ⟨sound.headRoot, sound.floorRoot, sound.currentReady, sound.retained, ?_, ?_⟩
      · intro id basis installed
        rcases split id basis installed with ⟨chosen, _⟩ | prior
        · exact Nat.le_of_eq chosen
        · exact Nat.le_trans (sound.issued id basis prior) (Nat.le_succ _)
      · intro id basis installed
        rcases split id basis installed with ⟨_, rfl⟩ | prior
        · exact unchanged_inputs_keep_protection (current_basis_is_protected sound) rfl rfl rfl
        · exact unchanged_inputs_keep_protection (sound.live id basis prior) rfl rfl rfl
  | release closed _ =>
      have previous : ∀ id basis,
          setSlot before.snapshots closed none id = some basis → before.snapshots id = some basis := by
        intro id basis held
        by_cases discharged : id = closed
        · simp [setSlot, discharged] at held
        · simpa [setSlot, discharged] using held
      exact ⟨sound.headRoot, sound.floorRoot, sound.currentReady, sound.retained,
        fun id basis held => sound.issued id basis (previous id basis held),
        fun id basis held =>
          unchanged_inputs_keep_protection (sound.live id basis (previous id basis held)) rfl rfl rfl⟩
  | trim floor advances checkpoint keeps =>
      have retained : before.head - floor ≤ environment.capacity := by
        have past := sound.retained
        omega
      refine ⟨sound.headRoot, checkpoint, sound.currentReady, retained, sound.issued, ?_⟩
      intro id basis held
      have prior := sound.live id basis held
      have retainedTail : basis.start < basis.stop → floor ≤ basis.start := keeps id basis held
      exact ⟨prior.rootPresent, prior.ordered, prior.committed, retainedTail⟩
  | authorizeDisposal root _ _ notCurrent unheld =>
      refine ⟨sound.headRoot, sound.floorRoot, ?_, sound.retained, sound.issued, ?_⟩
      · simpa [setSlot, Ne.symm notCurrent] using sound.currentReady
      · intro id basis held
        have prior := sound.live id basis held
        have untouched : basis.root ≠ root := Ne.symm (unheld id basis held)
        exact ⟨by simpa [setSlot, untouched] using prior.rootPresent,
          prior.ordered, prior.committed, prior.tailPresent⟩
  | finishDisposal root authorized =>
      have untouched : ∀ id cut, before.custody id = .ready cut → id ≠ root := by
        intro id cut ready aliases
        subst id
        exact existing_root_rejects_nonready ready authorized (by intro _ impossible; cases impossible)
      refine ⟨sound.headRoot, sound.floorRoot, ?_, sound.retained, sound.issued, ?_⟩
      · simpa [setSlot, untouched _ _ sound.currentReady] using sound.currentReady
      · intro id basis held
        have prior := sound.live id basis held
        exact ⟨by simpa [setSlot, untouched _ _ prior.rootPresent] using prior.rootPresent,
          prior.ordered, prior.committed, prior.tailPresent⟩
  | install _ _ =>
      exact ⟨sound.headRoot, sound.floorRoot, sound.currentReady, sound.retained, sound.issued,
        fun id basis held => unchanged_inputs_keep_protection (sound.live id basis held) rfl rfl rfl⟩

inductive Trace (environment : Environment) : View → View → Prop
  | same (view : View) : Trace environment view view
  | next {origin before after} : Trace environment origin before → Step environment before after →
      Trace environment origin after

theorem trace_preserves_admitted_bases {environment : Environment} {first last : View}
    (sound : Sound environment first) (history : Trace environment first last) :
    Sound environment last := by
  induction history with
  | same => exact sound
  | next _ step prior => exact step_preserves_admitted_basis prior step

theorem latest_reservation_is_always_enabled {environment : Environment} {view : View}
    (sound : Sound environment view) (room : environment.canReserve view) :
    ∃ after, Step environment view after ∧
      after.snapshots (view.issued + 1) = some (currentBasis view) ∧
      Protected after (currentBasis view) := by
  refine ⟨snapshotView view, .reserve room, by simp [snapshotView, setSlot], ?_⟩
  exact unchanged_inputs_keep_protection (current_basis_is_protected sound) rfl rfl rfl

theorem held_input_survives_until_its_own_release {environment : Environment} {before after : View}
    (sound : Sound environment before) (step : Step environment before after)
    (id : Nat) (basis : Basis) (admitted : before.snapshots id = some basis) :
    after.snapshots id = some basis ∨ environment.drained before id := by
  cases step with
  | reserve _ =>
      have issued := sound.issued id basis admitted
      have other : id ≠ before.issued + 1 := by omega
      exact .inl (by simpa [snapshotView, setSlot, other] using admitted)
  | release closing drained =>
      by_cases closingThis : id = closing
      · exact .inr (closingThis ▸ drained)
      · exact .inl (by simpa [setSlot, closingThis] using admitted)
  | _ => exact .inl admitted

theorem unrevoked_basis_survives_moves {environment : Environment} {first last : View}
    (sound : Sound environment first) (history : Trace environment first last)
    (id : Nat) (basis : Basis) (admitted : first.snapshots id = some basis)
    (stillRunning : ∀ view, Trace environment first view → ¬ environment.drained view id) :
    last.snapshots id = some basis ∧ Protected last basis := by
  induction history with
  | same => exact ⟨admitted, sound.live id basis admitted⟩
  | next earlier step prior =>
      have held := held_input_survives_until_its_own_release
        (trace_preserves_admitted_bases sound earlier) step id basis prior.1
      have retained := held.resolve_right (stillRunning _ earlier)
      exact ⟨retained, (trace_preserves_admitted_bases sound (.next earlier step)).live id basis retained⟩

theorem disposing_root_cannot_be_readopted {view : View}
    {root start : Nat} (disposing : view.custody root = .disposing) :
    view.custody root ≠ .ready start := by
  intro ready
  exact existing_root_rejects_nonready ready disposing (by intro _ impossible; cases impossible)

theorem held_nonempty_tail_limits_write_head {environment : Environment} {view : View}
    (sound : Sound environment view) {id : Nat} {basis : Basis}
    (admitted : view.snapshots id = some basis) (nonempty : basis.start < basis.stop) :
    view.head ≤ basis.start + environment.capacity := by
  have floor := (sound.live id basis admitted).tailPresent nonempty
  have retained := sound.retained
  omega

theorem published_start_is_monotone {environment : Environment} {first last : View}
    (history : Trace environment first last) : first.restart ≤ last.restart := by
  induction history with
  | same => exact Nat.le_refl _
  | next _ step prior =>
      cases step with
      | publish _ _ _ advances _ => exact Nat.le_trans prior advances
      | _ => exact prior

theorem latest_only_cannot_reserve_overtaken_cut {environment : Environment} {first last : View}
    (history : Trace environment first last) {target : Nat}
    (advanced : target < first.restart) : ¬ last.restart ≤ target :=
  Nat.not_le_of_lt (Nat.lt_of_lt_of_le advanced (published_start_is_monotone history))

theorem nonempty_reservation_creates_a_kernel_hold {environment : Environment} {view : View}
    {limits : Kernel.Limits} {stream : Kernel.State Payload} {writer : Kernel.Writer}
    (sound : Sound environment view) (valid : Kernel.Valid limits stream)
    (room : environment.canReserve view) (active : stream.authority = .active writer)
    (start : view.restart = stream.checkpointEnd) (head : view.head = stream.history.length)
    (nonempty : view.restart < view.head) :
    ∃ admittedView admittedStream, Step environment view admittedView ∧
      Kernel.Trace limits stream admittedStream ∧ Kernel.Valid limits admittedStream ∧
      admittedView.snapshots (view.issued + 1) = some (currentBasis view) ∧
      admittedStream.replays (stream.replayIssued + 1) = .holding view.restart := by
  obtain ⟨admittedView, step, held, _⟩ := latest_reservation_is_always_enabled sound room
  obtain ⟨admittedStream, trace, replay⟩ := Kernel.prepare_and_admit_replay_program (limits := limits)
    view.restart active (start.symm ▸ valid.trimCertified) (head ▸ nonempty)
  exact ⟨admittedView, admittedStream, step, trace, Kernel.every_trace_preserves_bounds valid trace,
    held, replay⟩

theorem root_only_recovery_does_not_need_the_journal {engine : CheckpointReconstruction.Engine Db Payload Root}
    {stream : Kernel.State Payload} {image : CheckpointReconstruction.Image Db Payload Root}
    (certified : CheckpointReconstruction.Certified engine stream image) :
    CheckpointReconstruction.replay engine image.root [] =
      some (CheckpointReconstruction.stateAt engine stream.history image.cut.next) := by
  rw [CheckpointReconstruction.replay, certified.rootMatches, Option.map_some, List.foldl_nil,
    certified.decodedAtCut, CheckpointReconstruction.stateAt, certified.exactPrefix, List.take_take, Nat.min_self]
  rfl

#print axioms current_basis_is_protected
#print axioms step_preserves_admitted_basis
#print axioms trace_preserves_admitted_bases
#print axioms latest_reservation_is_always_enabled
#print axioms held_input_survives_until_its_own_release
#print axioms unrevoked_basis_survives_moves
#print axioms disposing_root_cannot_be_readopted
#print axioms held_nonempty_tail_limits_write_head
#print axioms published_start_is_monotone
#print axioms latest_only_cannot_reserve_overtaken_cut
#print axioms nonempty_reservation_creates_a_kernel_hold
#print axioms root_only_recovery_does_not_need_the_journal

end SnapshotAdmission
