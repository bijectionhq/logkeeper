import ReadIndexProof
import SnapshotAdmission

set_option warningAsError true

namespace ReconfiguredReads

open JournalRefinement

def Joint (old new : List Replica) (votes : Replica → Bool) : Prop :=
  Majority old votes ∧ Majority new votes

def OneSide (old new : List Replica) (votes : Replica → Bool) : Prop :=
  Majority old votes ∨ Majority new votes

def DisjointVotes (fenced responding : Replica → Bool) : Prop :=
  ∀ replica, fenced replica = true → responding replica = false

theorem one_side_read_intersects_joint_write (old new : List Replica)
    (reads writes : Replica → Bool) (readQuorum : OneSide old new reads)
    (writeQuorum : Joint old new writes) :
    ∃ replica, (replica ∈ old ∨ replica ∈ new) ∧ reads replica = true ∧ writes replica = true := by
  rcases readQuorum with fromOld | fromNew
  · obtain ⟨replica, member, read, write⟩ := majorities_overlap old reads writes fromOld writeQuorum.1
    exact ⟨replica, Or.inl member, read, write⟩
  · obtain ⟨replica, member, read, write⟩ := majorities_overlap new reads writes fromNew writeQuorum.2
    exact ⟨replica, Or.inr member, read, write⟩

theorem joint_read_cut_covers_earlier_choice (old new : List Replica)
    (reads held : Replica → Bool) (readQuorum : OneSide old new reads)
    (covered : Joint old new held)
    (required maximum : Nat) (sampled : Replica → Nat)
    (copyAvailable : ∀ replica, held replica = true → reads replica = true → required ≤ sampled replica)
    (tracksMaximum : ∀ replica, reads replica = true → sampled replica ≤ maximum) :
    required ≤ maximum := by
  obtain ⟨replica, _, read, heldHere⟩ :=
    one_side_read_intersects_joint_write old new reads held readQuorum covered
  exact Nat.le_trans (copyAvailable replica heldHere read) (tracksMaximum replica read)

theorem new_majority_fences_successor_side_reads (new : List Replica)
    (fenced reads : Replica → Bool) (newFence : Majority new fenced)
    (refuses : DisjointVotes fenced reads) : ¬ Majority new reads :=
  durable_fence_excludes_stale_majority new fenced reads newFence
    (fun replica _ alreadyFenced => refuses replica alreadyFenced)

theorem new_majority_fences_dual_joint_reads (old new : List Replica)
    (fenced reads : Replica → Bool) (newFence : Majority new fenced)
    (refuses : DisjointVotes fenced reads) : ¬ Joint old new reads := by
  intro canRead
  exact new_majority_fences_successor_side_reads new fenced reads newFence refuses canRead.2

def FencesBoth (old new : List Replica) (fenced : Replica → Bool) : Prop :=
  Majority old fenced ∧ Majority new fenced

theorem both_majorities_fence_one_side_reads (old new : List Replica)
    (fenced reads : Replica → Bool) (closed : FencesBoth old new fenced)
    (refuses : DisjointVotes fenced reads) : ¬ OneSide old new reads := by
  have oldFence : Majority old fenced := by
    exact closed.1
  intro canRead
  rcases canRead with fromOld | fromNew
  · exact durable_fence_excludes_stale_majority old fenced reads oldFence
      (fun replica _ alreadyFenced => refuses replica alreadyFenced) fromOld
  · exact durable_fence_excludes_stale_majority new fenced reads closed.2
      (fun replica _ alreadyFenced => refuses replica alreadyFenced) fromNew

theorem new_majority_can_miss_a_joint_one_side_reader :
    ∃ fenced reads : Nat → Bool,
      Majority [2, 3, 4] fenced ∧ OneSide [1, 2, 3] [2, 3, 4] reads ∧ DisjointVotes fenced reads := by
  refine ⟨fun r => r == 3 || r == 4, fun r => r == 1 || r == 2, ?_, Or.inl ?_, ?_⟩
  · unfold Majority; decide
  · unfold Majority; decide
  · intro replica fenced
    simp at fenced
    rcases fenced with rfl | rfl <;> decide

def SameLineage (original current : ReadIndexProof.Scope) : Prop :=
  original.group = current.group ∧ original.incarnation = current.incarnation ∧
    original.placement = current.placement

abbrev Command := OrderedApplication.Command
abbrev ChoiceTrace := ReadIndexProof.ChoiceTrace
abbrev Invocation := ReadIndexProof.Invocation
abbrev Round := ReadIndexProof.Round

def BindsInvocation (call : Invocation) (round : Round Replica Value) : Prop :=
  round.invocation = call.nonce

structure VerifiedFloor (trace : ChoiceTrace Value) (call : Invocation)
    (round : Round Replica Value) : Prop where
  invocation : BindsInvocation call round
  fresh : call.started ≤ round.opened
  coversOpening : (trace.chosen round.opened).length ≤ round.target.length

theorem stable_round_supplies_verified_floor
    {members : List Replica} {stores : ReadIndexProof.Stores Replica Value}
    {trace : ChoiceTrace Value} {call : Invocation} {round : Round Replica Value}
    (evidence : ReadIndexProof.Evidence members stores call round)
    (keeps : ReadIndexProof.MonotoneWithinScope stores)
    (ready : ReadIndexProof.DurableBasis members stores round.scope round.opened (trace.chosen round.opened)) :
    VerifiedFloor trace call round :=
  ⟨evidence.invocation, (ReadIndexProof.successful_round_follows_invocation evidence).1,
    ReadIndexProof.sampled_maximum_covers_prior_choice evidence keeps (Nat.le_refl _) ready⟩

structure JointObservations (old new : List Replica) (stores : ReadIndexProof.Stores Replica Value)
    (call : Invocation) (round : Round Replica Value) : Prop where
  fresh : call.started ≤ round.opened
  invocation : call.nonce = round.invocation
  reads : OneSide old new round.answered
  accurate : ∀ replica, (replica ∈ old ∨ replica ∈ new) → round.answered replica = true →
    let sample := round.observed replica
    sample.round = round.identity ∧ round.opened ≤ sample.sampled ∧ sample.sampled ≤ call.replied ∧
      sample.scope = round.scope ∧ (stores sample.sampled replica).scope = round.scope ∧
      ReadIndexProof.EligiblePromise (stores sample.sampled replica) round.scope ∧
      sample.held = (stores sample.sampled replica).held
  maximum : ∀ replica, round.answered replica = true → ReadIndexProof.Dominates round replica

theorem joint_round_supplies_verified_floor (old new : List Replica)
    {stores : ReadIndexProof.Stores Replica Value} {trace : ChoiceTrace Value}
    {call : Invocation} {round : Round Replica Value}
    (evidence : JointObservations old new stores call round)
    (keeps : ReadIndexProof.MonotoneWithinScope stores)
    (covered : Replica → Bool) (enough : Joint old new covered)
    (installed : ∀ replica, (replica ∈ old ∨ replica ∈ new) → covered replica = true →
      (stores round.opened replica).scope = round.scope ∧
      trace.chosen round.opened <+: (stores round.opened replica).held) :
    VerifiedFloor trace call round := by
  obtain ⟨replica, member, replied, copied⟩ :=
    one_side_read_intersects_joint_write old new round.answered covered evidence.reads enough
  obtain ⟨scopeAtOpen, prior⟩ := installed replica member copied
  obtain ⟨_, sampledAfterOpen, _, _, sampleScope, _, sampleExact⟩ := evidence.accurate replica member replied
  have stillHeld := keeps replica _ _ sampledAfterOpen (scopeAtOpen.trans sampleScope.symm)
  have sampleCoverage : trace.chosen round.opened <+: (round.observed replica).held :=
    sampleExact.symm ▸ prior.trans stillHeld
  exact ⟨evidence.invocation.symm, evidence.fresh,
    Nat.le_trans sampleCoverage.length_le (evidence.maximum replica replied)⟩

def ReachesFloor (floor : Nat) (certified : List Value) : Prop :=
  floor ≤ certified.length

structure Reservation
    (trace : ChoiceTrace (Command Payload)) (call : Invocation)
    (round : Round Replica (Command Payload)) (current : ReadIndexProof.Scope)
    (limits : Kernel.Limits) (initial : Kernel.State Payload) (writer : Kernel.Writer)
    (instant : Nat) (snapshot : List (Command Payload)) (view : SnapshotAdmission.View) : Prop where
  lineage : SameLineage round.scope current
  afterRound : round.opened ≤ instant
  beforeReply : instant ≤ call.replied
  afterObservations : ∀ replica, round.answered replica = true → (round.observed replica).sampled ≤ instant
  coversObserved : ReachesFloor round.target.length snapshot
  appliedChoice : snapshot <+: trace.chosen instant
  materialized : view.head = (OrderedApplication.replay limits initial snapshot).1.history.length
  authorized : (OrderedApplication.replay limits initial snapshot).1.authority = .active writer

theorem reservation_covers_invocation_choice
    {trace : ChoiceTrace (Command Payload)} {call : Invocation}
    {round : Round Replica (Command Payload)} {current : ReadIndexProof.Scope}
    {limits : Kernel.Limits} {initial : Kernel.State Payload} {writer : Kernel.Writer}
    {instant : Nat} {snapshot : List (Command Payload)} {view : SnapshotAdmission.View}
    (floor : VerifiedFloor trace call round)
    (reserved : Reservation trace call round current limits initial writer instant snapshot view) :
      (trace.chosen round.opened).length ≤ round.target.length ∧
      round.target.length ≤ snapshot.length ∧ snapshot <+: trace.chosen instant := by
  have covers : round.target.length ≤ snapshot.length := by
    exact reserved.coversObserved
  exact ⟨floor.coversOpening, covers, reserved.appliedChoice⟩

theorem reserve_exact_applied_cut_after_reconfiguration
    {trace : ChoiceTrace (Command Payload)} {call : Invocation}
    {round : Round Replica (Command Payload)} {current : ReadIndexProof.Scope}
    {limits : Kernel.Limits} {initial : Kernel.State Payload} {writer : Kernel.Writer}
    {instant : Nat} {snapshot : List (Command Payload)} {view : SnapshotAdmission.View}
    {environment : SnapshotAdmission.Environment}
    (floor : VerifiedFloor trace call round) (unit : ReadIndexProof.UnitChoices trace)
    (reserved : Reservation trace call round current limits initial writer instant snapshot view)
    (sound : SnapshotAdmission.Sound environment view) (room : environment.canReserve view) :
    ∃ after point,
      SnapshotAdmission.Step environment view after ∧
      after.snapshots (view.issued + 1) = some (SnapshotAdmission.currentBasis view) ∧
      SnapshotAdmission.Protected after (SnapshotAdmission.currentBasis view) ∧
      round.invocation = call.nonce ∧ SameLineage round.scope current ∧
      call.started ≤ point ∧ point ≤ instant ∧ instant ≤ call.replied ∧ trace.chosen point = snapshot ∧
      Kernel.barrier (OrderedApplication.replay limits initial (trace.chosen point)).1 writer =
        some (SnapshotAdmission.currentBasis view).stop := by
  obtain ⟨after, acquired, held, safe⟩ :=
    SnapshotAdmission.latest_reservation_is_always_enabled sound room
  obtain ⟨opening, covers, applied⟩ := reservation_covers_invocation_choice floor reserved
  obtain ⟨point, inside, beforeReserve, exactLength⟩ :=
    ReadIndexProof.any_intermediate_length_occurs trace unit reserved.afterRound
      (Nat.le_trans opening covers) applied.length_le
  have exactState := ReadIndexProof.matching_prefix_is_exact_at_cut beforeReserve exactLength applied
  have sameInvocation : round.invocation = call.nonce := by
    exact floor.invocation
  exact ⟨after, point, acquired, held, safe, sameInvocation, reserved.lineage,
    Nat.le_trans floor.fresh inside, beforeReserve, reserved.beforeReply, exactState,
    by simp [exactState, Kernel.barrier,
      reserved.authorized, SnapshotAdmission.currentBasis, reserved.materialized]⟩

theorem delivered_reservation_keeps_its_original_cut
    {environment : SnapshotAdmission.Environment} {reserved now : SnapshotAdmission.View}
    (sound : SnapshotAdmission.Sound environment reserved)
    (trace : SnapshotAdmission.Trace environment reserved now)
    (id : Nat) (basis : SnapshotAdmission.Basis) (held : reserved.snapshots id = some basis)
    (live : ∀ view, SnapshotAdmission.Trace environment reserved view → ¬ environment.drained view id) :
    now.snapshots id = some basis ∧ SnapshotAdmission.Protected now basis :=
  SnapshotAdmission.unrevoked_basis_survives_moves sound trace id basis held live

#print axioms one_side_read_intersects_joint_write
#print axioms joint_read_cut_covers_earlier_choice
#print axioms new_majority_fences_successor_side_reads
#print axioms new_majority_fences_dual_joint_reads
#print axioms both_majorities_fence_one_side_reads
#print axioms new_majority_can_miss_a_joint_one_side_reader
#print axioms stable_round_supplies_verified_floor
#print axioms joint_round_supplies_verified_floor
#print axioms reservation_covers_invocation_choice
#print axioms reserve_exact_applied_cut_after_reconfiguration
#print axioms delivered_reservation_keeps_its_original_cut

end ReconfiguredReads
