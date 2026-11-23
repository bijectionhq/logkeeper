import UnifiedSource
import CheckpointReconstruction
import JournalRotation

set_option warningAsError true

namespace JointCheckpoint

variable {Proof Claim : Type}

structure Protection (Proof Claim : Type) where
  stable : JournalRotation.View
  visible : JournalRotation.View
  tail : JournalRotation.View → Proof → Prop
  borrowed : Proof → Prop
  owes : Claim → Prop
  equivalent : Proof → Claim → Prop
  certified : JournalRotation.View → Claim → Prop
  present : Proof → Prop

def Selectable (state : Protection Proof Claim) (view : JournalRotation.View) : Prop :=
  view = state.stable ∨ view = state.visible

structure Sound (state : Protection Proof Claim) : Prop where
  playback : ∀ view, Selectable state view → ∀ proof, state.tail view proof → state.present proof
  borrows : ∀ proof, state.borrowed proof → state.present proof
  outstanding : ∀ claim, state.owes claim → ∀ view, Selectable state view →
    state.certified view claim ∨ ∃ proof, state.present proof ∧ state.equivalent proof claim

def NoReplayUse (state : Protection Proof Claim) (removed : Proof) : Prop :=
  ∀ view, Selectable state view → ¬ state.tail view removed

def MayRemove (state : Protection Proof Claim) (removed : Proof) : Prop :=
  NoReplayUse state removed ∧ ¬ state.borrowed removed ∧
    ∀ claim, state.owes claim → ∀ view, Selectable state view →
      state.certified view claim ∨ ∃ proof, proof ≠ removed ∧ state.present proof ∧ state.equivalent proof claim

def remove (state : Protection Proof Claim) (removed : Proof) : Protection Proof Claim :=
  {state with present := fun proof => state.present proof ∧ proof ≠ removed}

theorem every_selectable_base_must_release_its_tail_attachment
    {state : Protection Proof Claim} {removed : Proof} (allowed : NoReplayUse state removed)
    (view : JournalRotation.View) (selected : Selectable state view) :
    ¬ state.tail view removed := by
  exact allowed view selected

theorem an_attachment_can_leave_only_when_all_three_uses_remain_covered
    {state : Protection Proof Claim} {removed : Proof}
    (sound : Sound state) (allowed : MayRemove state removed) :
    Sound (remove state removed) := by
  constructor
  · intro view selected proof required
    refine ⟨sound.playback view selected proof required, ?_⟩
    intro same
    subst proof
    exact every_selectable_base_must_release_its_tail_attachment allowed.1 view selected required
  · intro proof borrowed
    refine ⟨sound.borrows proof borrowed, ?_⟩
    intro same
    subst proof
    exact allowed.2.1 borrowed
  · intro claim owed view selected
    rcases allowed.2.2 claim owed view selected with regenerated | surviving
    · exact .inl regenerated
    · obtain ⟨proof, other, present, exactClaim⟩ := surviving
      exact .inr ⟨proof, ⟨present, other⟩, exactClaim⟩

theorem selecting_a_covered_base_preserves_all_evidence
    {state : Protection Proof Claim} {chosen : JournalRotation.View}
    (sound : Sound state) (allowed : Selectable state chosen) :
    Sound {state with stable := chosen, visible := chosen} := by
  constructor
  · intro view selected proof needed
    have same : view = chosen := selected.elim id id
    exact sound.playback view (same.symm ▸ allowed) proof needed
  · exact sound.borrows
  · intro claim owed view selected
    have same : view = chosen := selected.elim id id
    exact sound.outstanding claim owed view (same.symm ▸ allowed)

variable {width : Nat} {Pool Payload Root Ticket : Type}

open CheckpointReconstruction (StreamKey)

structure ControlImage (width : Nat) (Pool Root : Type) where
  scope : StreamKey
  position : Nat
  dataEnd : Nat
  minimumRetained : Nat
  dataCheckpoint : Nat
  authority : Kernel.Authority
  root : Root
  book : UnifiedSource.MoveBook width Pool
  pending : Option (SourceOutcomes.Key width)
  handoff : Option (UnifiedSource.Anchor width Pool)

def summarize (scope : StreamKey) (root : Root) (state : UnifiedSource.State width Pool Payload) :
    ControlImage width Pool Root :=
  ⟨scope, state.position, state.core.stream.history.length, state.core.stream.firstRetained,
    state.core.stream.checkpointEnd, state.core.stream.authority, root, state.core.book,
    state.core.pending, state.core.handoff⟩

structure ClaimAtCut (width : Nat) (Pool : Type) where
  scope : StreamKey
  position : Nat
  decision : SourceOutcomes.Decision width (FundedSeal.Intent Pool)
  participant : SettlementComposition.Participant Pool

def ClaimMatches (statement : ClaimAtCut width Pool) (scope : StreamKey)
    (image : ControlImage width Pool Root) : Prop :=
  statement.scope = scope ∧ scope = image.scope ∧ statement.position = image.position ∧
    ∃ row, SourceOutcomes.lookup image.book statement.decision.key = some row ∧
      row.binding = statement.decision.binding ∧ row.result = some statement.decision.result ∧
      statement.participant ∈ row.waiting

theorem a_reissued_claim_is_from_the_right_stream_and_its_current_cut
    {statement : ClaimAtCut width Pool} {scope : StreamKey} {image : ControlImage width Pool Root}
    (verified : ClaimMatches statement scope image) :
    statement.scope = scope ∧ scope = image.scope ∧ statement.position = image.position := by
  exact ⟨verified.1, verified.2.1, verified.2.2.1⟩

theorem a_joint_cut_reissues_the_exact_current_result_without_its_old_command
    (limits : Kernel.Limits) (rules : UnifiedSource.Rules width Pool Payload Ticket)
    (initial : UnifiedSource.State width Pool Payload) (commands : List (UnifiedSource.Command width Pool Payload Ticket))
    (scope : StreamKey) (root : Root) (image : ControlImage width Pool Root)
    (verified : image = summarize scope root (UnifiedSource.replay limits rules initial commands).1)
    (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (result : SourceOutcomes.Resolution) (participant : SettlementComposition.Participant Pool)
    (found : SourceOutcomes.lookup (UnifiedSource.replay limits rules initial commands).1.core.book key = some row)
    (resolved : row.result = some result) (owed : participant ∈ row.waiting) :
    ClaimMatches (⟨scope, image.position, ⟨key, row.binding, result⟩, participant⟩ : ClaimAtCut width Pool)
      scope image := by
  subst image
  exact ⟨by trivial, rfl, rfl, row, found, rfl, resolved, owed⟩

theorem original_abort_position_is_not_recoverable_from_equal_joint_states
    (limits : Kernel.Limits) (rules : UnifiedSource.Rules width Pool Payload Ticket)
    (initial : UnifiedSource.State width Pool Payload)
    (writer : Kernel.Writer) (key : SourceOutcomes.Key width)
    (row : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool))
    (ready : UnifiedSource.Ready initial.core key row)
    (authorized : initial.core.stream.authority = .active writer) :
    let cancel : UnifiedSource.Command width Pool Payload Ticket := .cancel writer key
    let refused : UnifiedSource.Command width Pool Payload Ticket := .stream (.freeze writer writer.placement)
    let early := UnifiedSource.replay limits rules initial [cancel, refused]
    let late := UnifiedSource.replay limits rules initial [refused, cancel]
    early.1 = late.1 ∧ early.2 = [.accepted, .refused] ∧ late.2 = [.refused, .accepted] := by
  classical
  have canceled (position : Nat) :
      UnifiedSource.decide limits rules initial.core position (.cancel writer key) =
        (UnifiedSource.terminal initial.core key row .canceled, .accepted) := by
    simp only [UnifiedSource.decide, ite_eq_left authorized]
    change (match SourceOutcomes.lookup initial.core.book key with
      | none => (initial.core, UnifiedSource.Reply.refused)
      | some current => if UnifiedSource.Ready initial.core key current
          then (UnifiedSource.terminal initial.core key current .canceled, UnifiedSource.Reply.accepted)
          else (initial.core, UnifiedSource.Reply.refused)) =
            (UnifiedSource.terminal initial.core key row .canceled, UnifiedSource.Reply.accepted)
    simp [ready.2.1, ready]
  simp only [UnifiedSource.replay, canceled, UnifiedSource.ordinary_commands_cannot_freeze_the_source,
    and_self]

def resultBytes (size : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool) → Nat)
    (book : UnifiedSource.MoveBook width Pool) : Nat :=
  (List.ofFn fun slot => ((book.rows slot).map size).getD 0).sum

private theorem bounded_sum (limit : Nat) (sizes : List Nat)
    (bounded : ∀ size ∈ sizes, size ≤ limit) : sizes.sum ≤ sizes.length * limit := by
  induction sizes with
  | nil => simp
  | cons size remaining prior =>
      have each := bounded size (by simp)
      have tail : ∀ part ∈ remaining, part ≤ limit :=
        fun part found => bounded part (by simp [found])
      have smaller := prior tail
      simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem the_result_book_encoding_has_a_per_slot_byte_bound
    (book : UnifiedSource.MoveBook width Pool)
    (size : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool) → Nat)
    (limit : Nat) (each : ∀ slot row, book.rows slot = some row → size row ≤ limit) :
    resultBytes size book ≤ width * limit := by
  let sizes := List.ofFn fun slot => ((book.rows slot).map size).getD 0
  have same : sizes.length = width := List.length_ofFn
  have bound : sizes.sum ≤ sizes.length * limit := by
    apply bounded_sum
    intro bytes member
    obtain ⟨slot, exactSize⟩ := List.mem_ofFn.mp member
    subst bytes
    cases found : book.rows slot with
    | none => simp
    | some row => simpa [found] using each slot row found
  simpa only [resultBytes, same] using bound

theorem two_selectable_result_books_fit_the_reserved_control_budget
    (stable visible : UnifiedSource.MoveBook width Pool)
    (size : SourceOutcomes.Row (FundedSeal.Intent Pool) (SettlementComposition.Participant Pool) → Nat)
    (headerStable headerVisible headerLimit rowLimit : Nat)
    (stableHeader : headerStable ≤ headerLimit) (visibleHeader : headerVisible ≤ headerLimit)
    (stableRows : ∀ slot row, stable.rows slot = some row → size row ≤ rowLimit)
    (visibleRows : ∀ slot row, visible.rows slot = some row → size row ≤ rowLimit) :
    headerStable + resultBytes size stable + (headerVisible + resultBytes size visible) ≤
      2 * (headerLimit + width * rowLimit) := by
  have stableBound := the_result_book_encoding_has_a_per_slot_byte_bound stable size rowLimit stableRows
  have visibleBound := the_result_book_encoding_has_a_per_slot_byte_bound visible size rowLimit visibleRows
  omega

theorem one_result_slot_does_not_bound_uncapped_row_bytes (limit : Nat) :
    ∃ (book : UnifiedSource.MoveBook 1 Unit)
      (size : SourceOutcomes.Row (FundedSeal.Intent Unit) (SettlementComposition.Participant Unit) → Nat),
      limit < resultBytes size book := by
  let intent : FundedSeal.Intent Unit := ⟨1, ⟨0, 1⟩, fun _ => 1⟩
  let book : UnifiedSource.MoveBook 1 Unit :=
    ⟨1, fun _ => some ⟨1, intent, some .canceled, [.pool ()]⟩⟩
  refine ⟨book, fun _ => limit + 1, ?_⟩
  simp [resultBytes, book, List.ofFn_succ]

#print axioms every_selectable_base_must_release_its_tail_attachment
#print axioms an_attachment_can_leave_only_when_all_three_uses_remain_covered
#print axioms selecting_a_covered_base_preserves_all_evidence
#print axioms a_reissued_claim_is_from_the_right_stream_and_its_current_cut
#print axioms a_joint_cut_reissues_the_exact_current_result_without_its_old_command
#print axioms original_abort_position_is_not_recoverable_from_equal_joint_states
#print axioms the_result_book_encoding_has_a_per_slot_byte_bound
#print axioms two_selectable_result_books_fit_the_reserved_control_budget
#print axioms one_result_slot_does_not_bound_uncapped_row_bytes

end JointCheckpoint
