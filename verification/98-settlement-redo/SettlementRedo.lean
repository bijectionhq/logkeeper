import JournalRotation
import PoolState

set_option warningAsError true

namespace SettlementRedo

open ChannelLifecycle (Key)
open PoolState (Image Row Rules)

variable {Ticket : Type}

structure Refund where
  key : Key
  serial : Nat

inductive Command where
  | refund (original : Refund)
  | occupy (bytes : Nat)

def Matches (original : Refund) (row : Row Ticket) : Prop :=
  row.key = original.key ∧ row.serial = original.serial

theorem a_refund_names_the_exact_physical_serial (original : Refund) (row : Row Ticket)
    (matching : Matches original row) : row.serial = original.serial := by
  exact matching.2

def Ready (pool : Image Ticket) (original : Refund) (row : Row Ticket) : Prop :=
  Matches original row ∧ CopyFence.Closed pool.gate row.key ∧ row.provider.erased = true

noncomputable def readyRow (pool : Image Ticket) (original : Refund) (row : Row Ticket) : Bool := by
  classical
  exact if Ready pool original row then true else false

private theorem readyRow_exact (pool : Image Ticket) (original : Refund) (row : Row Ticket) :
    readyRow pool original row = true ↔ Ready pool original row := by
  classical
  simp [readyRow]

noncomputable def decide (rules : Rules Ticket) (pool : Image Ticket) :
    Command → Option (Image Ticket)
  | .refund original =>
      if pool.rows.any (readyRow pool original) then
        some {pool with rows := pool.rows.eraseP (readyRow pool original)}
      else none
  | .occupy bytes =>
      if bytes + PoolState.charges rules pool.rows ≤ rules.limit then
        some {pool with ordinary := bytes}
      else none

noncomputable def replay (rules : Rules Ticket) (pool : Image Ticket) (journal : List Command) :
    Option (Image Ticket) :=
  journal.foldlM (decide rules) pool

section

variable [DecidableEq Ticket]

theorem any_refund_frame_returns_the_exact_closed_absent_row
    (rules : Rules Ticket) (pool after : Image Ticket) (original : Refund)
    (accepted : decide rules pool (.refund original) = some after) :
    ∃ row ∈ pool.rows, row.key = original.key ∧ row.serial = original.serial ∧
      CopyFence.Closed pool.gate row.key ∧ row.provider.erased = true ∧
      PoolState.Step rules pool after := by
  simp only [decide] at accepted
  split at accepted
  · next admitted =>
    obtain ⟨candidate, member, canReturn⟩ := List.any_eq_true.mp admitted
    obtain ⟨row, earlier, later, _, credited, rows, erasedRows⟩ := List.exists_of_eraseP member canReturn
    obtain ⟨corresponds, closed, erased⟩ := (readyRow_exact pool original row).mp credited
    have refunded : PoolState.Step rules pool {pool with rows := earlier ++ later} :=
      .refund earlier later rows closed erased
    cases accepted
    refine ⟨row, by simp [rows], corresponds.1, a_refund_names_the_exact_physical_serial original row corresponds,
      closed, erased, ?_⟩
    simpa only [erasedRows] using refunded
  · cases accepted

private theorem every_frame_projects_to_the_pool
    (rules : Rules Ticket) (before after : Image Ticket) (command : Command)
    (accepted : decide rules before command = some after) : PoolState.Step rules before after := by
  cases command with
  | refund original =>
      obtain ⟨_, _, _, _, _, _, event⟩ :=
        any_refund_frame_returns_the_exact_closed_absent_row rules before after original accepted
      exact event
  | occupy bytes =>
      simp only [decide] at accepted
      split at accepted
      · next fits =>
        cases accepted
        exact .ordinary bytes fits
      · cases accepted

theorem every_decoded_history_refines_the_pool
    (rules : Rules Ticket) (before after : Image Ticket) (commands : List Command)
    (accepted : replay rules before commands = some after) : PoolState.Trace rules before after := by
  have appendStep {first next last : Image Ticket} (step : PoolState.Step rules first next)
      (tail : PoolState.Trace rules next last) : PoolState.Trace rules first last := by
    induction tail with
    | same => exact .next (.same _) step
    | next _ event prior => exact .next prior event
  induction commands generalizing before with
  | nil =>
      simp [replay] at accepted
      exact accepted ▸ .same _
  | cons command rest prior =>
      simp only [replay, List.foldlM_cons] at accepted
      cases applied : decide rules before command with
      | none => simp [applied] at accepted
      | some next =>
        exact appendStep (every_frame_projects_to_the_pool rules before next command applied)
          (prior next (by simpa [replay, applied] using accepted))

omit [DecidableEq Ticket] in
theorem a_checkpoint_and_its_suffix_replay_in_order
    (rules : Rules Ticket) (start : Image Ticket) (prefixCommands suffix : List Command) :
    replay rules start (prefixCommands ++ suffix) =
      (replay rules start prefixCommands).bind (fun atCut => replay rules atCut suffix) := by
  exact List.foldlM_append

theorem every_legal_crash_root_recovers_the_refunded_and_reused_budget
    (rules : Rules Ticket) (first last : JournalRotation.State Command) (view : JournalRotation.View)
    (origin applied : Image Ticket) (safeMedia : JournalRotation.Safe first)
    (tracked : JournalRotation.TracksNamespace first) (history : JournalRotation.Trace first last)
    (chosen : replay rules origin last.history = some applied) (safePool : PoolState.Sound rules origin)
    (selected : last.namespaceChoices view) :
    ∃ base suffix atCut,
      last.media (.base view.generation) = some base ∧
      (∀ offset command, suffix[offset]? = some command →
        last.media (.tail (view.cut + offset)) = some [command]) ∧
      replay rules origin base = some atCut ∧ replay rules atCut suffix = some applied ∧
      PoolState.Sound rules applied := by
  obtain ⟨safe, exactNamespace⟩ := JournalRotation.every_trace_preserves_safety safeMedia tracked history
  obtain ⟨base, suffix, stored, same, frames⟩ :=
    JournalRotation.recovery_paths_cover_the_same_history safe exactNamespace selected
  have fits := (PoolState.all_local_histories_keep_the_exact_allocator_and_capacity safePool
    (every_decoded_history_refines_the_pool rules origin applied last.history chosen)).1
  rw [← same, a_checkpoint_and_its_suffix_replay_in_order] at chosen
  cases prefixResult : replay rules origin base with
  | none => simp [prefixResult] at chosen
  | some atCut => exact ⟨base, suffix, atCut, stored, frames, prefixResult, by simpa [prefixResult] using chosen, fits⟩

end

structure State (Ticket : Type) where
  journal : JournalRotation.State Command
  pool : Image Ticket

inductive Step (rules : Rules Ticket) : State Ticket → State Ticket → Prop
  | commit {before : State Ticket} {next : Image Ticket} (command : Command)
      (vacant : before.journal.media (.tail before.journal.history.length) = none)
      (applied : decide rules before.pool command = some next) :
      Step rules before ⟨JournalRotation.appendRecord before.journal command, next⟩
  | maintain {before : State Ticket} {next : JournalRotation.State Command}
      (change : JournalRotation.Step before.journal next)
      (keepsHistory : next.history = before.journal.history) :
      Step rules before {before with journal := next}

inductive Trace (rules : Rules Ticket) : State Ticket → State Ticket → Prop
  | same (state : State Ticket) : Trace rules state state
  | next {first before after : State Ticket} :
      Trace rules first before → Step rules before after → Trace rules first after

structure Sound (rules : Rules Ticket) (origin : Image Ticket) (state : State Ticket) : Prop where
  media : JournalRotation.Safe state.journal
  selectors : JournalRotation.TracksNamespace state.journal
  applied : replay rules origin state.journal.history = some state.pool

private theorem every_step_preserves_chosen_pool_and_media (rules : Rules Ticket) (origin : Image Ticket)
    {before after : State Ticket} (sound : Sound rules origin before)
    (event : Step rules before after) : Sound rules origin after := by
  have preserve (next : JournalRotation.State Command)
      (step : JournalRotation.Step before.journal next) :
      JournalRotation.Safe next ∧ JournalRotation.TracksNamespace next :=
    ⟨JournalRotation.step_preserves_safety sound.media sound.selectors step,
      JournalRotation.step_tracks_all_crash_choices sound.selectors step⟩
  cases event with
  | commit command vacant applied =>
    have media := preserve _ (.append command vacant)
    refine ⟨media.1, media.2, ?_⟩
    change replay rules origin (before.journal.history ++ [command]) = _
    rw [a_checkpoint_and_its_suffix_replay_in_order, sound.applied]
    simpa [replay] using applied
  | maintain change keepsHistory =>
    have media := preserve _ change
    exact ⟨media.1, media.2, keepsHistory.symm ▸ sound.applied⟩

theorem arbitrary_ordered_refund_and_reuse_traces_remain_recoverable
    (rules : Rules Ticket) (origin : Image Ticket) (state : State Ticket)
    (events : Trace rules ⟨JournalRotation.initial, origin⟩ state) :
    Sound rules origin state := by
  induction events with
  | same => exact ⟨JournalRotation.initial_safe, JournalRotation.initial_tracks_namespace, rfl⟩
  | next _ event prior => exact every_step_preserves_chosen_pool_and_media rules origin prior event

theorem every_crash_choice_of_the_composed_machine_recovers_the_current_budget
    [DecidableEq Ticket] (rules : Rules Ticket) (origin : Image Ticket) (state : State Ticket)
    (events : Trace rules ⟨JournalRotation.initial, origin⟩ state) (safePool : PoolState.Sound rules origin)
    (view : JournalRotation.View) (selected : state.journal.namespaceChoices view) :
    ∃ base suffix atCut,
      state.journal.media (.base view.generation) = some base ∧
      (∀ offset command, suffix[offset]? = some command →
        state.journal.media (.tail (view.cut + offset)) = some [command]) ∧
      replay rules origin base = some atCut ∧ replay rules atCut suffix = some state.pool ∧
      PoolState.Sound rules state.pool := by
  let sound := arbitrary_ordered_refund_and_reuse_traces_remain_recoverable rules origin state events
  exact every_legal_crash_root_recovers_the_refunded_and_reused_budget rules state.journal state.journal
    view origin state.pool sound.media sound.selectors (.same _) sound.applied safePool selected

theorem at_capacity_the_original_refund_must_precede_a_dependent_debit
    (rules : Rules Ticket) (pool : Image Ticket) (row : Row Ticket) (original : Refund)
    (rows : pool.rows = [row]) (ready : Ready pool original row)
    (full : PoolState.used rules pool = rules.limit) :
    let refill := Command.occupy (pool.ordinary + rules.cost row.binding)
    replay rules pool [refill] = none ∧
    ∃ after, replay rules pool [.refund original, refill] = some after ∧
      after.rows = [] ∧ PoolState.used rules after = rules.limit := by
  intro refill
  have canReturn := (readyRow_exact pool original row).mpr ready
  have originalFit : pool.ordinary + rules.cost row.binding = rules.limit := by
    simpa [PoolState.used, PoolState.charges, rows] using full
  have positive := rules.positive row.binding
  have beforeRefuses : ¬ (pool.ordinary + rules.cost row.binding) + PoolState.charges rules pool.rows ≤
      rules.limit := by
    simp [PoolState.charges, rows]
    omega
  refine ⟨?_, ?_⟩
  · simp [replay, refill, decide, beforeRefuses]
  · let after : Image Ticket := {pool with rows := [], ordinary := pool.ordinary + rules.cost row.binding}
    refine ⟨after, ?_, rfl, ?_⟩
    · simp [replay, refill, decide, rows, canReturn, after, PoolState.charges, originalFit]
    · simpa [after, PoolState.used, PoolState.charges] using originalFit

theorem the_composed_refund_and_refill_program_starts_at_full_capacity
    (rules : Rules Ticket) (pool : Image Ticket) (row : Row Ticket) (original : Refund)
    (rows : pool.rows = [row]) (ready : Ready pool original row)
    (full : PoolState.used rules pool = rules.limit) :
    ∃ after, Trace rules ⟨JournalRotation.initial, pool⟩ after ∧
      after.journal.history = [.refund original, .occupy (pool.ordinary + rules.cost row.binding)] ∧
      after.pool.rows = [] ∧ PoolState.used rules after.pool = rules.limit := by
  let first : State Ticket := ⟨JournalRotation.initial, pool⟩
  let refund := Command.refund original
  let refill := Command.occupy (pool.ordinary + rules.cost row.binding)
  obtain ⟨result, applyBoth, cleared, saturated⟩ :=
    (at_capacity_the_original_refund_must_precede_a_dependent_debit rules pool row original rows ready full).2
  change replay rules pool ([refund] ++ [refill]) = some result at applyBoth
  rw [a_checkpoint_and_its_suffix_replay_in_order rules pool [refund] [refill]] at applyBoth
  cases appliedRefund : decide rules pool refund with
  | none => simp [replay, appliedRefund] at applyBoth
  | some middle =>
    have appliedRefill : decide rules middle refill = some result := by
      simpa [replay, appliedRefund] using applyBoth
    let next : State Ticket := ⟨JournalRotation.appendRecord first.journal refund, middle⟩
    have refundStep : Step rules first next := .commit refund (by
      simp [first, JournalRotation.initial, JournalRotation.update]) appliedRefund
    let after : State Ticket := ⟨JournalRotation.appendRecord next.journal refill, result⟩
    have refillStep : Step rules next after := .commit refill (by
      simp [next, first, JournalRotation.appendRecord, JournalRotation.initial, JournalRotation.update]) appliedRefill
    exact ⟨after, .next (.next (.same _) refundStep) refillStep, rfl, cleared, saturated⟩

theorem predecessor_coverage_blocks_reusing_the_redo_extent
    (journal : JournalRotation.State Command) (position : Nat) (needed : journal.stable.cut ≤ position) :
    ¬ JournalRotation.Reclaimable journal (.tail position) := by
  intro allowed
  exact (JournalRotation.protected_extent_is_not_reclaimable allowed).1 needed

theorem overlapping_redo_and_alternate_image_need_their_combined_reserve
    (workspace redoBytes imageBytes : Nat) (redoPositive : 0 < redoBytes)
    (onlyImageFits : workspace = imageBytes) :
    ¬ redoBytes + imageBytes ≤ workspace := by
  omega

#print axioms a_refund_names_the_exact_physical_serial
#print axioms any_refund_frame_returns_the_exact_closed_absent_row
#print axioms every_decoded_history_refines_the_pool
#print axioms a_checkpoint_and_its_suffix_replay_in_order
#print axioms every_legal_crash_root_recovers_the_refunded_and_reused_budget
#print axioms arbitrary_ordered_refund_and_reuse_traces_remain_recoverable
#print axioms every_crash_choice_of_the_composed_machine_recovers_the_current_budget
#print axioms at_capacity_the_original_refund_must_precede_a_dependent_debit
#print axioms the_composed_refund_and_refill_program_starts_at_full_capacity
#print axioms predecessor_coverage_blocks_reusing_the_redo_extent
#print axioms overlapping_redo_and_alternate_image_need_their_combined_reserve

end SettlementRedo
