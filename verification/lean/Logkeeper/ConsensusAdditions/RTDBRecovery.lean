import Logkeeper.ConsensusAdditions.JournalContract

set_option warningAsError true

namespace Logkeeper.ConsensusAdditions.RTDBRecovery

open JournalContract (Entry Recovery)

/-- An RTDB checkpoint can stand for a trimmed recovery entry only when its
epoch was computed at the checkpoint's covered cut. -/
structure Checkpoint where
  through : Nat
  recoveryEpoch : Nat
  deriving DecidableEq, Repr

inductive Observed where
  | record (entry : Entry)
  | checkpoint (checkpoint : Checkpoint)
  deriving DecidableEq, Repr

def Observed.epoch : Observed → Nat
  | .record (.recovery recovery _) => recovery.fence.epoch
  | .checkpoint stamped => stamped.recoveryEpoch
  | .record (.data ..) => 0

def learn (before : Nat) (suffix : List Observed) : Nat :=
  suffix.foldl (fun epoch record => max epoch record.epoch) before

def capture (base : Checkpoint) (suffix : List Observed) (count : Nat) : Checkpoint :=
  ⟨base.through + count, learn base.recoveryEpoch (suffix.take count)⟩

private theorem learn_ge (seen : Nat) (suffix : List Observed) :
    seen ≤ learn seen suffix := by
  induction suffix generalizing seen with
  | nil => exact Nat.le_refl _
  | cons record rest prior =>
    exact Nat.le_trans (Nat.le_max_left _ _) (prior (max seen record.epoch))

private theorem member_le_learn (seen : Nat) {record : Observed} {suffix : List Observed}
    (member : record ∈ suffix) : record.epoch ≤ learn seen suffix := by
  induction suffix generalizing seen with
  | nil => simp at member
  | cons first rest prior =>
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_trans (Nat.le_max_right _ _) (learn_ge _ _)
    · exact prior (max seen first.epoch) later

/-- Study 110 binds the selected base and chosen suffix to the publication.
Here cutting the same suffix also determines the epoch in the published base. -/
theorem checkpoint_stamps_its_cut (base : Checkpoint) (before after : List Observed) :
    capture base (before ++ after) before.length =
      ⟨base.through + before.length, learn base.recoveryEpoch before⟩ := by
  simp [capture]

theorem checkpoint_and_suffix_preserve_seen_epoch (base : Checkpoint)
    (before after : List Observed) :
    learn (capture base (before ++ after) before.length).recoveryEpoch after =
      learn base.recoveryEpoch (before ++ after) := by
  rw [checkpoint_stamps_its_cut]
  simp [learn, List.foldl_append]

structure Cursor where
  head : Nat
  floor : Nat
  seen : Nat
  deriving DecidableEq, Repr

structure View where
  head : Nat
  floor : Nat
  /-- A failed recheck includes changed authenticated tail bytes. -/
  tailMatches : Bool
  /-- Exact typed suffix selected from the same applied history. -/
  suffix : List Observed
  deriving DecidableEq, Repr

def freshEvidence (seen : Nat) : Observed → Bool
  | .record (.recovery ..) => true
  | .checkpoint checkpoint => seen < checkpoint.recoveryEpoch
  | .record (.data ..) => false

def mayResume (cursor : Cursor) (view : View) : Bool :=
  decide (cursor.head ≤ view.head ∧ view.floor ≤ cursor.floor) &&
    view.tailMatches && !view.suffix.any (freshEvidence cursor.seen)

/-- Coverage of a published recovery is a property of the view and its
selected basis. A recovery already behind the cursor needs a changed tail
(or a floor change or checkpoint witness). That tail implication is an
assumption on authenticated RTDB writer epochs and the selected lineage. -/
inductive Covers (cursor : Cursor) (view : View) (recovery : Nat) : Prop
  | shortened : view.head < cursor.head → Covers cursor view recovery
  | movedFloor : cursor.floor < view.floor → Covers cursor view recovery
  | changedTail : view.tailMatches = false → Covers cursor view recovery
  | typed (record : Recovery) (marker : Option Nat) :
      record.fence.epoch = recovery →
      .record (.recovery record marker) ∈ view.suffix → Covers cursor view recovery
  | certified (checkpoint : Checkpoint) : recovery ≤ checkpoint.recoveryEpoch →
      .checkpoint checkpoint ∈ view.suffix → Covers cursor view recovery

theorem follower_rebuilds_across_unseen_recovery (cursor : Cursor) (view : View)
    (epoch : Nat) (unseen : cursor.seen < epoch) (coverage : Covers cursor view epoch) :
    mayResume cursor view = false := by
  have blocks {record : Observed} (member : record ∈ view.suffix)
      (witness : freshEvidence cursor.seen record = true) :
      view.suffix.any (freshEvidence cursor.seen) = true :=
    List.any_eq_true.mpr ⟨record, member, witness⟩
  cases coverage with
  | shortened shorter => simp [mayResume, Nat.not_le_of_gt shorter]
  | movedFloor moved => simp [mayResume, Nat.not_le_of_gt moved]
  | changedTail changed => simp [mayResume, changed]
  | typed _ _ _ member => simp [mayResume, blocks member rfl]
  | certified checkpoint includes member =>
    have fresh : freshEvidence cursor.seen (.checkpoint checkpoint) = true :=
      decide_eq_true (Nat.lt_of_lt_of_le unseen includes)
    simp [mayResume, blocks member fresh]

/-- Rebuilding replaces the old replay state. A fresh base is the selected
checkpoint of study 110, or the empty genesis basis. -/
def rebuild (view : View) (base : Checkpoint) : Cursor :=
  ⟨view.head, view.floor, learn base.recoveryEpoch view.suffix⟩

theorem rebuild_installs_recovery_evidence (view : View) (base : Checkpoint) (epoch : Nat)
    (witness : epoch ≤ base.recoveryEpoch ∨
      ∃ record ∈ view.suffix, epoch ≤ Observed.epoch record) :
    epoch ≤ (rebuild view base).seen := by
  rcases witness with included | ⟨record, retained, includes⟩
  · exact Nat.le_trans included (learn_ge _ _)
  · exact Nat.le_trans includes (member_le_learn _ retained)

/-- Auto-resume may use an acknowledged fence to start a new writer only
after fresh replay covers that fence. No writer permit follows a failed
rebuild or a hold-writes configuration. -/
def writerMayResume (holdWrites : Bool) (fenceEpoch : Nat) (rebuilt : Option Cursor) : Bool :=
  !holdWrites && rebuilt.any (fun cursor => fenceEpoch ≤ cursor.seen)

theorem auto_resume_requires_seen_epoch (holdWrites : Bool) (epoch : Nat)
    (rebuilt : Option Cursor) (allowed : writerMayResume holdWrites epoch rebuilt = true) :
    holdWrites = false ∧ ∃ cursor, rebuilt = some cursor ∧ epoch ≤ cursor.seen := by
  cases rebuilt with
  | none => simp [writerMayResume] at allowed
  | some cursor =>
    have admitted : holdWrites = false ∧ epoch ≤ cursor.seen := by
      simpa [writerMayResume] using allowed
    exact ⟨admitted.1, cursor, rfl, admitted.2⟩

/-! ## Resuming over the journal contract

The follower's view below comes from the contract's state, so coverage is a
consequence, not a premise. A recovery only cuts the history and raises the
epoch, and every later entry carries an epoch at least as high, so the
record at the cursor changes for good once a recovery cuts below it. -/

open JournalContract (State Command Inv step_inv)

def run (state : State) (commands : List Command) : State :=
  commands.foldl (fun state command => (JournalContract.apply state command).1) state

/-- How one step changes the history and the epoch. -/
inductive Shape (before after : State) : Prop
  | same : after.entries = before.entries → before.epoch ≤ after.epoch → Shape before after
  | extend (entry : Entry) : after.entries = before.entries ++ [entry] →
      entry.epoch = before.epoch → after.epoch = before.epoch → Shape before after
  | cut (keep : Nat) : after.entries = before.entries.take keep →
      after.epoch = before.epoch + 1 → Shape before after

theorem step_shape {state : State} (inv : Inv state) (command : Command) :
    Shape state (JournalContract.apply state command).1 := by
  cases command with
  | «seal» writer =>
    simp only [JournalContract.apply]
    split
    · exact .same rfl (Nat.le_refl _)
    · split
      · rename_i advances
        exact .same rfl (Nat.le_of_lt advances)
      · split <;> exact .same rfl (Nat.le_refl _)
  | append writer lsn payload =>
    simp only [JournalContract.apply]
    split
    · exact .same rfl (Nat.le_refl _)
    · rename_i owns
      have owned : state.owns writer := by simpa using owns
      split
      · exact .same rfl (Nat.le_refl _)
      · split
        · exact .same rfl (Nat.le_refl _)
        · split
          · exact .extend _ rfl (inv.writer writer owned.2) rfl
          · exact .same rfl (Nat.le_refl _)
  | trim writer through =>
    simp only [JournalContract.apply]
    split <;> exact .same rfl (Nat.le_refl _)
  | recover survivor offloaded time =>
    simp only [JournalContract.apply]
    split
    · exact .cut _ rfl rfl
    · exact .same rfl (Nat.le_refl _)
  | acknowledge fence marker =>
    simp only [JournalContract.apply]
    split
    · rename_i record standing
      split
      · exact .extend _ rfl (inv.pending record standing) rfl
      · exact .same rfl (Nat.le_refl _)
    · split <;> first | exact .same rfl (Nat.le_refl _) | (split <;> exact .same rfl (Nat.le_refl _))
  | head => exact .same rfl (Nat.le_refl _)

theorem run_inv {state : State} (inv : Inv state) (commands : List Command) :
    Inv (run state commands) := by
  induction commands generalizing state with
  | nil => exact inv
  | cons command rest prior => exact prior (step_inv inv command)

/-- The follower's applied prefix still stands, or the record at the cursor
changed for good. -/
def Kept (before : State) (cursor : Nat) (now : State) : Prop :=
  now.entries.take cursor = before.entries.take cursor ∨
    ∃ old, before.entries[cursor - 1]? = some old ∧ old.epoch < now.epoch ∧
      ∀ entry, now.entries[cursor - 1]? = some entry → old.epoch < entry.epoch

private theorem kept_step {before now : State} {cursor : Nat} (inv : Inv now)
    (positive : 0 < cursor) (within : cursor ≤ before.entries.length)
    (kept : Kept before cursor now) (command : Command) :
    Kept before cursor (JournalContract.apply now command).1 := by
  have index : cursor - 1 < cursor := by omega
  rcases kept with same | ⟨old, held, older, newer⟩
  · have long : cursor ≤ now.entries.length := by
      have := congrArg List.length same
      simp only [List.length_take] at this
      omega
    have oldAt : now.entries[cursor - 1]? = before.entries[cursor - 1]? := by
      rw [← List.getElem?_take_of_lt index, same, List.getElem?_take_of_lt index]
    cases step_shape inv command with
    | same entries _ => exact Or.inl (by rw [entries, same])
    | extend entry entries _ _ =>
      exact Or.inl (by rw [entries, List.take_append_of_le_length long, same])
    | cut keep entries epoch =>
      by_cases covers : cursor ≤ keep
      · exact Or.inl (by rw [entries, List.take_take, Nat.min_eq_left covers, same])
      · obtain ⟨old, held⟩ : ∃ old, before.entries[cursor - 1]? = some old :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        refine Or.inr ⟨old, held, ?_, ?_⟩
        · rw [epoch]
          exact Nat.lt_succ_of_le (inv.bounded old (List.mem_of_getElem? (oldAt.trans held)))
        · intro entry present
          rw [entries, List.getElem?_take] at present
          simp [show ¬ cursor - 1 < keep by omega] at present
  · cases step_shape inv command with
    | same entries epoch =>
      exact Or.inr ⟨old, held, Nat.lt_of_lt_of_le older epoch, by rw [entries]; exact newer⟩
    | extend entry entries entryEpoch epoch =>
      refine Or.inr ⟨old, held, by omega, ?_⟩
      intro found present
      rw [entries, List.getElem?_append] at present
      split at present
      · exact newer found present
      · rename_i outside
        rw [List.getElem?_singleton] at present
        split at present
        · cases present
          omega
        · contradiction
    | cut keep entries epoch =>
      refine Or.inr ⟨old, held, by omega, ?_⟩
      intro found present
      rw [entries, List.getElem?_take] at present
      split at present
      · exact newer found present
      · contradiction

/-- RTDB rechecks the record at its cursor before it resumes. When that
record is unchanged, the whole prefix it applied is still the journal's,
whatever ran in between: no recovery rewrote what the follower saw. -/
theorem recheck_keeps_the_applied_prefix {before : State} (inv : Inv before)
    (commands : List Command) (cursor : Nat) (within : cursor ≤ before.head)
    (recheck : (run before commands).entries[cursor - 1]? = before.entries[cursor - 1]?) :
    (run before commands).entries.take cursor = before.entries.take cursor := by
  rcases Nat.eq_zero_or_pos cursor with rfl | positive
  · simp
  have kept : ∀ (commands : List Command) (now : State), Inv now → Kept before cursor now →
      Kept before cursor (run now commands) := by
    intro commands
    induction commands with
    | nil => exact fun _ _ kept => kept
    | cons command rest prior =>
      exact fun now inv kept => prior _ (step_inv inv command) (kept_step inv positive within kept command)
  rcases kept commands before inv (Or.inl rfl) with same | ⟨old, held, _, newer⟩
  · exact same
  · have := newer old (recheck.trans held)
    omega

/-- The follower's view of the journal: its next records and the recheck of
the record at its cursor. While the floor stays at or below the follower's,
every record after the cursor is retained, so the suffix is readable. -/
def journalView (before now : State) (cursor : Cursor) : View :=
  ⟨now.head, now.floor, decide (now.entries[cursor.head - 1]? = before.entries[cursor.head - 1]?),
    (now.entries.drop cursor.head).map .record⟩

/-- The pending recovery is the latest one, and an acknowledged latest
recovery left its typed entry right after the last record it kept. -/
def Latest (state : State) : Prop :=
  (∀ record, state.pending = some record → state.recoveries.getLast? = some record) ∧
    ∀ record, state.recoveries.getLast? = some record →
      state.pending = some record ∨ ∃ marker, state.entries[record.fence.head]? = some (.recovery record marker)

private theorem latest_extend {state next : State} (more : List Entry)
    (latest : Latest state) (entries : next.entries = state.entries ++ more)
    (recoveries : next.recoveries = state.recoveries) (pending : next.pending = state.pending) :
    Latest next := by
  refine ⟨fun record standing => recoveries ▸ latest.1 record (pending ▸ standing), ?_⟩
  intro record last
  rw [recoveries] at last
  rcases latest.2 record last with standing | ⟨marker, entry⟩
  · exact Or.inl (pending.trans standing)
  · refine Or.inr ⟨marker, ?_⟩
    rw [entries, List.getElem?_append_left (List.getElem?_eq_some_iff.mp entry).1, entry]

theorem latest_init : Latest {} := ⟨by simp, by simp⟩

theorem latest_step {state : State} (latest : Latest state) (command : Command) :
    Latest (JournalContract.apply state command).1 := by
  cases command with
  | «seal» writer =>
    simp only [JournalContract.apply]
    split
    · exact latest
    · split
      · exact latest_extend [] latest (by simp) rfl rfl
      · split <;> exact latest
  | append writer lsn payload =>
    simp only [JournalContract.apply]
    split
    · exact latest
    · split
      · exact latest
      · split
        · exact latest
        · split
          · exact latest_extend _ latest rfl rfl rfl
          · exact latest
  | trim writer through =>
    simp only [JournalContract.apply]
    split
    · exact latest_extend [] latest (by simp) rfl rfl
    · exact latest
  | recover survivor offloaded time =>
    simp only [JournalContract.apply]
    split
    · refine ⟨fun record standing => ?_, fun record last => ?_⟩
      · simp only [JournalContract.install, Option.some.injEq] at standing
        simp [JournalContract.install, standing]
      · left
        simp only [JournalContract.install, List.getLast?_append, List.getLast?_singleton,
          Option.some_or, Option.some.injEq] at last ⊢
        exact last
    · exact latest
  | acknowledge fence marker =>
    simp only [JournalContract.apply]
    split
    · rename_i record standing
      split
      · rename_i same
        refine ⟨fun _ cleared => by simp [JournalContract.writeEntry] at cleared, ?_⟩
        intro last newest
        right
        have isLast := latest.1 record standing
        simp only [JournalContract.writeEntry] at newest ⊢
        rw [isLast] at newest
        cases newest
        refine ⟨marker, ?_⟩
        have position : record.fence.head = state.entries.length := by
          rw [same.1, ← same.2]
          rfl
        rw [position]
        simp
      · exact latest
    · split <;> first | exact latest | (split <;> exact latest)
  | head => exact latest

theorem run_latest {state : State} (latest : Latest state) (commands : List Command) :
    Latest (run state commands) := by
  induction commands generalizing state with
  | nil => exact latest
  | cons command rest prior => exact prior (latest_step latest command)

/-- A follower resumes only past every acknowledged recovery it has seen:
when the journal's latest recovery is acknowledged and the view lets the
follower resume, the recovery's typed entry is in the prefix the follower
applied, so its epoch is in the follower's seen epoch. While the latest
recovery's fence still stands, the follower's prefix is intact and no
writer can seal (`apply` answers `Recovered`). -/
theorem follower_never_resumes_across_an_unseen_recovery {before : State} (inv : Inv before)
    (latest : Latest before) (commands : List Command) (cursor : Cursor)
    (within : cursor.head ≤ before.head)
    (seen : cursor.seen = learn 0 ((before.entries.take cursor.head).map .record))
    (resumes : mayResume cursor (journalView before (run before commands) cursor) = true)
    (record : Recovery) (last : (run before commands).recoveries.getLast? = some record) :
    (run before commands).pending = some record ∨
      (∃ marker, .recovery record marker ∈ before.entries.take cursor.head) ∧
        record.fence.epoch ≤ cursor.seen := by
  have allowed := resumes
  simp [mayResume, journalView] at allowed
  obtain ⟨⟨_, recheck⟩, fresh⟩ := allowed
  have prefixKept := recheck_keeps_the_applied_prefix inv commands cursor.head within recheck
  rcases (run_latest latest commands).2 record last with standing | ⟨marker, entry⟩
  · exact Or.inl standing
  · right
    by_cases below : record.fence.head < cursor.head
    · have member : .recovery record marker ∈ before.entries.take cursor.head := by
        rw [← prefixKept]
        exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt below, entry])
      refine ⟨⟨marker, member⟩, ?_⟩
      rw [seen]
      exact member_le_learn (record := .record (.recovery record marker)) 0 (List.mem_map_of_mem member)
    · exfalso
      have after : Observed.record (.recovery record marker) ∈
          (journalView before (run before commands) cursor).suffix := by
        apply List.mem_map_of_mem
        rw [List.mem_iff_getElem?]
        exact ⟨record.fence.head - cursor.head, by rw [List.getElem?_drop, Nat.add_sub_cancel' (by omega), entry]⟩
      exact absurd (fresh _ (by simpa [journalView] using after)) (by simp [freshEvidence])

#print axioms checkpoint_stamps_its_cut
#print axioms checkpoint_and_suffix_preserve_seen_epoch
#print axioms follower_rebuilds_across_unseen_recovery
#print axioms rebuild_installs_recovery_evidence
#print axioms auto_resume_requires_seen_epoch
#print axioms step_shape
#print axioms recheck_keeps_the_applied_prefix
#print axioms latest_step
#print axioms follower_never_resumes_across_an_unseen_recovery

end Logkeeper.ConsensusAdditions.RTDBRecovery
