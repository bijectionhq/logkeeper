/-!
Continuous offload of committed records to object storage, and recovery
from the object store plus a survivor (design section "Endgame", subsection
"Complements").

One offload lineage of one stream. The ghost `committed` is the stream's
committed log, which Raft only ever extends. The uploader reads applied
entries only (`applied ≤ committed.length`), uploads the records from
`offloaded_through` on as one object, and advances `offloaded_through`. The
writer's trim may delete whole objects below a new floor.

`step_preserves_good` keeps the offload invariant: objects are contiguous
from the lineage's floor, together they hold exactly the committed records in
`[floor, offloaded_through)`, and `offloaded_through ≤ applied ≤ commit`.
`uploaded_prefix` and `object_records_committed` follow: the uploaded prefix
is a prefix of the committed log, and every object holds the committed
records at its LSNs. `through_monotone` shows `offloaded_through` never moves
back within a lineage.

Recovery (`Command::Restore` before `Command::Recover`) restores the
committed records up to `known = max offloaded_through survivorCommit`: the
survivor's committed prefix when it is at least as long as the store's, the
store's prefix otherwise. `restore_exact` shows the restored log is exactly
the committed log through `known`, so recovery loses exactly the committed
records past `known`, and `restore_keeps_uploaded` that the old lineage's
uploaded prefix is a prefix of the restored log, which starts the new
lineage. `one_recovery_record` states the owner's one-record decision: the
recovery marker opens the next configuration epoch, which is the new offload
lineage, at the reported loss point. The control `whole_survivor_log_diverges` shows why the restore
point is the known-committed `known` and not the survivor's head: a survivor
may hold an uncommitted record at an LSN at or below its head where the
committed log holds another, so a loss check that compares heads misses it.
-/

namespace Logkeeper.ConsensusAdditions.OffloadPrefix

set_option warningAsError true

abbrev Entry := Nat × Nat
abbrev Log := List Entry

/-- An uploaded object: the records at LSNs `start ..< start + records.length`
    (LSNs index the committed log from 0 here). -/
structure Object where
  start : Nat
  records : Log

def uploaded (objects : List Object) : Log := objects.flatMap Object.records

/-- Each object starts where the previous one ended. -/
def Contiguous : Nat → List Object → Prop
  | _, [] => True
  | start, object :: rest => object.start = start ∧ Contiguous (start + object.records.length) rest

/-- The committed records at LSNs `[start, stop)`. -/
def segment (log : Log) (start stop : Nat) : Log := (log.drop start).take (stop - start)

theorem segment_split (log : Log) {a b c : Nat} (ab : a ≤ b) (bc : b ≤ c) :
    segment log a c = segment log a b ++ segment log b c := by
  unfold segment
  rw [show c - a = (b - a) + (c - b) by omega, List.take_add, List.drop_drop,
    show a + (b - a) = b by omega]

theorem segment_length (log : Log) {a b : Nat} (ab : a ≤ b) (within : b ≤ log.length) :
    (segment log a b).length = b - a := by
  unfold segment
  rw [List.length_take, List.length_drop]
  omega

theorem segment_extend (log more : Log) {a b : Nat} (within : b ≤ log.length) :
    segment (log ++ more) a b = segment log a b := by
  unfold segment
  by_cases early : a ≤ log.length
  · rw [List.drop_append_of_le_length early,
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  · have : b - a = 0 := by omega
    simp [this]

structure Offload where
  committed : Log
  applied : Nat
  through : Nat
  floor : Nat
  objects : List Object

/-- The offload invariant. -/
structure Good (o : Offload) : Prop where
  floorBelow : o.floor ≤ o.through
  throughApplied : o.through ≤ o.applied
  appliedCommitted : o.applied ≤ o.committed.length
  contiguous : Contiguous o.floor o.objects
  exact : uploaded o.objects = segment o.committed o.floor o.through

inductive Step : Offload → Offload → Prop
  /-- Raft commits more records: the committed log only grows by extension. -/
  | commit (o : Offload) (more : Log) : Step o { o with committed := o.committed ++ more }
  | apply (o : Offload) (applied : Nat) :
      o.applied ≤ applied → applied ≤ o.committed.length → Step o { o with applied }
  /-- Upload `count` applied records from `offloaded_through` as one object. -/
  | upload (o : Offload) (count : Nat) :
      o.through + count ≤ o.applied →
      Step o { o with
        through := o.through + count
        objects := o.objects ++ [⟨o.through, segment o.committed o.through (o.through + count)⟩] }
  /-- The writer's trim deletes the first object; the floor moves past it. -/
  | trim (o : Offload) (first : Object) (rest : List Object) :
      o.objects = first :: rest →
      Step o { o with floor := o.floor + first.records.length, objects := rest }

theorem contiguous_append {start : Nat} {objects : List Object}
    (contiguous : Contiguous start objects) (object : Object)
    (ends : object.start = start + (uploaded objects).length) :
    Contiguous start (objects ++ [object]) := by
  induction objects generalizing start with
  | nil => simp [Contiguous, uploaded] at ends ⊢; exact ends
  | cons head tail ih =>
      obtain ⟨here, rest⟩ := contiguous
      refine ⟨here, ih rest ?_⟩
      simp [uploaded, List.flatMap_cons] at ends
      simp [uploaded]
      omega

theorem step_preserves_good {o next : Offload} (good : Good o) (step : Step o next) :
    Good next := by
  obtain ⟨floorBelow, throughApplied, appliedCommitted, contiguous, exact⟩ := good
  cases step with
  | commit more =>
      refine ⟨floorBelow, throughApplied, by simp; omega, contiguous, ?_⟩
      show uploaded o.objects = segment (o.committed ++ more) o.floor o.through
      rw [exact, segment_extend _ _ (by omega)]
  | apply applied grows within =>
      exact ⟨floorBelow, show o.through ≤ applied by omega, within, contiguous, exact⟩
  | upload count within =>
      have length : (uploaded o.objects).length = o.through - o.floor := by
        rw [exact,
          segment_length o.committed floorBelow (Nat.le_trans throughApplied appliedCommitted)]
      refine ⟨by simp; omega, within, appliedCommitted,
        contiguous_append contiguous _
          (show o.through = o.floor + (uploaded o.objects).length by rw [length]; omega), ?_⟩
      show uploaded (o.objects ++ _) = segment o.committed o.floor (o.through + count)
      rw [segment_split o.committed floorBelow (Nat.le_add_right _ count), ← exact]
      simp [uploaded]
  | trim first rest split =>
      rw [split] at contiguous exact
      obtain ⟨starts, rest_contiguous⟩ := contiguous
      have whole : first.records ++ uploaded rest = segment o.committed o.floor o.through := by
        rw [← exact]; simp [uploaded]
      have bound : first.records.length ≤ o.through - o.floor := by
        have := congrArg List.length whole
        rw [segment_length o.committed floorBelow (Nat.le_trans throughApplied appliedCommitted),
          List.length_append] at this
        omega
      rw [segment_split o.committed (Nat.le_add_right o.floor first.records.length)
        (show o.floor + first.records.length ≤ o.through by omega)] at whole
      have parts := List.append_inj whole (by
        rw [segment_length o.committed (Nat.le_add_right o.floor first.records.length)
          (by omega)]
        omega)
      exact ⟨by simp; omega, throughApplied, appliedCommitted, rest_contiguous, parts.2⟩

/-- `offloaded_through` never moves back within a lineage. -/
theorem through_monotone {o next : Offload} (step : Step o next) : o.through ≤ next.through := by
  cases step <;> simp

/-- `offloaded_through ≤ commit`. -/
theorem through_committed {o : Offload} (good : Good o) : o.through ≤ o.committed.length :=
  Nat.le_trans good.throughApplied good.appliedCommitted

/-- The uploaded prefix is a prefix of the committed log from the floor. -/
theorem uploaded_prefix {o : Offload} (good : Good o) :
    uploaded o.objects <+: o.committed.drop o.floor := by
  rw [good.exact]
  exact List.take_prefix _ _

/-- Every object holds the committed records at its LSNs. -/
theorem object_records_committed {log : Log} {start : Nat} {objects : List Object}
    (contiguous : Contiguous start objects) (isPrefix : uploaded objects <+: log.drop start) :
    ∀ object ∈ objects, ∀ index < object.records.length,
      object.records[index]? = log[object.start + index]? := by
  induction objects generalizing start with
  | nil => intro _ absent; simp at absent
  | cons head tail ih =>
      obtain ⟨here, rest⟩ := contiguous
      obtain ⟨extra, whole⟩ := isPrefix
      simp only [uploaded, List.flatMap_cons, List.append_assoc] at whole
      intro object member index within
      rcases List.mem_cons.mp member with same | later
      · subst same
        have := congrArg (·[index]?) whole
        simp only [List.getElem?_append_left within, List.getElem?_drop] at this
        rw [this, here]
      · refine ih rest ⟨extra, ?_⟩ object later index within
        have := congrArg (List.drop head.records.length) whole
        rw [List.drop_left, List.drop_drop] at this
        exact this

theorem objects_hold_committed {o : Offload} (good : Good o) :
    ∀ object ∈ o.objects, ∀ index < object.records.length,
      object.records[index]? = o.committed[object.start + index]? :=
  object_records_committed good.contiguous (uploaded_prefix good)

/-! ## Recovery from the object store plus a survivor -/

/-- The survivor's log and its commit index. Raft makes its committed prefix
    a prefix of the committed log. -/
structure Survivor where
  log : Log
  commit : Nat

/-- The known-committed point: what the object store or the survivor's
    committed prefix covers. -/
def known (o : Offload) (survivor : Survivor) : Nat := max o.through survivor.commit

/-- `Command::Restore`: the survivor's committed prefix when it is at least as
    long as the store's, the uploaded records otherwise, from the floor. -/
def restore (o : Offload) (survivor : Survivor) : Log :=
  if o.through ≤ survivor.commit then (survivor.log.take survivor.commit).drop o.floor
  else uploaded o.objects

/-- Recovery loses exactly the committed records past `known`: the restored
    log is the committed log from the floor through `known`, and the
    committed log from the floor is the restored log followed by the loss. -/
theorem restore_exact {o : Offload} (good : Good o) (survivor : Survivor)
    (committedPrefix : survivor.log.take survivor.commit <+: o.committed)
    (held : survivor.commit ≤ survivor.log.length) :
    restore o survivor = segment o.committed o.floor (known o survivor) ∧
      o.committed.drop o.floor =
        restore o survivor ++ (o.committed.drop o.floor).drop (known o survivor - o.floor) := by
  have restored : restore o survivor = segment o.committed o.floor (known o survivor) := by
    unfold restore known
    split
    · next covers =>
        rw [Nat.max_eq_right covers]
        obtain ⟨rest, whole⟩ := committedPrefix
        have length : (survivor.log.take survivor.commit).length = survivor.commit := by
          rw [List.length_take]; omega
        unfold segment
        have floorBelow := good.floorBelow
        rw [← whole, List.drop_append_of_le_length (by omega),
          List.take_append_of_le_length (by rw [List.length_drop]; omega),
          List.take_of_length_le (l := List.drop o.floor (List.take survivor.commit survivor.log))
            (by rw [List.length_drop]; omega)]
    · next beyond =>
        rw [Nat.max_eq_left (by omega)]
        exact good.exact
  refine ⟨restored, ?_⟩
  rw [restored]
  exact (List.take_append_drop _ _).symm

/-- The old lineage's uploaded prefix is a prefix of the restored log, which
    starts the new lineage. -/
theorem restore_keeps_uploaded {o : Offload} (good : Good o) (survivor : Survivor)
    (committedPrefix : survivor.log.take survivor.commit <+: o.committed)
    (held : survivor.commit ≤ survivor.log.length) :
    uploaded o.objects <+: restore o survivor := by
  rw [(restore_exact good survivor committedPrefix held).1, good.exact]
  exact List.take_prefix_take_left (by unfold known; omega)

/-- The restored head moves forward when the store holds a longer committed
    prefix than the survivor. -/
theorem restore_moves_forward {o : Offload} (good : Good o) (survivor : Survivor)
    (committedPrefix : survivor.log.take survivor.commit <+: o.committed)
    (held : survivor.commit ≤ survivor.log.length) :
    (restore o survivor).length = known o survivor - o.floor := by
  rw [(restore_exact good survivor committedPrefix held).1,
    segment_length _ (by unfold known; have := good.floorBelow; omega)
      (by unfold known; have := through_committed good
          have := committedPrefix.length_le; rw [List.length_take] at this; omega)]

/-- The one recovery record (owner decision, 2026-11-27): the catalog's
    recovery transaction bumps the stream's configuration epoch, the new
    offload lineage is that epoch, and the journal's recovery marker, the
    first entry of the new epoch, carries it and the loss point. -/
structure RecoveryRecord where
  epoch : Nat
  lossPoint : Nat

/-- The recovery: the restored log followed by the marker of the next
    configuration epoch, at the loss point `known`. -/
def recover (o : Offload) (survivor : Survivor) (epoch : Nat) : Log × RecoveryRecord :=
  (restore o survivor ++ [(epoch + 1, known o survivor)], ⟨epoch + 1, known o survivor⟩)

/-- One record: the marker opens the next epoch at the reported loss point,
    every committed record below it is kept at its LSN, and the old
    lineage's uploads are a prefix of the new lineage's log. -/
theorem one_recovery_record {o : Offload} (good : Good o) (survivor : Survivor) (epoch : Nat)
    (committedPrefix : survivor.log.take survivor.commit <+: o.committed)
    (held : survivor.commit ≤ survivor.log.length) :
    let (log, record) := recover o survivor epoch
    record.epoch = epoch + 1 ∧ record.lossPoint = known o survivor ∧
      log = segment o.committed o.floor record.lossPoint ++ [(record.epoch, record.lossPoint)] ∧
      uploaded o.objects <+: log := by
  have exact := (restore_exact good survivor committedPrefix held).1
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show restore o survivor ++ _ = _
    rw [exact]
  · exact (restore_keeps_uploaded good survivor committedPrefix held).trans
      (List.prefix_append _ _)

/-- The control: a survivor holds an uncommitted record `(1, 9)` at LSN 1, at
    or below its head 2, where the committed log holds `(2, 2)`. Restoring
    its whole log would keep the head at the acknowledged LSN and silently
    replace the committed record, so a loss check that compares heads finds
    nothing. Restoring through `known` drops it and reports LSN 1 lost. -/
theorem whole_survivor_log_diverges :
    let committed : Log := [(1, 1), (2, 2)]
    let survivor : Survivor := ⟨[(1, 1), (1, 9)], 1⟩
    survivor.log.take survivor.commit <+: committed ∧
      committed.length ≤ survivor.log.length ∧ survivor.log[1]? ≠ committed[1]? ∧
      survivor.log.take (max 0 survivor.commit) = [(1, 1)] := by
  decide

#print axioms segment_split
#print axioms step_preserves_good
#print axioms through_monotone
#print axioms through_committed
#print axioms uploaded_prefix
#print axioms objects_hold_committed
#print axioms restore_exact
#print axioms restore_keeps_uploaded
#print axioms restore_moves_forward
#print axioms one_recovery_record
#print axioms whole_survivor_log_diverges

end Logkeeper.ConsensusAdditions.OffloadPrefix
