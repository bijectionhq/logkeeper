import Std

namespace SharedWAL

structure Frame (Group Image : Type) where
  group : Group
  generation : Nat
  image : Image

variable {Group Image : Type} [DecidableEq Group]

def project (group : Group) (wal : List (Frame Group Image)) : List (Frame Group Image) :=
  wal.filter (fun row => row.group == group)

theorem project_append (group : Group) (left right : List (Frame Group Image)) :
    project group (left ++ right) = project group left ++ project group right := by
  simp [project]

theorem other_scope_append (group : Group) (wal tail : List (Frame Group Image))
    (different : ∀ row ∈ tail, row.group ≠ group) :
    project group (wal ++ tail) = project group wal := by
  rw [project_append]
  suffices project group tail = [] by simp [this]
  induction tail with
  | nil => rfl
  | cons row rest ih =>
    have other := different row (by simp)
    have restScoped : ∀ next ∈ rest, next.group ≠ group :=
      fun next member => different next (List.mem_cons_of_mem _ member)
    simp only [project, List.filter_cons, beq_eq_false_iff_ne.mpr other, Bool.false_eq_true,
      ite_false]
    exact ih restScoped

def recoverGroup (group : Group) (frames : List (Frame Group Image)) :=
  project group frames

theorem recovery_respects_scope (group : Group) (wal tail : List (Frame Group Image))
    (different : ∀ row ∈ tail, row.group ≠ group) :
    recoverGroup group (wal ++ tail) = project group wal := by
  exact other_scope_append group wal tail different

structure Log (Row : Type) where
  written : List Row
  frontier : Nat

def covered (wal : Log Row) : List Row := wal.written.take wal.frontier

def permitsReply (wal : Log Row) (id : Row) : Prop :=
  id ∈ covered wal

def reopen (wal : Log Row) (validTail : List Row) : List Row :=
  covered wal ++ validTail

theorem reply_survives_torn_tail (wal : Log Row) (id : Row) (tail : List Row)
    (reply : permitsReply wal id) : id ∈ reopen wal tail := by
  apply List.mem_append_left
  exact reply

def sync (wal : Log Row) : Log Row := { wal with frontier := wal.written.length }

theorem batch_covers_every_written_frame (wal : Log Row) :
    covered (sync wal) = wal.written := by
  simp [covered, sync]

def cleanup (owner : Group) (old : Nat) (wal : List (Frame Group Image)) :
    List (Frame Group Image) :=
  wal.filter (fun row => !(row.group == owner && row.generation == old))

theorem cleanup_preserves_other_scope (owner group : Group) (old : Nat)
    (wal : List (Frame Group Image)) (other : group ≠ owner) :
    project group (cleanup owner old wal) = project group wal := by
  rw [project, cleanup, List.filter_filter, project]
  apply List.filter_congr
  intro row _
  by_cases same : row.group = group
  · subst group
    simp [other]
  · simp [same]

theorem cleanup_removes_scoped_generation (owner : Group) (old : Nat)
    (wal : List (Frame Group Image)) (row : Frame Group Image)
    (member : row ∈ cleanup owner old wal) :
    row.group ≠ owner ∨ row.generation ≠ old := by
  by_cases scope : row.group = owner
  · right
    intro generation
    simp [cleanup, scope, generation] at member
  · exact Or.inl scope

theorem reachable_batch_with_torn_tail :
    ∃ wal : Log (Frame Nat Nat), ∃ (a b : Frame Nat Nat) (tail : List (Frame Nat Nat)),
      a.group ≠ b.group ∧ covered wal = [] ∧
      permitsReply (sync wal) a ∧ permitsReply (sync wal) b ∧
      let flushed := sync wal
      let withPending := { flushed with written := flushed.written ++ tail }
      tail.length = 2 ∧
      project 1 (reopen withPending []) = [a] ∧
      project 2 (reopen withPending []) = [b] := by
  let a : Frame Nat Nat := ⟨1, 1, 10⟩
  let b : Frame Nat Nat := ⟨2, 1, 20⟩
  let tail : List (Frame Nat Nat) := [⟨1, 1, 11⟩, ⟨2, 1, 21⟩]
  exact ⟨⟨[a, b], 0⟩, a, b, tail, by decide, rfl,
    by simp [permitsReply, covered, sync], by simp [permitsReply, covered, sync],
    rfl, rfl, rfl⟩

#print axioms project_append
#print axioms other_scope_append
#print axioms recovery_respects_scope
#print axioms reply_survives_torn_tail
#print axioms batch_covers_every_written_frame
#print axioms cleanup_preserves_other_scope
#print axioms cleanup_removes_scoped_generation
#print axioms reachable_batch_with_torn_tail

end SharedWAL
