import Safety

set_option warningAsError true

namespace Logkeeper.DecisionKernel

open Reducer (Cut Checkpoint RequestId Hold)

inductive Node where
  | replay
  | pending
  | hold (id : RequestId)
  | checkpoint (root : Checkpoint)
  | record (lsn : Nat)
  | object (name : Nat)

/-- Durable custody is a root until explicitly released or disposed. Pending
preparation may pin a base even when no worker holds it. -/
inductive Root (s : State) : Node → Prop
  | replay : Root s .replay
  | pending : Root s .pending
  | hold {id : RequestId} (present : s.holds id = some hold) : Root s (.hold id)

inductive Edge (s : State) : Node → Node → Prop
  | selected : Edge s .replay (.checkpoint s.checkpoints.selected)
  | suffix (starts : s.checkpoints.selected.cut.nextLsn ≤ lsn) (existsAt : lsn < s.head.nextLsn) :
    Edge s .replay (.record lsn)
  | protectedRoot {id : RequestId} (present : s.holds id = some hold) :
    Edge s (.hold id) (.checkpoint hold.checkpoint)
  | protectedRecord {id : RequestId} (present : s.holds id = some hold) (starts : hold.start.nextLsn ≤ lsn)
      (ends : lsn < hold.through.nextLsn) :
    Edge s (.hold id) (.record lsn)
  | pendingBase (present : s.checkpoints.preparing = some preparation) :
    Edge s .pending (.checkpoint preparation.base)
  | pendingObject (present : s.checkpoints.preparing = some preparation)
      (refs : s.objects.references name .root preparation.revision) :
    Edge s .pending (.object name)
  | rootObject (refs : s.objects.references name .root checkpoint.revision) :
    Edge s (.checkpoint checkpoint) (.object name)
  | recordObject (refs : s.objects.references name .suffix lsn) :
    Edge s (.record lsn) (.object name)

inductive Reachable (s : State) : Node → Prop
  | root : Root s node → Reachable s node
  | next : Reachable s source → Edge s source node → Reachable s node

theorem trimmed_records_are_unreachable
    (action : r.action = .collect (.prefix selected through))
    (applied : Applied limits s r (.trimmed cut credit) t) (removed : lsn < cut.nextLsn) :
    ¬ Reachable s (.record lsn) := by
  obtain ⟨rfl, bound, _, _, pins, _⟩ := trim_respects_protected_range action applied
  intro reachable
  cases reachable with
  | root root => cases root
  | next _ edge =>
    cases edge with
    | suffix start _ => omega
    | protectedRecord present starts ends =>
      have pinned := pins _ _ present (Nat.lt_of_le_of_lt starts ends)
      omega

theorem trim_drops_only_unreachable_record_references
    (action : r.action = .collect (.prefix selected through))
    (applied : Applied limits s r (.trimmed cut credit) t)
    (registered : s.objects.references name role owner)
    (dropped : ¬ t.objects.references name role owner) :
    role = .suffix ∧ owner < cut.nextLsn ∧ ¬ Reachable s (.record owner) := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, references⟩ := writes
  obtain ⟨_, _, updated⟩ := references
  have outside : ¬ (role ≠ .suffix ∨ cut.nextLsn ≤ owner) := by
    intro retained
    apply dropped
    rw [updated]
    exact ⟨registered, retained⟩
  have suffix : role = .suffix := Classical.not_not.mp (fun distinct => outside (.inl distinct))
  have earlier : owner < cut.nextLsn := Nat.lt_of_not_ge (fun later => outside (.inr later))
  exact ⟨suffix, earlier, trimmed_records_are_unreachable action applied earlier⟩

theorem settled_root_is_unreachable
    (action : r.action = .collect (.root checkpoint certificate floor))
    (applied : Applied limits s r (.checkpointSettled checkpoint) t)
    (different : checkpoint ≠ s.checkpoints.selected) :
    ¬ Reachable s (.checkpoint checkpoint) := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, _, _, _, _, noHold, noBase, _, _⟩ := writes
  intro reachable
  cases reachable with
  | root root => cases root
  | next _ edge =>
    cases edge with
    | selected => exact different rfl
    | protectedRoot present => exact noHold _ _ present rfl
    | pendingBase present => exact noBase _ present rfl

theorem settlement_requires_closed_root_and_exact_evidence
    (action : r.action = .collect (.root checkpoint certificate floor))
    (applied : Applied limits s r (.checkpointSettled checkpoint) t) :
    s.checkpoints.oldRoots checkpoint.revision = some (checkpoint, true) ∧
      floor = s.checkpoints.erasureFloor ∧ certificate ≠ 0 ∧
      t.checkpoints.oldRoots checkpoint.revision = none := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, _, exactFloor, evidence, closed, _, _, settled, _⟩ := writes
  exact ⟨closed, exactFloor, evidence, by simp [settled, Reducer.replace]⟩

/-- The physical graph includes every registered reference. It can exceed the
protection graph because an old root or covered record has yet to be removed. -/
inductive PhysicalPath (s : State) : Nat → Prop
  | registered (ref : s.objects.references name role owner) : PhysicalPath s name

theorem fence_requires_complete_unreferenced_name
    (action : r.action = .fence name version)
    (applied : Applied limits s r (.objectWithdrawn name version) t) :
    t.objects.fence name = some version ∧
      (s.objects.fence name ≠ some version →
        ¬ s.objects.hasOpaqueReferences ∧ ¬ PhysicalPath s name) := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  rcases writes.2.2.2.2 with ⟨already, same⟩ | ⟨available, _, update⟩
  · exact ⟨same ▸ already, fun different => False.elim (different already)⟩
  · refine ⟨by simp [update, Reducer.commitWithdrawal, Reducer.replace],
      fun _ => ⟨available.1, ?_⟩⟩
    rintro ⟨ref⟩
    exact available.2 ⟨_, _, ref⟩

/-- The hypothesized graph starts with just the selection and timed live
holds. It reuses the same edges, leaving a preparation without a root. -/
inductive LiveRoot (s : State) : Node → Prop
  | replay : LiveRoot s .replay
  | hold {id : RequestId} (present : s.holds id = some hold) (leased : s.leases hold.owner = some leaseEnd)
      (live : s.time < leaseEnd) : LiveRoot s (.hold id)

inductive LiveReachable (s : State) : Node → Prop
  | root : LiveRoot s node → LiveReachable s node
  | next : LiveReachable s source → Edge s source node → LiveReachable s node

theorem unleased_hold_still_pins_record {s : State} {id : RequestId} {hold : Hold}
    (noLeases : ∀ owner, s.leases owner = none)
    (selectedAfter : lsn < s.checkpoints.selected.cut.nextLsn)
    (present : s.holds id = some hold)
    (starts : hold.start.nextLsn ≤ lsn) (ends : lsn < hold.through.nextLsn) :
    Reachable s (.record lsn) ∧ ¬ LiveReachable s (.record lsn) := by
  refine ⟨.next (.root (.hold present)) (.protectedRecord present starts ends), ?_⟩
  intro live
  cases live with
  | root root => cases root
  | next path edge =>
    cases edge with
    | suffix starts _ => omega
    | protectedRecord =>
      cases path with
      | root root =>
        cases root with
        | hold _ leased _ => simp [noLeases] at leased
      | next _ edge => cases edge

end Logkeeper.DecisionKernel
