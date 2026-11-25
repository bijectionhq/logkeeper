import Logkeeper.LeaderJournal

namespace Logkeeper.LeaderJournal.Media

set_option warningAsError true

/-- The snapshot cut is a ghost log. A physical image represents it by its
    included index and term, configuration, reducer fields and retained bytes. -/
structure Image (Payload : Type) where
  snapshot : Log (Request Payload)
  suffix : Log (Request Payload)

def Image.history (image : Image Payload) : Log (Request Payload) :=
  image.snapshot ++ image.suffix

def Image.restore [DecidableEq Payload] (image : Image Payload) : Journal Payload :=
  image.suffix.foldl applyEntry (replay image.snapshot)

theorem restore_exact [DecidableEq Payload] (image : Image Payload) :
    image.restore = replay image.history := by
  simp [Image.restore, Image.history, replay, List.foldl_append]

structure Prepared (Payload : Type) where
  cut : Log (Request Payload)
  synced : Bool

structure Disk (Payload : Type) where
  selected : Image Payload
  prepared : Option (Prepared Payload)
  term : Nat
  vote : Option KeeperId

def Image.install (history cut : Log (Request Payload)) : Image Payload :=
  ⟨cut, history.drop cut.length⟩

theorem install_history {known cut : Log (Request Payload)} (exactCut : cut <+: known) :
    (Image.install known cut).history = known := by
  obtain ⟨suffix, rfl⟩ := exactCut
  simp [Image.install, Image.history]

/-- The sync and manifest selections are abstract durable barriers. A prepared
    image may be abandoned by a crash at any point before manifest selection. -/
inductive Step : Disk Payload → Disk Payload → Prop
  | prepare {disk} (cut applied : Log (Request Payload))
      (forward : disk.selected.snapshot <+: cut) (appliedCut : cut <+: applied)
      (known : applied <+: disk.selected.history) :
      Step disk { disk with prepared := some ⟨cut, false⟩ }
  | sync {disk cut} (prepared : disk.prepared = some ⟨cut, false⟩) :
      Step disk { disk with prepared := some ⟨cut, true⟩ }
  | publish {disk cut} (synced : disk.prepared = some ⟨cut, true⟩)
      (selected : cut <+: disk.selected.history) :
      Step disk { disk with
        selected := Image.install disk.selected.history cut
        prepared := none }
  | crash {disk} : Step disk { disk with prepared := none }
  | reclaim {disk} : Step disk disk

inductive Trace : Disk Payload → Disk Payload → Prop
  | nil (disk : Disk Payload) : Trace disk disk
  | snoc {first before after} : Trace first before → Step before after → Trace first after

theorem step_preserves_recovery {before after : Disk Payload} (step : Step before after) :
    after.selected.history = before.selected.history ∧
      after.term = before.term ∧ after.vote = before.vote := by
  cases step with
  | publish _ selected => exact ⟨install_history selected, rfl, rfl⟩
  | _ => exact ⟨rfl, rfl, rfl⟩

theorem trace_preserves_recovery {before after : Disk Payload} (trace : Trace before after) :
    after.selected.history = before.selected.history ∧
      after.term = before.term ∧ after.vote = before.vote := by
  induction trace with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | snoc _ step ih =>
      obtain ⟨history, term, vote⟩ := step_preserves_recovery step
      exact ⟨history.trans ih.1, term.trans ih.2.1, vote.trans ih.2.2⟩

/-- A reclaimed or restarted image still provides the exact applied cut and
    accepted suffix that the consensus proof reads at election. -/
theorem compaction_refines_durable_replica {s : Cluster Payload} {keeper : KeeperId}
    {before after : Disk Payload} (trace : Trace before after)
    (represents : before.selected.history = s.durable keeper)
    (sound : Sound s) :
    after.selected.history = s.durable keeper ∧ s.applied keeper <+: after.selected.history := by
  have exactHistory := (trace_preserves_recovery trace).1.trans represents
  exact ⟨exactHistory, exactHistory.symm ▸ (sound.applied keeper).2⟩

theorem snapshot_and_suffix_restore_same_applied_state [DecidableEq Payload]
    {cut applied : Log (Request Payload)} (covered : cut <+: applied) :
    (Image.install applied cut).restore = replay applied := by
  rw [restore_exact, install_history covered]

theorem retained_snapshot_record {s : Journal Payload} {lsn : Nat} {payload : Payload}
    (bounds : s.Valid) (live : s.deleted = false) (retained : s.floor ≤ lsn)
    (stored : s.record lsn = some payload) :
    s.retain[lsn - s.floor]? = some payload := by
  have nonzero : lsn ≠ 0 := by have := bounds.1; omega
  have index : s.floor - 1 + (lsn - s.floor) = lsn - 1 := by have := bounds.1; omega
  have exactRecord : s.history[lsn - 1]? = some payload := by
    simpa only [Journal.record, ite_eq_right nonzero] using stored
  simpa [Journal.retain, live, List.getElem?_drop, index] using exactRecord

#print axioms compaction_refines_durable_replica
#print axioms snapshot_and_suffix_restore_same_applied_state
#print axioms retained_snapshot_record

end Logkeeper.LeaderJournal.Media
