import DecisionKernel

set_option warningAsError true

namespace Logkeeper.DecisionKernel

open Kernel (Writer)
open Protocol (Credit)
open Protocol.Ordered (replay replay_mutation)
open Reducer (Owner Principal Cut Checkpoint Preparation Record Hold RequestId Receipt
  removesOwner pruneLeases leaseOwner replace trimCredit publishSelection)

theorem append_uses_current_writer
    (action : r.action = .append grant expected lane payload bytes references)
    (applied : Applied limits s r (.appended cut) t) :
    s.history.active = true ∧ s.history.writer = grant ∧ erasurePending s = false ∧
    (∃ owner, s.authority.holder = some owner ∧ r.principal = .worker owner) ∧
    Kernel.Ordered.append_next_lsn s.history.head expected
      (min limits.history.recovery limits.history.retained) = some cut.nextLsn := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, openWriter, owner, _, ⟨active, current, next, _⟩, _⟩ := writes
  exact ⟨active, current, openWriter, owner, next⟩

theorem cached_mutation_returns_original
    (reading : r.action.isRead = false)
    (placed : earlyRefusal s r = none)
    (stored : s.book r.key = some entry) (matching : entry.fingerprint = r.fingerprint)
    (step : RequestStep limits r s receipt t) :
    receipt = entry.original ∧ t = s := by
  cases step with
  | early _ refused => simp [placed] at refused
  | cached _ _ found =>
    rw [stored] at found
    cases found
    exact ⟨by simp [cachedReceipt, reading, replay, replay_mutation, matching], rfl⟩
  | late _ _ unused _ => simp [stored] at unused
  | refused _ admitted | applied admitted _ =>
    have impossible := stored.symm.trans admitted.2.1
    contradiction

theorem barrier_holds_exact_cut
    (action : r.action = .lease (.acquire .read))
    (applied : Applied limits s r (.barrier hold) t) :
    hold.checkpoint = s.checkpoints.selected ∧ hold.start = s.checkpoints.selected.cut ∧
      hold.through = s.head ∧ exactRange s hold.start hold.through ∧
      t.holds r.id = some hold := by
  have writes := applied.commandEffect
  simp only [effect, action, Basis.outcome] at writes
  obtain ⟨_, equality, _, _, basis, inserted⟩ := writes
  cases equality
  obtain ⟨_, _, root, start, through, range⟩ := basis
  exact ⟨root, start, through, range, by simp [inserted.2.2.2, replace]⟩

theorem step_preserves_budget (inv : Inv limits s) (step : Step limits position time r s out t) :
    OrderedBudgets.fundedBudget t.budget.budget t.budget.window
      limits.ordinaryCapacity limits.reserve :=
  (step_preserves_inv inv step).budget

theorem step_preserves_object_separation
    (inv : Inv limits s) (step : Step limits position time r s out t) :
    ObjectWithdrawal.Safe t.objects :=
  (step_preserves_inv inv step).references

theorem trim_respects_protected_range
    (action : r.action = .collect (.prefix selected through))
    (applied : Applied limits s r (.trimmed cut credit) t) :
    selected = s.checkpoints.selected ∧ cut.nextLsn ≤ selected.cut.nextLsn ∧
      retainedCut s cut.nextLsn = some cut ∧ t.floor = cut ∧
      (∀ id hold, s.holds id = some hold → hold.start.nextLsn < hold.through.nextLsn →
        cut.nextLsn ≤ hold.start.nextLsn) ∧
      credit = trimCredit s.history (cut.nextLsn - s.floor.nextLsn) := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, root, _, _, bound, atCut, holds, floor, _, _, _, credit, _⟩ := writes
  exact ⟨root, bound, atCut, floor, holds, credit⟩

theorem lease_renewals_preserve_later_end
    (action : r.action = .lease (.renew scope))
    (outcome : out = match scope with
      | .writer _ => .leased issuedAt leaseEnd
      | .read _ _ => .readLeased issuedAt leaseEnd)
    (applied : Applied limits s r out t) :
    ∃ owner, r.principal = .worker owner ∧ issuedAt = s.time ∧
      leaseEnd = s.time + limits.leaseDuration ∧ leaseEnd ≤ limits.maxTime ∧
      t.leases owner = some (DisposalLease.retained_end (s.leases owner) leaseEnd) := by
  have writes := applied.commandEffect
  cases scope with
  | writer grant =>
    simp only [effect, action, outcome] at writes
    obtain ⟨_, _, _, owner, principal, _, _, issued, ends, bound, leases⟩ := writes
    exact ⟨owner, principal, issued, ends, bound, by simp [leases, replace]⟩
  | read hold id =>
    simp only [effect, action, outcome] at writes
    obtain ⟨_, principal, _, _, issued, ends, bound, leases⟩ := writes
    exact ⟨hold.owner, principal, issued, ends, bound, by simp [leases, replace]⟩

theorem read_renewal_requires_open_basis {id : RequestId}
    (action : r.action = .lease (.renew (.read hold id)))
    (applied : Applied limits s r (.readLeased issuedAt leaseEnd) t) :
    checkpointOpen s hold.checkpoint := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  exact writes.2.2.1

private theorem removed_owner_absent {id : RequestId} {holds : Reducer.Holds}
    (held : removesOwner holds owner id = some hold) : hold.owner ≠ owner := by
  cases present : holds id <;> simp_all [removesOwner]

theorem disposal_leaves_no_custody
    (action : r.action = .dispose owner basis)
    (applied : Applied limits s r (.workerDisposed owner) t) :
    t.leases owner = none ∧ ∀ id hold, t.holds id = some hold → hold.owner ≠ owner := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, permission, holds, leases⟩ := writes
  have withdrawn :
      DisposalLease.withdrawn owner.2 s.lastSerial (decide (s.roster owner.1 = some owner)) =
        true := by
    cases basis with
    | certified => exact permission.2.2
    | expired => exact (DisposalLease.disposal_requires_withdrawal_and_drift permission).1
  have noHolds : ∀ id hold, t.holds id = some hold → hold.owner ≠ owner := by
    intro id hold held
    rw [holds] at held
    exact removed_owner_absent held
  have absent : ¬ leaseOwner s.roster t.holds owner := by
    rintro (enrolled | ⟨id, hold, held, same⟩)
    · simp [DisposalLease.withdrawn, enrolled] at withdrawn
    · exact noHolds id hold held same
  exact ⟨by simp [leases, pruneLeases, absent], noHolds⟩

theorem expiry_disposal_cannot_race_a_bounded_worker
    (action : r.action = .dispose owner .expired)
    (applied : Applied limits s r (.workerDisposed owner) t)
    (leased : s.leases owner = some leaseEnd) (bounded : s.time ≤ workerClock + limits.drift) :
    ¬ DisposalLease.Admits leaseEnd workerClock := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  have due := (DisposalLease.disposal_requires_withdrawal_and_drift writes.2.2.1).2 leaseEnd leased
  exact DisposalLease.no_read_is_admitted_once_disposal_is_allowed _ _ _ _ bounded due

theorem rotation_requires_exact_preparation
    (action : r.action = .reconfigure (.rotate incumbent checkpoint))
    (applied : Applied limits s r (.granted writer recovery) t) :
    r.principal = .custodian ∧ s.history.active = true ∧ s.history.writer = incumbent ∧
    checkpoint.cut = s.head ∧ checkpoint ≠ s.checkpoints.selected ∧
    ∃ p, s.checkpoints.preparing = some p ∧ p.erasure = true ∧ p.source = incumbent ∧
      p.base = s.checkpoints.selected ∧ matchesPreparation p checkpoint := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, custodian, active, current, head, different, prepared, _⟩ := writes
  exact ⟨custodian, active, current, head, different, prepared⟩

theorem erasure_commit_is_atomic
    (action : r.action = .reconfigure (.rotate incumbent checkpoint))
    (applied : Applied limits s r (.granted writer recovery) t) :
    t.checkpoints.selected = checkpoint ∧ t.checkpoints.preparing = none ∧
    t.checkpoints.erasureFloor = s.head.nextLsn ∧
    t.authority.generation = s.authority.generation + 1 ∧ t.authority.holder = s.authority.holder ∧
    (∀ start, start < s.head.nextLsn →
      ErasureCommit.admits_history t.checkpoints.erasureFloor start = false) ∧
    (∀ id old, s.holds id = some old → t.holds id = some old) := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, _, _, head, _, _, _, _, _, _, _, inserted, successor, selected, _⟩ := writes
  have floor : t.checkpoints.erasureFloor = s.head.nextLsn := by
    simp [selected, publishSelection, ErasureCommit.erasure_floor, head]
  refine ⟨by simp [selected, publishSelection], by simp [selected, publishSelection], floor,
    ?_, ?_, ?_, ?_⟩
  · rw [successor.2.2.2]; rfl
  · rw [successor.2.2.2]; rfl
  · intro start older
    simp [floor, ErasureCommit.admits_history, Nat.not_le_of_lt older]
  · intro id old present
    have different : id ≠ r.id := by
      rintro rfl
      rw [inserted.1] at present
      contradiction
    simp [inserted.2.2.2, replace, different, present]

theorem erasure_closes_every_old_root
    (action : r.action = .reconfigure (.rotate incumbent checkpoint))
    (applied : Applied limits s r (.granted writer recovery) t)
    (old : t.checkpoints.oldRoots revision = some (root, closed)) :
    closed = true := by
  have writes := applied.commandEffect
  simp only [effect, action] at writes
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, selected, _⟩ := writes
  rw [selected] at old
  simp only [publishSelection] at old
  split at old
  · exact (congrArg Prod.snd (Option.some.inj old)).symm
  · cases existing : s.checkpoints.oldRoots revision with
    | none => simp [existing] at old
    | some previous =>
      obtain ⟨_, wasClosed⟩ := previous
      simp [existing] at old
      exact old.2

theorem erased_recovery_readability_requires_image_evidence
    (applied : Applied limits s r (.granted writer recovery) t)
    (action : r.action = .reconfigure (.rotate incumbent checkpoint))
    (clean : ErasureCommit.MayCommit s.authority.generation selectable)
    (suffix : ErasureCommit.Fenced selectable) :
    t.authority.generation = s.authority.generation + 1 ∧
    ∀ recoveryImage ∈ selectable, ErasureCommit.Readable s.authority.generation recoveryImage :=
  ⟨(erasure_commit_is_atomic action applied).2.2.2.1,
    ErasureCommit.every_selectable_recovery_avoids_the_revoked_generation _ _ clean suffix⟩

end Logkeeper.DecisionKernel
