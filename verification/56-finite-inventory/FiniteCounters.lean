import PoolIncarnations

set_option warningAsError true

namespace FiniteCounters

open PoolIncarnations (State Access Phase Event Validation)
open SharedExtentAccounting (Layout)
open SnapshotAdmission (setSlot)

variable {Ticket Book : Type}

structure Fits (serialMax epochMax : Nat) (state : State Ticket) : Prop where
  issuer : state.issued ≤ serialMax
  epochs : ∀ scope ∈ state.registry, (state.access scope).epoch ≤ epochMax + 1
  blocked : ∀ scope ∈ state.registry, epochMax < (state.access scope).epoch →
    (state.access scope).phase = .offline

def Ordered (state : State Ticket) : Prop :=
  state.registry.Pairwise (fun earlier later => later < earlier) ∧
    ∀ scope ∈ state.registry, 0 < scope

inductive Step [DecidableEq Ticket] (limit serialMax epochMax : Nat)
    (layout : Layout Nat) (needs : SharedCustody.Dependencies)
    (closeAllowed : Nat → Prop) (reserve : ProviderIOClosure.Custody Ticket → Prop)
    (expected : SharedExtentAccounting.State Nat Ticket → Nat → Book)
    (authenticated : Validation Book → Prop) (namespaceClosed : Nat → Prop) :
    State Ticket → Event → State Ticket → Prop
  | register {state} (room : state.registry.length < limit) (fresh : state.issued < serialMax) :
      Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .register (PoolIncarnations.register state)
  | fault {state} (scope : Nat) (enrolled : scope ∈ state.registry)
      (canAdvance : (state.access scope).epoch ≤ epochMax) :
      Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .fault (PoolIncarnations.fault state scope)
  | reconnect {state} (scope : Nat) (enrolled : scope ∈ state.registry)
      (offline : (state.access scope).phase = .offline) (usable : (state.access scope).epoch ≤ epochMax) :
      Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .reconnect (PoolIncarnations.changePhase state scope .quarantine)
  | validate {state} (scope : Nat) (proof : Validation Book)
      (verified : PoolIncarnations.CanOpen expected authenticated state scope proof)
      (usable : (state.access scope).epoch ≤ epochMax) :
      Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .validate (PoolIncarnations.changePhase state scope .eligible)
  | settle {state next}
      (update : PoolIncarnations.Step limit layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .settle next) :
      Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .settle next
  | account {state next}
      (update : PoolIncarnations.Step limit layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .account next) :
      Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
        namespaceClosed state .account next

variable [DecidableEq Ticket] {limit serialMax epochMax : Nat} {layout : Layout Nat}
variable {needs : SharedCustody.Dependencies} {closeAllowed namespaceClosed : Nat → Prop}
variable {reserve : ProviderIOClosure.Custody Ticket → Prop}
variable {expected : SharedExtentAccounting.State Nat Ticket → Nat → Book}
variable {authenticated : Validation Book → Prop}

theorem every_finite_step_is_the_original_custody_step {state next : State Ticket} {event : Event}
    (step : Step limit serialMax epochMax layout needs closeAllowed reserve
      expected authenticated namespaceClosed state event next) :
    PoolIncarnations.Step limit layout needs closeAllowed reserve expected authenticated
      namespaceClosed state event next := by
  cases step with
  | register room _ => exact .register room
  | fault scope live _ => exact .fault scope live
  | reconnect scope live offline _ => exact .reconnect scope live offline
  | validate scope proof verified _ => exact .validate scope proof verified
  | settle update | account update => exact update

omit [DecidableEq Ticket] in
private theorem phase_change_keeps_the_counter_bound
    {state : State Ticket} (fits : Fits serialMax epochMax state) (scope : Nat) (phase : Phase)
    (usable : (state.access scope).epoch ≤ epochMax) :
    Fits serialMax epochMax (PoolIncarnations.changePhase state scope phase) := by
  refine ⟨fits.issuer, ?_, ?_⟩
  · intro current live
    by_cases same : current = scope
    · subst current
      simpa [PoolIncarnations.changePhase, PoolIncarnations.setAccess, setSlot]
        using Nat.le_succ_of_le usable
    · simpa [PoolIncarnations.changePhase, PoolIncarnations.setAccess, setSlot, same]
        using fits.epochs current live
  · intro current live exhausted
    by_cases same : current = scope
    · subst current
      simp [PoolIncarnations.changePhase, PoolIncarnations.setAccess, setSlot] at exhausted
      omega
    · simpa [PoolIncarnations.changePhase, PoolIncarnations.setAccess, setSlot, same] using
        fits.blocked current live (by
          simpa [PoolIncarnations.changePhase, PoolIncarnations.setAccess, setSlot, same] using exhausted)

theorem finite_steps_preserve_custody_and_representability {state next : State Ticket} {event : Event}
    (safe : PoolIncarnations.Sound limit layout needs state) (fits : Fits serialMax epochMax state)
    (step : Step limit serialMax epochMax layout needs closeAllowed reserve
      expected authenticated namespaceClosed state event next) :
    PoolIncarnations.Sound limit layout needs next ∧ Fits serialMax epochMax next := by
  refine ⟨PoolIncarnations.every_step_preserves_bounded_scoped_custody safe
    (every_finite_step_is_the_original_custody_step step), ?_⟩
  cases step with
  | register _ fresh =>
      let allocated := state.issued + 1
      refine ⟨Nat.succ_le_of_lt fresh, ?_, ?_⟩
      · intro scope live
        change scope ∈ allocated :: state.registry at live
        rcases List.mem_cons.mp live with same | earlier
        · subst scope
          simp [PoolIncarnations.register, setSlot, allocated]
        · have different : scope ≠ allocated := by
            have known := safe.issued scope earlier
            omega
          simpa [PoolIncarnations.register, setSlot, allocated, different] using fits.epochs scope earlier
      · intro scope live exhausted
        change scope ∈ allocated :: state.registry at live
        rcases List.mem_cons.mp live with same | earlier
        · subst scope
          simp [PoolIncarnations.register, setSlot, allocated] at exhausted
        · have different : scope ≠ allocated := by
            have known := safe.issued scope earlier
            omega
          simpa [PoolIncarnations.register, setSlot, allocated, different] using
            fits.blocked scope earlier (by simpa [PoolIncarnations.register, setSlot, allocated, different] using exhausted)
  | fault scope _ canAdvance =>
      refine ⟨fits.issuer, ?_, ?_⟩
      · intro current live
        by_cases same : current = scope
        · subst current
          simpa [PoolIncarnations.fault, PoolIncarnations.setAccess, setSlot]
            using Nat.succ_le_succ canAdvance
        · simpa [PoolIncarnations.fault, PoolIncarnations.setAccess, setSlot, same] using fits.epochs current live
      · intro current live exhausted
        by_cases same : current = scope
        · subst current
          simp [PoolIncarnations.fault, PoolIncarnations.setAccess, setSlot]
        · simpa [PoolIncarnations.fault, PoolIncarnations.setAccess, setSlot, same] using
            fits.blocked current live (by
              simpa [PoolIncarnations.fault, PoolIncarnations.setAccess, setSlot, same] using exhausted)
  | reconnect scope _ _ usable => exact phase_change_keeps_the_counter_bound fits scope .quarantine usable
  | validate scope _ _ usable => exact phase_change_keeps_the_counter_bound fits scope .eligible usable
  | settle update =>
      cases update with
      | settle =>
          exact ⟨fits.issuer, fun scope live => fits.epochs scope (List.mem_filter.mp live).1,
            fun scope live => fits.blocked scope (List.mem_filter.mp live).1⟩
  | account update =>
      cases update with
      | account => exact ⟨fits.issuer, fits.epochs, fits.blocked⟩

theorem finite_steps_keep_a_canonical_registry_order {state next : State Ticket} {event : Event}
    (safe : PoolIncarnations.Sound limit layout needs state)
    (ordered : Ordered state)
    (step : Step limit serialMax epochMax layout needs closeAllowed reserve
      expected authenticated namespaceClosed state event next) :
    Ordered next := by
  cases step with
  | register =>
      refine ⟨List.pairwise_cons.mpr ⟨?_, ordered.1⟩, ?_⟩
      · exact fun scope live => Nat.lt_succ_of_le (safe.issued scope live)
      · intro scope live
        rcases List.mem_cons.mp live with rfl | old
        · exact Nat.zero_lt_succ _
        · exact ordered.2 scope old
  | fault | reconnect | validate => exact ordered
  | settle update =>
      cases update with
      | settle =>
          exact ⟨ordered.1.filter _, fun scope live => ordered.2 scope (List.mem_filter.mp live).1⟩
  | account update =>
      cases update with
      | account => exact ordered

theorem no_registration_can_wrap_at_the_issuer_limit {state next : State Ticket}
    (full : state.issued = serialMax) :
    ¬ Step limit serialMax epochMax layout needs closeAllowed reserve
      expected authenticated namespaceClosed state .register next := by
  intro admitted
  cases admitted with
  | register _ fresh => exact (Nat.lt_irrefl serialMax) (full ▸ fresh)

theorem a_fault_at_the_last_access_epoch_closes_without_losing_custody {state : State Ticket} {scope : Nat}
    (live : scope ∈ state.registry) (lastEpoch : (state.access scope).epoch = epochMax) :
    let next := PoolIncarnations.fault state scope
    Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated namespaceClosed
      state .fault next ∧ next.ledger = state.ledger ∧ next.registry = state.registry ∧
      (next.access scope).epoch = epochMax + 1 ∧ (next.access scope).phase = .offline := by
  refine ⟨.fault scope live (by omega), rfl, rfl, ?_, ?_⟩ <;>
    simp [PoolIncarnations.fault, PoolIncarnations.setAccess, setSlot, lastEpoch]

theorem reconnect_cannot_reopen_an_exhausted_incarnation {state next : State Ticket} {scope : Nat}
    (exhausted : epochMax < (state.access scope).epoch)
    (offline : (state.access scope).phase = .offline)
    (admitted : Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated
      namespaceClosed state .reconnect next) :
    (next.access scope).phase = .offline := by
  cases admitted with
  | reconnect current _ _ usable =>
      have different : scope ≠ current := by
        intro same
        subst current
        exact (Nat.not_lt_of_ge usable) exhausted
      simpa [PoolIncarnations.changePhase, PoolIncarnations.setAccess, setSlot, different] using offline

theorem exact_custody_settlement_can_run_with_both_counters_exhausted {state : State Ticket} {scope : Nat}
    (live : scope ∈ state.registry) (offline : (state.access scope).phase = .offline)
    (terminal : namespaceClosed scope) (clear : PoolIncarnations.Uncharged layout state scope) :
    Step limit serialMax epochMax layout needs closeAllowed reserve expected authenticated namespaceClosed
      state .settle (PoolIncarnations.forget state scope) :=
  .settle (.settle scope live offline terminal clear)

omit [DecidableEq Ticket] in
theorem recovering_the_exact_selected_base_and_suffix_restores_the_inventory
    {Command : Type} (apply : State Ticket → Command → State Ticket)
    (initial selected : State Ticket) (base tail chosen : List Command)
    (verifiedBase : base.foldl apply initial = selected) (verifiedTail : base ++ tail = chosen) :
    tail.foldl apply selected = chosen.foldl apply initial := by
  rw [← verifiedBase, ← verifiedTail, List.foldl_append]

#print axioms every_finite_step_is_the_original_custody_step
#print axioms finite_steps_preserve_custody_and_representability
#print axioms finite_steps_keep_a_canonical_registry_order
#print axioms no_registration_can_wrap_at_the_issuer_limit
#print axioms a_fault_at_the_last_access_epoch_closes_without_losing_custody
#print axioms reconnect_cannot_reopen_an_exhausted_incarnation
#print axioms exact_custody_settlement_can_run_with_both_counters_exhausted
#print axioms recovering_the_exact_selected_base_and_suffix_restores_the_inventory

end FiniteCounters
