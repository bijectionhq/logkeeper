import StorageBoundary
import PoolIncarnations

set_option warningAsError true

namespace NamespaceClosure

variable {Address Payload Ticket Book : Type} {width : Nat}

structure Scope (Address : Type) where
  address : Address
  serial : Nat
  deriving DecidableEq

abbrev ChildAddress (Address : Type) (width : Nat) := Scope Address × Fin width
abbrev Guard (Address Payload : Type) (width : Nat) :=
  StorageBoundary.Slot (ChildAddress Address width) Payload

inductive Phase where
  | vacant
  | provisioning
  | serving
  | sealed
  deriving DecidableEq

structure Bank (Address Payload : Type) (width : Nat) where
  address : Address
  issued : Nat
  phase : Phase
  guards : Fin width → Option (Guard Address Payload width)

def current (bank : Bank Address Payload width) : Scope Address :=
  ⟨bank.address, bank.issued⟩

def withGuard (bank : Bank Address Payload width) (index : Fin width)
    (value : Option (Guard Address Payload width)) : Bank Address Payload width :=
  {bank with guards := fun other => if other = index then value else bank.guards other}

def vacantGuard (scope : Scope Address) (index : Fin width) : Guard Address Payload width :=
  ⟨(scope, index), 0, .vacant⟩

def CanSeed (bank : Bank Address Payload width) (scope : Scope Address) (index : Fin width) : Prop :=
  scope = current bank ∧ bank.phase = .provisioning ∧ (bank.guards index).isNone = true

def seedIfLive [DecidableEq Address] (bank : Bank Address Payload width) (scope : Scope Address)
    (index : Fin width) : Option (Bank Address Payload width) :=
  if scope = current bank ∧ bank.phase = .provisioning ∧ (bank.guards index).isNone = true then
    some (withGuard bank index (some (vacantGuard scope index)))
  else none

theorem a_guard_is_created_only_under_the_current_provisioning_scope [DecidableEq Address]
    {bank next : Bank Address Payload width} {scope : Scope Address} {index : Fin width}
    (created : seedIfLive bank scope index = some next) :
    CanSeed bank scope index ∧ next = withGuard bank index (some (vacantGuard scope index)) := by
  unfold seedIfLive at created
  split at created
  next allowed =>
    cases created
    exact ⟨allowed, rfl⟩
  next => simp at created

structure Rules (Address : Type) (width : Nat) where
  bankFunded : Scope Address → Prop
  closing : Scope Address → Prop
  auxiliaryClosed : Scope Address → Prop
  childFunded : StorageBoundary.Binding (ChildAddress Address width) → Prop
  childClosing : StorageBoundary.Binding (ChildAddress Address width) → Prop

def AllMissing (bank : Bank Address Payload width) : Prop :=
  ∀ index, bank.guards index = none

structure Sound (bank : Bank Address Payload width) : Prop where
  vacant : bank.phase = .vacant → AllMissing bank
  exactGuard : ∀ index guard, bank.guards index = some guard → guard.location = (current bank, index)
  ready : bank.phase = .serving → ∀ index, ∃ guard, bank.guards index = some guard

inductive Step [DecidableEq Address] (rules : Rules Address width) :
    Bank Address Payload width → Bank Address Payload width → Prop
  | reserve {bank} (vacant : bank.phase = .vacant) (paid : rules.bankFunded ⟨bank.address, bank.issued + 1⟩) :
      Step rules bank {bank with issued := bank.issued + 1, phase := .provisioning}
  | seed {bank next} (scope : Scope Address) (index : Fin width)
      (created : seedIfLive bank scope index = some next) :
      Step rules bank next
  | publish {bank} (provisioning : bank.phase = .provisioning)
      (ready : ∀ index, ∃ guard, bank.guards index = some guard) :
      Step rules bank {bank with phase := .serving}
  | close {bank} (live : bank.phase ≠ .vacant) (authorized : rules.closing (current bank)) :
      Step rules bank {bank with phase := .sealed}
  | child {bank} (index : Fin width) {guard after : Guard Address Payload width}
      (located : bank.guards index = some guard)
      (effect : StorageBoundary.Step (fun permit => bank.phase = .serving ∧ rules.childFunded permit)
        rules.childClosing guard after) :
      Step rules bank (withGuard bank index (some after))
  | releaseGuard {bank} (index : Fin width) {guard : Guard Address Payload width}
      (located : bank.guards index = some guard) (closed : bank.phase = .sealed)
      (retired : guard.body = .vacant) :
      Step rules bank (withGuard bank index none)
  | finish {bank} (live : bank.phase ≠ .vacant) (authorized : rules.closing (current bank))
      (empty : AllMissing bank) (settled : rules.auxiliaryClosed (current bank)) :
      Step rules bank {bank with phase := .vacant}
  | restart {bank} : Step rules bank bank

variable [DecidableEq Address]
variable {rules : Rules Address width}

theorem the_guard_inventory_is_exact_and_never_partial_when_serving {bank next : Bank Address Payload width}
    (safe : Sound bank) (step : Step rules bank next) : Sound next := by
  cases step with
  | reserve vacant _ =>
      refine ⟨?_, ?_, ?_⟩
      · intro impossible
        cases impossible
      · intro index guard present
        have empty := safe.vacant vacant index
        rw [empty] at present
        cases present
      · intro impossible
        cases impossible
  | seed scope index created =>
      obtain ⟨⟨sameScope, provisioning, _⟩, rfl⟩ :=
        a_guard_is_created_only_under_the_current_provisioning_scope created
      refine ⟨?_, ?_, ?_⟩
      · intro vacant
        change bank.phase = .vacant at vacant
        rw [provisioning] at vacant
        cases vacant
      · intro other guard present
        by_cases same : other = index
        · subst other
          have shape : vacantGuard scope index = guard := by simpa [withGuard] using present
          subst guard
          exact congrArg (fun root => (root, index)) sameScope
        · exact safe.exactGuard other guard (by simpa [withGuard, same] using present)
      · intro serving
        change bank.phase = .serving at serving
        rw [provisioning] at serving
        cases serving
  | publish _ ready =>
      refine ⟨?_, safe.exactGuard, fun _ => ready⟩
      intro impossible
      cases impossible
  | close =>
      refine ⟨?_, safe.exactGuard, ?_⟩ <;> intro impossible <;> cases impossible
  | @child index beforeGuard afterGuard located effect =>
      refine ⟨?_, ?_, ?_⟩
      · intro vacant
        have missing := safe.vacant vacant index
        rw [missing] at located
        cases located
      · intro other guard present
        by_cases same : other = index
        · subst other
          have eqGuard : afterGuard = guard := by simpa [withGuard] using present
          subst guard
          exact (StorageBoundary.slot_changes_preserve_location_and_monotone_issuance effect).1.trans
            (safe.exactGuard index beforeGuard located)
        · exact safe.exactGuard other guard (by simpa [withGuard, same] using present)
      · intro serving other
        by_cases same : other = index
        · subst other
          exact ⟨afterGuard, by simp [withGuard]⟩
        · obtain ⟨guard, present⟩ := safe.ready serving other
          exact ⟨guard, by simpa [withGuard, same] using present⟩
  | releaseGuard index _ closed _ =>
      refine ⟨?_, ?_, ?_⟩
      · intro vacant
        change bank.phase = .vacant at vacant
        rw [closed] at vacant
        cases vacant
      · intro other guard present
        by_cases same : other = index
        · simp [withGuard, same] at present
        · exact safe.exactGuard other guard (by simpa [withGuard, same] using present)
      · intro serving
        change bank.phase = .serving at serving
        rw [closed] at serving
        cases serving
  | finish _ _ empty _ =>
      refine ⟨fun _ => empty, safe.exactGuard, ?_⟩
      intro impossible
      cases impossible
  | restart => exact safe

def Retired (bank : Bank Address Payload width) (scope : Scope Address) : Prop :=
  scope.address = bank.address ∧ 0 < scope.serial ∧
    (scope.serial < bank.issued ∨ scope.serial = bank.issued ∧ bank.phase = .vacant)

private theorem a_retired_scope_cannot_seed {bank : Bank Address Payload width}
    {scope : Scope Address} (retired : Retired bank scope) (index : Fin width) :
    seedIfLive bank scope index = none := by
  cases seeded : seedIfLive bank scope index with
  | none => rfl
  | some _ =>
      have allowed := (a_guard_is_created_only_under_the_current_provisioning_scope seeded).1
      rcases retired.2.2 with older | ⟨_, vacant⟩
      · have same := congrArg Scope.serial allowed.1
        change scope.serial = bank.issued at same
        omega
      · have active := allowed.2.1
        rw [vacant] at active
        cases active

private theorem progress_preserves_root_and_watermark {bank next : Bank Address Payload width}
    (step : Step rules bank next) : next.address = bank.address ∧ bank.issued ≤ next.issued := by
  cases step with
  | reserve => exact ⟨rfl, Nat.le_succ _⟩
  | seed _ _ created =>
      obtain ⟨_, rfl⟩ := a_guard_is_created_only_under_the_current_provisioning_scope created
      exact ⟨rfl, Nat.le_refl _⟩
  | publish | close | child | releaseGuard | finish | restart => exact ⟨rfl, Nat.le_refl _⟩

private theorem a_retired_scope_stays_retired {bank next : Bank Address Payload width}
    {scope : Scope Address} (retired : Retired bank scope) (step : Step rules bank next) :
    Retired next scope := by
  have stable := progress_preserves_root_and_watermark step
  refine ⟨retired.1.trans stable.1.symm, retired.2.1, ?_⟩
  rcases retired.2.2 with older | ⟨currentSerial, vacant⟩
  · exact .inl (Nat.lt_of_lt_of_le older stable.2)
  · cases step with
    | reserve => exact .inl (currentSerial ▸ Nat.lt_succ_self _)
    | seed _ _ created =>
        have active := (a_guard_is_created_only_under_the_current_provisioning_scope created).1.2.1
        rw [vacant] at active
        cases active
    | publish active _ => rw [vacant] at active; cases active
    | close live _ => exact False.elim (live vacant)
    | child | restart => exact .inr ⟨currentSerial, vacant⟩
    | releaseGuard _ _ closed _ => rw [vacant] at closed; cases closed
    | finish => exact .inr ⟨currentSerial, rfl⟩

inductive Trace (rules : Rules Address width) :
    Bank Address Payload width → Bank Address Payload width → Prop
  | same (bank) : Trace rules bank bank
  | next {start before after} :
      Trace rules start before → Step rules before after → Trace rules start after

theorem a_terminal_namespace_rejects_late_creates_across_restart_and_reuse
    {first last : Bank Address Payload width} {scope : Scope Address}
    (retired : Retired first scope) (trace : Trace rules first last) (index : Fin width) :
    Retired last scope ∧ seedIfLive last scope index = none := by
  have permanent : Retired last scope := by
    induction trace with
    | same => exact retired
    | next _ step prior => exact a_retired_scope_stays_retired prior step
  exact ⟨permanent, a_retired_scope_cannot_seed permanent index⟩

omit [DecidableEq Address] in
theorem a_retired_namespace_has_no_guard_at_any_planned_address
    {bank : Bank Address Payload width} {scope : Scope Address}
    (safe : Sound bank) (retired : Retired bank scope) (index : Fin width)
    (guard : Guard Address Payload width) (old : guard.location = (scope, index)) :
    bank.guards index ≠ some guard := by
  intro present
  rcases retired.2.2 with older | ⟨_, vacant⟩
  · have same : scope = current bank := congrArg Prod.fst (old.symm.trans (safe.exactGuard index guard present))
    have serial := congrArg Scope.serial same
    change scope.serial = bank.issued at serial
    omega
  · rw [safe.vacant vacant index] at present
    cases present

theorem a_sealed_bank_cannot_arm_new_child_payload_work {bank : Bank Address Payload width}
    {guard after : Guard Address Payload width} (sealed : bank.phase = .sealed)
    (effect : StorageBoundary.Step (fun permit => bank.phase = .serving ∧ rules.childFunded permit)
      rules.childClosing guard after) :
    after.issued = guard.issued := by
  cases effect with
  | arm _ paid =>
      have active := paid.1
      rw [sealed] at active
      cases active
  | put _ _ accepted =>
      obtain ⟨_, rfl⟩ := StorageBoundary.a_successful_put_uses_the_live_scoped_permission accepted
      rfl
  | fence | clear | restart => rfl

theorem an_empty_guard_keeps_every_issued_child_write_closed {guard : Guard Address Payload width}
    (empty : guard.body = .vacant) (serial : Nat) (issued : serial ≤ guard.issued) (positive : 0 < serial) :
    ProviderIOClosure.StableAbsence (StorageBoundary.provider guard ⟨guard.location, serial⟩) := by
  apply StorageBoundary.a_retired_slot_body_has_stable_absence
  refine ⟨rfl, positive, ?_⟩
  rcases Nat.lt_or_eq_of_le issued with earlier | equal
  · exact .inl earlier
  · exact .inr ⟨equal, empty⟩

def Terminal (rules : Rules Address width) (bank : Bank Address Payload width) (scope : Scope Address) : Prop :=
  Retired bank scope ∧ rules.auxiliaryClosed scope

theorem finishing_a_live_namespace_requires_exact_auxiliary_evidence
    {bank next : Bank Address Payload width} (wasLive : bank.phase ≠ .vacant)
    (finished : next.phase = .vacant) (step : Step rules bank next) :
    rules.auxiliaryClosed (current bank) := by
  cases step with
  | reserve | publish | close => cases finished
  | seed _ _ created =>
      obtain ⟨_, rfl⟩ := a_guard_is_created_only_under_the_current_provisioning_scope created
      exact False.elim (wasLive finished)
  | child | releaseGuard | restart => exact False.elim (wasLive finished)
  | finish _ _ _ settled => exact settled

theorem an_exact_empty_bank_can_close_before_any_seed_reply
    {bank : Bank Address Payload width} (live : bank.phase ≠ .vacant) (positive : 0 < bank.issued)
    (allowed : rules.closing (current bank)) (empty : AllMissing bank)
    (settled : rules.auxiliaryClosed (current bank)) :
    ∃ next, Step rules bank next ∧ Terminal rules next (current bank) := by
  exact ⟨{bank with phase := .vacant}, .finish live allowed empty settled,
    ⟨⟨rfl, positive, .inr ⟨rfl, rfl⟩⟩, settled⟩⟩

theorem terminal_evidence_keeps_the_original_scope_after_replacement
    {first last : Bank Address Payload width} {scope : Scope Address}
    (retired : Terminal rules first scope) (trace : Trace rules first last) :
    Terminal rules last scope := by
  have permanent : Retired last scope := by
    induction trace with
    | same => exact retired.1
    | next _ step prior => exact a_retired_scope_stays_retired prior step
  exact ⟨permanent, retired.2⟩

omit [DecidableEq Address] in
theorem exact_terminal_scope_can_settle_its_incarnation [DecidableEq Ticket]
    {bank : Bank Address Payload width} {scope : Nat} {state : PoolIncarnations.State Ticket}
    (terminal : Terminal rules bank ⟨bank.address, scope⟩)
    (enrolled : scope ∈ state.registry) (offline : (state.access scope).phase = .offline)
    {limit : Nat} {layout : SharedExtentAccounting.Layout Nat} {needs : SharedCustody.Dependencies}
    {closeAllowed : Nat → Prop} {reserve : ProviderIOClosure.Custody Ticket → Prop}
    {expected : SharedExtentAccounting.State Nat Ticket → Nat → Book}
    {authenticated : PoolIncarnations.Validation Book → Prop}
    (clear : PoolIncarnations.Uncharged layout state scope) :
    PoolIncarnations.Step limit layout needs closeAllowed reserve expected authenticated
      (fun id => Terminal rules bank ⟨bank.address, id⟩) state .settle (PoolIncarnations.forget state scope) :=
  .settle scope enrolled offline terminal clear

#print axioms a_guard_is_created_only_under_the_current_provisioning_scope
#print axioms the_guard_inventory_is_exact_and_never_partial_when_serving
#print axioms a_terminal_namespace_rejects_late_creates_across_restart_and_reuse
#print axioms a_retired_namespace_has_no_guard_at_any_planned_address
#print axioms a_sealed_bank_cannot_arm_new_child_payload_work
#print axioms an_empty_guard_keeps_every_issued_child_write_closed
#print axioms finishing_a_live_namespace_requires_exact_auxiliary_evidence
#print axioms an_exact_empty_bank_can_close_before_any_seed_reply
#print axioms terminal_evidence_keeps_the_original_scope_after_replacement
#print axioms exact_terminal_scope_can_settle_its_incarnation

end NamespaceClosure
