import SharedCustody
import ProviderIOClosure

set_option warningAsError true

namespace SharedExtentAccounting

open SnapshotAdmission (setSlot)

variable {Pool Ticket : Type}

structure Layout (Pool : Type) where
  pool : Nat → Pool
  bytes : Nat → Nat
  limit : Pool → Nat

def allocationBytes [DecidableEq Pool] (layout : Layout Pool) (pool : Pool) (version : Nat) : Nat :=
  if layout.pool version = pool then layout.bytes version else 0

def charges [DecidableEq Pool] (layout : Layout Pool) (pool : Pool) (versions : List Nat) : Nat :=
  (versions.map (allocationBytes layout pool)).sum

structure State (Pool Ticket : Type) where
  ordinary : Pool → Nat
  debits : List Nat
  issued : Nat
  catalog : SharedCustody.Store
  provider : Nat → ProviderIOClosure.State Ticket
  opening : Nat → Bool

def Used [DecidableEq Pool] (layout : Layout Pool) (state : State Pool Ticket) (pool : Pool) : Nat :=
  state.ordinary pool + charges layout pool state.debits

def PhysicalWork (provider : ProviderIOClosure.State Ticket) : Prop :=
  provider.present = true ∨ ∃ ticket, ProviderIOClosure.MayWrite provider ticket

structure Sound [DecidableEq Pool] (layout : Layout Pool) (needs : SharedCustody.Dependencies)
    (state : State Pool Ticket) : Prop where
  fit : ∀ pool, Used layout state pool ≤ layout.limit pool
  unique : state.debits.Nodup
  known : ∀ version ∈ state.debits, version ≤ state.issued
  covered : SharedCustody.Covered needs state.catalog
  providerSound : ∀ version, ProviderIOClosure.Sound (state.provider version)
  available : ∀ version, state.catalog.physical version = true → (state.provider version).present = true
  paid : ∀ version, PhysicalWork (state.provider version) → version ∈ state.debits

def expose (store : SharedCustody.Store) (version : Nat) : SharedCustody.Store :=
  {store with gates := setSlot store.gates version .open,
              physical := setSlot store.physical version true}

def CanRefund (state : State Pool Ticket) (version evidence : Nat) : Prop :=
  evidence = version ∧ (state.provider evidence).erased = true

theorem a_receipt_for_another_version_cannot_return_this_debit {state : State Pool Ticket}
    {version evidence : Nat} (allowed : CanRefund state version evidence) : evidence = version := by
  exact allowed.1

inductive Step [DecidableEq Pool] [DecidableEq Ticket] (layout : Layout Pool) (needs : SharedCustody.Dependencies)
    (closeAllowed : Nat → Prop) (reserve : ProviderIOClosure.Custody Ticket → Prop) :
    State Pool Ticket → State Pool Ticket → Prop
  | ordinary {state} (next : Pool → Nat)
      (fits : ∀ pool, next pool + charges layout pool state.debits ≤ layout.limit pool) :
      Step layout needs closeAllowed reserve state {state with ordinary := next}
  | allocate {state} (version : Nat) (next : version = state.issued + 1)
      (empty : state.catalog.physical version = false)
      (fits : ∀ pool, Used layout state pool + allocationBytes layout pool version ≤ layout.limit pool) :
      Step layout needs closeAllowed reserve state
        {state with
          debits := version :: state.debits
          issued := version
          provider := setSlot state.provider version ProviderIOClosure.initial
          opening := setSlot state.opening version true}
  | providerEvent {state next} (version : Nat) (charged : version ∈ state.debits)
      (effect : ProviderIOClosure.Step reserve (state.provider version) next)
      (serving : state.catalog.physical version = true → next.present = true) :
      Step layout needs closeAllowed reserve state {state with provider := setSlot state.provider version next}
  | publish {state} (version : Nat) (once : state.opening version = true)
      (charged : version ∈ state.debits) (materialized : (state.provider version).present = true) :
      Step layout needs closeAllowed reserve state
        {state with catalog := expose state.catalog version, opening := setSlot state.opening version false}
  | references {state next} (change : SharedCustody.Step needs closeAllowed state.catalog next) :
      Step layout needs closeAllowed reserve state {state with catalog := next}
  | refund {state} (version evidence : Nat) (verified : CanRefund state version evidence) :
      Step layout needs closeAllowed reserve state
        {state with debits := state.debits.filter (· != version)}
  | recover {state} : Step layout needs closeAllowed reserve state state

private theorem exposing_an_exact_version_preserves_custody {store : SharedCustody.Store}
    {needs : SharedCustody.Dependencies} (sound : SharedCustody.Covered needs store) (version : Nat) :
    SharedCustody.Covered needs (expose store version) := by
  constructor
  · exact sound.complete
  · intro root query held
    by_cases same : query = version
    · simp [expose, setSlot, same]
    · simpa [expose, setSlot, same] using sound.referenceGate root query held
  · intro query borrowed
    by_cases same : query = version
    · simp [expose, setSlot, same]
    · simpa [expose, setSlot, same] using sound.borrowGate query borrowed
  · intro query openGate
    by_cases same : query = version
    · simp [expose, setSlot, same]
    · have original : store.gates query ≠ .gone := by simpa [expose, setSlot, same] using openGate
      simpa [expose, setSlot, same] using sound.bytes query original

private theorem reference_changes_do_not_create_bytes {store next : SharedCustody.Store}
    {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop}
    (change : SharedCustody.Step needs closeAllowed store next) (version : Nat)
    (present : next.physical version = true) : store.physical version = true := by
  cases change with
  | erase erased _ =>
      by_cases same : version = erased
      · simp [setSlot, same] at present
      · simpa [setSlot, same] using present
  | _ => exact present

private theorem filtering_removes_only_its_charge [DecidableEq Pool]
    (layout : Layout Pool) (pool : Pool) (version : Nat) (versions : List Nat) :
    charges layout pool (versions.filter (· != version)) ≤ charges layout pool versions := by
  induction versions with
  | nil => simp [charges]
  | cons value remaining prior =>
      by_cases same : value = version
      · subst value
        simp [charges] at prior ⊢
        omega
      · simp [charges, same] at prior ⊢
        omega

private theorem stable_absence_leaves_no_physical_work (state : ProviderIOClosure.State Ticket)
    (absent : ProviderIOClosure.StableAbsence state) : ¬ PhysicalWork state := by
  intro work
  rcases work with present | ⟨ticket, pending⟩
  · exact Bool.false_ne_true (absent.2.1.symm.trans present)
  · exact absent.2.2 ticket pending

theorem numeric_and_custody_invariants_hold_after_each_step [DecidableEq Pool] [DecidableEq Ticket]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop}
    {reserve : ProviderIOClosure.Custody Ticket → Prop} {before after : State Pool Ticket}
    (safe : Sound layout needs before) (step : Step layout needs closeAllowed reserve before after) :
    Sound layout needs after := by
  cases step with
  | ordinary _ fits => exact ⟨fits, safe.unique, safe.known, safe.covered, safe.providerSound, safe.available, safe.paid⟩
  | allocate version fresh empty fits =>
      have notCharged : version ∉ before.debits := by
        intro member
        have bound := safe.known version member
        omega
      refine ⟨?_, List.nodup_cons.mpr ⟨notCharged, safe.unique⟩, ?_,
        safe.covered, ?_, ?_, ?_⟩
      · intro pool
        simpa [Used, charges, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits pool
      · intro query member
        rcases List.mem_cons.mp member with rfl | older
        · exact Nat.le_refl _
        · have prior := safe.known query older
          change query ≤ version
          omega
      · intro query
        by_cases same : query = version
        · simpa [setSlot, same] using (ProviderIOClosure.initial_sound : ProviderIOClosure.Sound
            (ProviderIOClosure.initial : ProviderIOClosure.State Ticket))
        · simpa [setSlot, same] using safe.providerSound query
      · intro query present
        by_cases same : query = version
        · subst query
          rw [empty] at present
          cases present
        · simpa [setSlot, same] using safe.available query present
      · intro query work
        by_cases same : query = version
        · subst query
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (safe.paid query (by simpa [setSlot, same] using work))
  | providerEvent version charged effect serving =>
      refine ⟨safe.fit, safe.unique, safe.known, safe.covered, ?_, ?_, ?_⟩
      · intro query
        by_cases same : query = version
        · simpa [setSlot, same] using ProviderIOClosure.sound_step (safe.providerSound version) effect
        · simpa [setSlot, same] using safe.providerSound query
      · intro query present
        by_cases same : query = version
        · subst query
          simpa [setSlot] using serving present
        · simpa [setSlot, same] using safe.available query present
      · intro query work
        by_cases same : query = version
        · subst query
          exact charged
        · exact safe.paid query (by simpa [setSlot, same] using work)
  | publish version _ _ materialized =>
      refine ⟨safe.fit, safe.unique, safe.known, exposing_an_exact_version_preserves_custody safe.covered version,
        safe.providerSound, ?_, safe.paid⟩
      intro query present
      by_cases same : query = version
      · subst query
        exact materialized
      · apply safe.available query
        simpa [expose, setSlot, same] using present
  | references change =>
      exact ⟨safe.fit, safe.unique, safe.known, SharedCustody.every_step_keeps_dependencies safe.covered change,
        safe.providerSound, fun version present => safe.available version
          (reference_changes_do_not_create_bytes change version present), safe.paid⟩
  | refund version evidence verified =>
      have same := a_receipt_for_another_version_cannot_return_this_debit verified
      have erased : (before.provider version).erased = true := same ▸ verified.2
      have noWork := stable_absence_leaves_no_physical_work _ ((safe.providerSound version).erasure erased)
      refine ⟨?_, safe.unique.filter _, ?_, safe.covered, safe.providerSound, safe.available, ?_⟩
      · intro pool
        have kept := filtering_removes_only_its_charge layout pool version before.debits
        exact Nat.le_trans (Nat.add_le_add_left kept _) (safe.fit pool)
      · intro query member
        exact safe.known query (List.mem_filter.mp member).1
      · intro query work
        have different : query ≠ version := by
          intro sameVersion
          exact noWork (sameVersion ▸ work)
        exact List.mem_filter.mpr ⟨safe.paid query work, by simp [different]⟩
  | recover => exact safe

inductive Trace [DecidableEq Pool] [DecidableEq Ticket] (layout : Layout Pool)
    (needs : SharedCustody.Dependencies) (closeAllowed : Nat → Prop)
    (reserve : ProviderIOClosure.Custody Ticket → Prop) : State Pool Ticket → State Pool Ticket → Prop
  | same (state) : Trace layout needs closeAllowed reserve state state
  | next {first before after} : Trace layout needs closeAllowed reserve first before →
      Step layout needs closeAllowed reserve before after → Trace layout needs closeAllowed reserve first after

theorem arbitrary_admitted_traces_preserve_exact_physical_capacity [DecidableEq Pool] [DecidableEq Ticket]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop}
    {reserve : ProviderIOClosure.Custody Ticket → Prop} {first last : State Pool Ticket}
    (safe : Sound layout needs first) (trace : Trace layout needs closeAllowed reserve first last) :
    Sound layout needs last := by
  induction trace with
  | same => exact safe
  | next _ step prior => exact numeric_and_custody_invariants_hold_after_each_step prior step

theorem a_live_checkpoint_or_evidence_root_has_charged_provider_bytes [DecidableEq Pool]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {state : State Pool Ticket}
    (safe : Sound layout needs state) {root version : Nat}
    (live : state.catalog.roots root = .live) (depends : needs root version) :
    (state.provider version).present = true ∧ version ∈ state.debits := by
  have physical := safe.available version (SharedCustody.live_manifest_has_exact_version safe.covered live depends)
  exact ⟨physical, safe.paid version (.inl physical)⟩

theorem a_read_borrow_preserves_its_debit_without_a_live_root [DecidableEq Pool]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {state : State Pool Ticket}
    (safe : Sound layout needs state) {version : Nat} (borrowed : 0 < state.catalog.borrows version) :
    (state.provider version).present = true ∧ version ∈ state.debits := by
  have physical := safe.available version (SharedCustody.retained_borrow_has_exact_version safe.covered borrowed)
  exact ⟨physical, safe.paid version (.inl physical)⟩

theorem an_old_borrow_blocks_return_of_its_physical_debit [DecidableEq Pool]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {state : State Pool Ticket}
    (safe : Sound layout needs state) {version evidence : Nat}
    (borrowed : 0 < state.catalog.borrows version) : ¬ CanRefund state version evidence := by
  intro allowed
  have matchesVersion := a_receipt_for_another_version_cannot_return_this_debit allowed
  have erased : (state.provider version).erased = true := matchesVersion ▸ allowed.2
  have absent := (safe.providerSound version).erasure erased
  have present := (a_read_borrow_preserves_its_debit_without_a_live_root safe borrowed).1
  exact Bool.false_ne_true (absent.2.1.symm.trans present)

theorem another_exact_reference_can_be_added_at_full_byte_capacity [DecidableEq Pool] [DecidableEq Ticket]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop}
    {reserve : ProviderIOClosure.Custody Ticket → Prop} {state : State Pool Ticket}
    (safe : Sound layout needs state) {root version : Nat}
    (dependency : needs root version) (prepared : state.catalog.roots root ≠ .fresh)
    (unused : state.catalog.refs root version = .unused) (admitting : state.catalog.gates version = .open) :
    ∃ next, Step layout needs closeAllowed reserve state next ∧ Sound layout needs next ∧
      next.catalog.refs root version = .held ∧ ∀ pool, Used layout next pool = Used layout state pool := by
  let registered := SharedCustody.setReference state.catalog.refs root version .held
  let next := {state with catalog := {state.catalog with refs := registered}}
  have acquired : Step layout needs closeAllowed reserve state next :=
    .references (.acquire root version dependency prepared unused admitting)
  exact ⟨next, acquired, numeric_and_custody_invariants_hold_after_each_step safe acquired,
    by simp [next, registered, SharedCustody.setReference, setSlot], fun _ => rfl⟩

theorem a_new_allocation_uses_its_own_pointwise_charge [DecidableEq Pool] [DecidableEq Ticket]
    {layout : Layout Pool} {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop}
    {reserve : ProviderIOClosure.Custody Ticket → Prop} {state : State Pool Ticket}
    (safe : Sound layout needs state) (version : Nat)
    (fresh : version = state.issued + 1) (empty : state.catalog.physical version = false)
    (fits : ∀ pool, Used layout state pool + allocationBytes layout pool version ≤ layout.limit pool) :
    ∃ next, Step layout needs closeAllowed reserve state next ∧ Sound layout needs next ∧
      ∀ pool, Used layout next pool = Used layout state pool + allocationBytes layout pool version := by
  let next := {state with
    debits := version :: state.debits
    issued := version
    provider := setSlot state.provider version ProviderIOClosure.initial
    opening := setSlot state.opening version true}
  have reserved : Step layout needs closeAllowed reserve state next :=
    .allocate version fresh empty fits
  refine ⟨next, reserved, numeric_and_custody_invariants_hold_after_each_step safe reserved, ?_⟩
  intro pool
  simp [next, Used, charges, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

#print axioms a_receipt_for_another_version_cannot_return_this_debit
#print axioms numeric_and_custody_invariants_hold_after_each_step
#print axioms arbitrary_admitted_traces_preserve_exact_physical_capacity
#print axioms a_live_checkpoint_or_evidence_root_has_charged_provider_bytes
#print axioms a_read_borrow_preserves_its_debit_without_a_live_root
#print axioms an_old_borrow_blocks_return_of_its_physical_debit
#print axioms another_exact_reference_can_be_added_at_full_byte_capacity
#print axioms a_new_allocation_uses_its_own_pointwise_charge

end SharedExtentAccounting
