import RecoveryCapacity

set_option warningAsError true

namespace CapacityLedger

variable {Scope Pool : Type}

structure Profile (Pool : Type) where
  residency : Pool → Nat
  workspace : Pool → Nat
  resident : Pool → Nat
  obsolete : Pool → Nat
  residentFits : ∀ pool, resident pool ≤ residency pool
  obsoleteFits : ∀ pool, obsolete pool ≤ workspace pool

inductive Phase where
  | funded
  | sealed
  | installed (keepsOld : Bool)
  | aborted
  deriving DecidableEq

structure Entry (Scope Pool : Type) where
  scope : Scope
  profile : Profile Pool
  phase : Phase

def charge (entry : Entry Scope Pool) (pool : Pool) : Nat :=
  match entry.phase with
  | .funded | .sealed => entry.profile.residency pool + entry.profile.workspace pool
  | .installed true => entry.profile.resident pool + entry.profile.obsolete pool
  | .installed false => entry.profile.resident pool
  | .aborted => 0

def load : List (Entry Scope Pool) → Pool → Nat
  | [], _ => 0
  | entry :: remaining, pool => charge entry pool + load remaining pool

theorem load_concat (left right : List (Entry Scope Pool)) (pool : Pool) :
    load (left ++ right) pool = load left pool + load right pool := by
  induction left with
  | nil => simp [load]
  | cons entry remaining prior => simp [load, prior, Nat.add_assoc]

def CanRelease (disposed : Scope → Prop) (receipt : Scope) (entry : Entry Scope Pool) : Prop :=
  receipt = entry.scope ∧ disposed receipt

inductive Advance (installed disposed : Scope → Prop) :
    Entry Scope Pool → Entry Scope Pool → Prop
  | authorizeSeal {entry} (funded : entry.phase = .funded) :
      Advance installed disposed entry {entry with phase := .sealed}
  | abort {entry} (funded : entry.phase = .funded) :
      Advance installed disposed entry {entry with phase := .aborted}
  | promote {entry} (sealed : entry.phase = .sealed) (certified : installed entry.scope) :
      Advance installed disposed entry {entry with phase := .installed true}
  | release {entry} (held : entry.phase = .installed true) (receipt : Scope)
      (exactDisposition : CanRelease disposed receipt entry) :
      Advance installed disposed entry {entry with phase := .installed false}

theorem a_disposition_releases_only_its_own_scope {disposed : Scope → Prop}
    {receipt : Scope} {entry : Entry Scope Pool} (proof : CanRelease disposed receipt entry) :
    receipt = entry.scope := by
  exact proof.1

theorem scope_is_immutable_across_a_move {installed disposed : Scope → Prop} {before after : Entry Scope Pool}
    (step : Advance installed disposed before after) : before.scope = after.scope := by
  cases step <;> rfl

theorem spending_a_reservation_never_needs_extra_space {installed disposed : Scope → Prop}
    {before after : Entry Scope Pool} (step : Advance installed disposed before after) :
    ∀ pool, charge after pool ≤ charge before pool := by
  intro pool
  cases step with
  | authorizeSeal funded => simp [charge, funded]
  | abort funded => simp [charge, funded]
  | promote sealed _ =>
      simpa [charge, sealed] using Nat.add_le_add
        (before.profile.residentFits pool) (before.profile.obsoleteFits pool)
  | release held _ _ => simp [charge, held]

theorem a_sealed_move_is_promoted_with_its_obsolete_charge {installed disposed : Scope → Prop}
    {before after : Entry Scope Pool} (sealed : before.phase = .sealed)
    (step : Advance installed disposed before after) :
    after.phase = .installed true ∧
    ∀ pool, charge after pool = before.profile.resident pool + before.profile.obsolete pool := by
  cases step with
  | authorizeSeal funded => simp [sealed] at funded
  | abort funded => simp [sealed] at funded
  | promote _ _ => exact ⟨rfl, fun _ => rfl⟩
  | release held _ _ => simp [sealed] at held

structure Ledger (Scope Pool : Type) where
  ordinary : Pool → Nat
  moves : List (Entry Scope Pool)

def usage (ledger : Ledger Scope Pool) (pool : Pool) : Nat :=
  ledger.ordinary pool + load ledger.moves pool

def CanAdmit (limit : Pool → Nat) (ledger : Ledger Scope Pool) (row : Entry Scope Pool) : Prop :=
  ∀ pool, usage ledger pool + charge row pool ≤ limit pool

structure Sound (limit : Pool → Nat) (ledger : Ledger Scope Pool) : Prop where
  fits : ∀ pool, usage ledger pool ≤ limit pool
  unique : (ledger.moves.map Entry.scope).Nodup

inductive Step (limit : Pool → Nat) (installed disposed : Scope → Prop) :
    Ledger Scope Pool → Option Scope → Ledger Scope Pool → Prop
  | ordinary {ledger} (next : Pool → Nat) (fits : ∀ pool, next pool + load ledger.moves pool ≤ limit pool) :
      Step limit installed disposed ledger none {ledger with ordinary := next}
  | admit {ledger} (entry : Entry Scope Pool) (pending : entry.phase = .funded)
      (fresh : entry.scope ∉ ledger.moves.map Entry.scope) (fits : CanAdmit limit ledger entry) :
      Step limit installed disposed ledger (some entry.scope) {ledger with moves := entry :: ledger.moves}
  | advance {ordinary} {prior later : List (Entry Scope Pool)} {entry next : Entry Scope Pool}
      (lawful : Advance installed disposed entry next) :
      Step limit installed disposed ⟨ordinary, prior ++ entry :: later⟩ (some entry.scope)
        ⟨ordinary, prior ++ next :: later⟩
  | restart {ledger} : Step limit installed disposed ledger none ledger

inductive Trace (limit : Pool → Nat) (installed disposed : Scope → Prop) :
    Ledger Scope Pool → Ledger Scope Pool → Prop
  | same (ledger) : Trace limit installed disposed ledger ledger
  | next {first before after changed} : Trace limit installed disposed first before →
      Step limit installed disposed before changed after → Trace limit installed disposed first after

theorem every_pool_fits_after_vector_admission {limit : Pool → Nat} {ledger : Ledger Scope Pool}
    {entry : Entry Scope Pool} (fits : CanAdmit limit ledger entry) :
    ∀ pool, usage {ledger with moves := entry :: ledger.moves} pool ≤ limit pool := by
  intro pool
  have within : usage ledger pool + charge entry pool ≤ limit pool := by
    exact fits pool
  simpa [usage, load, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using within

theorem every_transition_preserves_each_capacity_and_unique_scope
    {limit : Pool → Nat} {installed disposed : Scope → Prop} {before after : Ledger Scope Pool}
    {changed : Option Scope} (sound : Sound limit before)
    (step : Step limit installed disposed before changed after) : Sound limit after := by
  cases step with
  | ordinary _ fits => exact ⟨fits, sound.unique⟩
  | admit entry _ fresh fits =>
      exact ⟨every_pool_fits_after_vector_admission fits, List.nodup_cons.mpr ⟨fresh, sound.unique⟩⟩
  | advance lawful =>
      refine ⟨?_, ?_⟩
      · intro pool
        have beforeFit := sound.fits pool
        have down := spending_a_reservation_never_needs_extra_space lawful pool
        simp only [usage, load_concat, load] at *
        omega
      · simpa only [List.map_append, List.map_cons, ← scope_is_immutable_across_a_move lawful] using sound.unique
  | restart => exact sound

theorem arbitrary_interleavings_preserve_each_capacity
    {limit : Pool → Nat} {installed disposed : Scope → Prop} {first last : Ledger Scope Pool}
    (sound : Sound limit first) (trace : Trace limit installed disposed first last) : Sound limit last := by
  induction trace with
  | same => exact sound
  | next _ step prior => exact every_transition_preserves_each_capacity_and_unique_scope prior step

theorem other_scopes_cannot_change_an_existing_reservation
    {limit : Pool → Nat} {installed disposed : Scope → Prop} {before after : Ledger Scope Pool}
    {changed : Option Scope} {entry : Entry Scope Pool} (held : entry ∈ before.moves)
    (unrelated : changed ≠ some entry.scope) (step : Step limit installed disposed before changed after) :
    entry ∈ after.moves := by
  cases step with
  | ordinary _ _ => exact held
  | admit _ _ _ _ => exact List.mem_cons_of_mem _ held
  | advance lawful =>
      rcases List.mem_append.mp held with earlier | later
      · exact List.mem_append.mpr (.inl earlier)
      · rcases List.mem_cons.mp later with same | tail
        · subst entry
          exact False.elim (unrelated rfl)
        · exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ tail))
  | restart => exact held

theorem a_funded_scope_can_promote_without_rebilling
    {limit : Pool → Nat} {installed disposed : Scope → Prop} {ledger : Ledger Scope Pool}
    {entry : Entry Scope Pool} (funded : entry ∈ ledger.moves) (sealed : entry.phase = .sealed)
    (certified : installed entry.scope) (sound : Sound limit ledger) :
    ∃ after, Step limit installed disposed ledger (some entry.scope) after ∧ Sound limit after ∧
      {entry with phase := .installed true} ∈ after.moves := by
  obtain ⟨prior, later, split⟩ := List.mem_iff_append.mp funded
  have transition : Advance installed disposed entry {entry with phase := .installed true} :=
    .promote sealed certified
  let next : Ledger Scope Pool := ⟨ledger.ordinary, prior ++ {entry with phase := .installed true} :: later⟩
  have applyStep : Step limit installed disposed ledger (some entry.scope) next := by
    have exactLedger : ledger = ⟨ledger.ordinary, prior ++ entry :: later⟩ := by
      cases ledger
      simp_all
    exact exactLedger.symm ▸ Step.advance transition
  exact ⟨next, applyStep, every_transition_preserves_each_capacity_and_unique_scope sound applyStep,
    List.mem_append.mpr (.inr (List.mem_cons_self ..))⟩

inductive UnrelatedTrace (limit : Pool → Nat) (installed disposed : Scope → Prop) (focus : Scope) :
    Ledger Scope Pool → Ledger Scope Pool → Prop
  | same (ledger) : UnrelatedTrace limit installed disposed focus ledger ledger
  | next {first before after changed} :
      UnrelatedTrace limit installed disposed focus first before →
      Step limit installed disposed before changed after → changed ≠ some focus →
      UnrelatedTrace limit installed disposed focus first after

theorem unrelated_traffic_preserves_a_reserved_row_and_pool_bounds
    {limit : Pool → Nat} {installed disposed : Scope → Prop} {first last : Ledger Scope Pool}
    {entry : Entry Scope Pool} (held : entry ∈ first.moves) (sound : Sound limit first)
    (trace : UnrelatedTrace limit installed disposed entry.scope first last) :
    entry ∈ last.moves ∧ Sound limit last := by
  induction trace with
  | same => exact ⟨held, sound⟩
  | next _ step unrelated prior =>
      exact ⟨other_scopes_cannot_change_an_existing_reservation prior.1 unrelated step,
        every_transition_preserves_each_capacity_and_unique_scope prior.2 step⟩

structure Layout (Pool : Type) where
  residencyCopies : Pool → Nat
  workspaceCopies : Pool → Nat

variable {Payload Voter Ticket : Type}

def recoveryProfile {context : RecoveryCapacity.Context Payload Voter}
    (layout : Layout Pool) (cut : RecoveryCapacity.Cut context) : Profile Pool := by
  have fits : cut.bytes ≤ context.budget.envelope := cut.fits
  have twice : cut.bytes ≤ 2 * context.budget.envelope := by omega
  exact {
    residency := fun pool => layout.residencyCopies pool * context.budget.envelope
    workspace := fun pool => layout.workspaceCopies pool * (2 * context.budget.envelope)
    resident := fun pool => layout.residencyCopies pool * cut.bytes
    obsolete := fun pool => layout.workspaceCopies pool * cut.bytes
    residentFits := fun pool => Nat.mul_le_mul_left _ fits
    obsoleteFits := fun pool => Nat.mul_le_mul_left _ twice }

theorem a_concurrent_ledger_preserves_a_funded_exact_recovery
    [DecidableEq Ticket] {context : RecoveryCapacity.Context Payload Voter}
    (layout : Layout Pool) (scope : Scope) (cut : RecoveryCapacity.Cut context)
    (installation : RecoveryCapacity.Installation cut)
    {limit : Pool → Nat} {installed disposed : Scope → Prop}
    {bank busy : Ledger Scope Pool}
    (held : (⟨scope, recoveryProfile layout cut, .sealed⟩ : Entry Scope Pool) ∈ bank.moves)
    (sound : Sound limit bank) (interleaved : UnrelatedTrace limit installed disposed scope bank busy)
    (certified : installed scope)
    (reserveProvider : ProviderIOClosure.Custody Ticket → Prop)
    (localState : RecoveryCapacity.State context Ticket) (sealed : localState.phase = .sealed cut)
    (localSound : RecoveryCapacity.Sound localState)
    (old : ProviderIOClosure.State Ticket) (oldSound : ProviderIOClosure.Sound old) (oldPresent : old.present = true) :
    ∃ (after : Ledger Scope Pool) (settled : RecoveryCapacity.State context Ticket),
      Step limit installed disposed busy (some scope) after ∧ Sound limit after ∧
      (⟨scope, recoveryProfile layout cut, .installed true⟩ : Entry Scope Pool) ∈ after.moves ∧
      RecoveryCapacity.Trace reserveProvider localState settled ∧
      settled.phase = .installed cut installation true ∧ settled.incumbent = old ∧
      (∀ pool, charge (⟨scope, recoveryProfile layout cut, .installed true⟩ : Entry Scope Pool) pool =
        layout.residencyCopies pool * RecoveryCapacity.finalCharge settled.phase +
        layout.workspaceCopies pool * RecoveryCapacity.workspaceCharge settled.phase) := by
  obtain ⟨stillHeld, busySound⟩ :=
    unrelated_traffic_preserves_a_reserved_row_and_pool_bounds held sound interleaved
  obtain ⟨after, reclassify, finalFit, marked⟩ :=
    a_funded_scope_can_promote_without_rebilling stillHeld rfl certified busySound
  obtain ⟨settled, recovery, installedPhase, _, _, _, sameOld⟩ :=
    RecoveryCapacity.a_sealed_move_can_install_without_new_ordinary_or_custody_capacity
      reserveProvider localState cut installation sealed localSound old oldSound oldPresent
  refine ⟨after, settled, reclassify, finalFit, marked, recovery, installedPhase, sameOld, ?_⟩
  intro pool
  rw [installedPhase]
  rfl

#print axioms load_concat
#print axioms a_disposition_releases_only_its_own_scope
#print axioms scope_is_immutable_across_a_move
#print axioms spending_a_reservation_never_needs_extra_space
#print axioms a_sealed_move_is_promoted_with_its_obsolete_charge
#print axioms every_pool_fits_after_vector_admission
#print axioms every_transition_preserves_each_capacity_and_unique_scope
#print axioms arbitrary_interleavings_preserve_each_capacity
#print axioms other_scopes_cannot_change_an_existing_reservation
#print axioms a_funded_scope_can_promote_without_rebilling
#print axioms unrelated_traffic_preserves_a_reserved_row_and_pool_bounds
#print axioms a_concurrent_ledger_preserves_a_funded_exact_recovery

end CapacityLedger
