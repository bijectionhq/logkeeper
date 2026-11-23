import JournalRotation
import SharedCustody
import ScopeProtection
import ProviderIOClosure

set_option warningAsError true

namespace WithdrawalRecovery

open SharedCustody (Store Covered)
open SnapshotAdmission (setSlot)
open ScopeProtection (Protects Coverage)

structure Receipt (Ticket : Type) where
  version : Nat
  observed : ProviderIOClosure.State Ticket

variable {Input Zone Change Ticket : Type}

structure Rules (Input Zone Change Ticket : Type) where
  needs : SharedCustody.Dependencies
  mayClose : Nat → Prop
  owed : Input → Prop
  credible : Zone → Prop
  contains : Nat → Input → Prop
  zoneOf : Nat → Zone
  delta : Store → Change → Option Store
  authentic : Receipt Ticket → Prop

inductive Frame (Change Ticket : Type) where
  | custody (change : Change)
  | reserve (version : Nat)
  | settle (version : Nat) (receipt : Receipt Ticket)

def Witnesses (rules : Rules Input Zone Change Ticket) (store : Store) (keep : Nat → Prop) :
    Input → Zone → Prop :=
  fun input zone => ∃ version, store.gates version = .open ∧ keep version ∧
    rules.contains version input ∧ rules.zoneOf version = zone

def Safe (rules : Rules Input Zone Change Ticket) (store : Store) : Prop :=
  Covered rules.needs store ∧ Protects rules.credible rules.owed (Witnesses rules store fun _ => True)

def Issued (store : Store) (version : Nat) : Prop :=
  store.gates version = .deleting

def NoExactHold (store : Store) (version : Nat) : Prop :=
  (∀ root, store.refs root version ≠ .held) ∧ store.borrows version = 0

def CanReserve (rules : Rules Input Zone Change Ticket) (store : Store) (version : Nat) : Prop :=
  store.gates version = .open ∧ NoExactHold store version ∧
    Protects rules.credible rules.owed (Witnesses rules store fun kept => kept ≠ version)

def StableReceipt (rules : Rules Input Zone Change Ticket) (version : Nat) (receipt : Receipt Ticket) : Prop :=
  receipt.version = version ∧ rules.authentic receipt ∧
    ProviderIOClosure.Sound receipt.observed ∧ receipt.observed.erased = true

theorem a_receipt_identifies_its_exact_version
    (rules : Rules Input Zone Change Ticket) (version : Nat) (receipt : Receipt Ticket)
    (stable : StableReceipt rules version receipt) : receipt.version = version := by
  exact stable.1

def reserved (store : Store) (version : Nat) : Store :=
  { store with gates := setSlot store.gates version .deleting }

def settled (store : Store) (version : Nat) : Store :=
  { store with gates := setSlot store.gates version .gone, physical := setSlot store.physical version false }

noncomputable def apply (rules : Rules Input Zone Change Ticket) (store : Store) :
    Frame Change Ticket → Option Store := by
  classical
  exact fun frame => match frame with
  | .custody change =>
    (rules.delta store change).bind fun next =>
      if SharedCustody.Step rules.needs rules.mayClose store next ∧ next.gates = store.gates
      then some next else none
  | .reserve version =>
    if CanReserve rules store version then some (reserved store version) else none
  | .settle version receipt =>
    if Issued store version ∧ StableReceipt rules version receipt then some (settled store version) else none

theorem a_withdrawal_requires_every_exact_hold_to_be_closed
    (rules : Rules Input Zone Change Ticket) (before after : Store) (version : Nat)
    (admitted : apply rules before (.reserve version) = some after) :
    NoExactHold before version ∧ after = reserved before version := by
  simp only [apply] at admitted
  split at admitted
  · next allowed =>
    cases admitted
    exact ⟨allowed.2.1, rfl⟩
  · cases admitted

theorem an_issued_withdrawal_cannot_be_used_by_a_root_or_borrow
    (rules : Rules Input Zone Change Ticket) (store : Store) (version : Nat)
    (safe : Safe rules store) (issued : Issued store version) :
    NoExactHold store version := by
  have excludesOpen : store.gates version ≠ .open := by
    intro openGate
    exact SharedCustody.VersionPhase.noConfusion (issued.symm.trans openGate)
  exact ⟨fun root held => excludesOpen (safe.1.referenceGate root version held),
    Nat.eq_zero_of_not_pos fun active => excludesOpen (safe.1.borrowGate version active)⟩

private theorem coverage_depends_on_open_versions
    (rules : Rules Input Zone Change Ticket) (before after : Store)
    (same : ∀ version, after.gates version = .open ↔ before.gates version = .open)
    (prior : Protects rules.credible rules.owed (Witnesses rules before fun _ => True)) :
    Protects rules.credible rules.owed (Witnesses rules after fun _ => True) := by
  intro input required loss credible
  obtain ⟨zone, survives, version, openGate, _, exact, domain⟩ := prior input required loss credible
  exact ⟨zone, survives, version, (same version).2 openGate, trivial, exact, domain⟩

theorem each_accepted_frame_preserves_custody_and_zone_coverage
    (rules : Rules Input Zone Change Ticket) (before after : Store) (frame : Frame Change Ticket)
    (safe : Safe rules before) (admitted : apply rules before frame = some after) :
    Safe rules after := by
  cases frame with
  | custody change =>
    simp only [apply] at admitted
    cases reduced : rules.delta before change with
    | none => simp [reduced] at admitted
    | some next =>
      simp only [reduced, Option.bind_some] at admitted
      split at admitted
      · next checked =>
        have nextSafe : Safe rules next :=
          ⟨SharedCustody.every_step_keeps_dependencies safe.1 checked.1,
            coverage_depends_on_open_versions rules before next
              (fun version => by rw [checked.2]) safe.2⟩
        exact Option.some.inj admitted ▸ nextSafe
      · cases admitted
  | reserve version =>
    simp only [apply] at admitted
    split at admitted
    · next allowed =>
      cases admitted
      refine ⟨SharedCustody.every_step_keeps_dependencies (closeAllowed := rules.mayClose) safe.1
        (.fenceDisposal version allowed.1 allowed.2.1.1 allowed.2.1.2), ?_⟩
      intro input required loss credible
      obtain ⟨zone, survives, kept, openGate, different, exact, domain⟩ :=
        allowed.2.2 input required loss credible
      exact ⟨zone, survives, kept, by simpa [reserved, setSlot, different] using openGate,
        trivial, exact, domain⟩
    · cases admitted
  | settle version receipt =>
    simp only [apply] at admitted
    split at admitted
    · next allowed =>
      cases admitted
      refine ⟨SharedCustody.every_step_keeps_dependencies (closeAllowed := rules.mayClose) safe.1 (.erase version allowed.1), ?_⟩
      apply coverage_depends_on_open_versions rules before (settled before version) _ safe.2
      intro queried
      by_cases same : queried = version
      · subst queried
        have pending : before.gates version = .deleting := allowed.1
        simp [settled, setSlot, pending]
      · simp [settled, setSlot, same]
    · cases admitted

theorem a_settlement_binds_stable_absence_to_the_original_version
    (rules : Rules Input Zone Change Ticket) (before after : Store) (version : Nat) (receipt : Receipt Ticket)
    (accepted : apply rules before (.settle version receipt) = some after) :
    Issued before version ∧ receipt.version = version ∧ rules.authentic receipt ∧
      ProviderIOClosure.StableAbsence receipt.observed ∧ after = settled before version := by
  simp only [apply] at accepted
  split at accepted
  · next checked =>
    cases accepted
    exact ⟨checked.1, a_receipt_identifies_its_exact_version rules version receipt checked.2,
      checked.2.2.1, checked.2.2.2.1.erasure checked.2.2.2.2, rfl⟩
  · cases accepted

theorem a_delayed_exact_settlement_stays_absent [DecidableEq Ticket]
    (rules : Rules Input Zone Change Ticket) (before after : Store) (version : Nat) (receipt : Receipt Ticket)
    (accepted : apply rules before (.settle version receipt) = some after)
    (reserve : ProviderIOClosure.Custody Ticket → Prop) (provider : ProviderIOClosure.State Ticket)
    (later : ProviderIOClosure.Trace reserve receipt.observed provider) :
    receipt.version = version ∧ ProviderIOClosure.StableAbsence provider := by
  simp only [apply] at accepted
  split at accepted
  · next matched =>
    exact ⟨a_receipt_identifies_its_exact_version rules version receipt matched.2,
      (ProviderIOClosure.no_write_can_recreate_a_certified_erasure matched.2.2.2.1 matched.2.2.2.2 later).2⟩
  · cases accepted

def Backed (store : Store) (provider : Nat → Bool) : Prop :=
  ∀ version, store.gates version = .open → provider version = true

def applyDelete (provider : Nat → Bool) (version : Nat) : Nat → Bool :=
  setSlot provider version false

theorem a_provider_effect_targets_only_an_excluded_version
    (store : Store) (provider : Nat → Bool) (version : Nat)
    (backed : Backed store provider) (issued : Issued store version) :
    Backed store (applyDelete provider version) := by
  intro query openGate
  have different : query ≠ version := by
    intro same
    subst query
    exact SharedCustody.VersionPhase.noConfusion (openGate.symm.trans issued)
  simpa [applyDelete, setSlot, different] using backed query openGate

theorem no_chosen_frame_reopens_a_withdrawing_or_settled_version
    (rules : Rules Input Zone Change Ticket) (before after : Store) (frame : Frame Change Ticket)
    (applied : apply rules before frame = some after) (version : Nat)
    (opened : after.gates version = .open) :
    before.gates version = .open := by
  cases frame with
  | custody change =>
    simp only [apply] at applied
    cases reduced : rules.delta before change with
    | none => simp [reduced] at applied
    | some next =>
      simp only [reduced, Option.bind_some] at applied
      split at applied
      · next checked =>
        have gates : after.gates = before.gates := (Option.some.inj applied).symm ▸ checked.2
        rwa [gates] at opened
      · cases applied
  | reserve removed =>
    simp only [apply] at applied
    split at applied
    · cases applied
      by_cases same : version = removed
      · subst version
        simp [reserved, setSlot] at opened
      · simpa [reserved, setSlot, same] using opened
    · cases applied
  | settle removed receipt =>
    simp only [apply] at applied
    split at applied
    · cases applied
      by_cases same : version = removed
      · subst version
        simp [settled, setSlot] at opened
      · simpa [settled, setSlot, same] using opened
    · cases applied

structure Runtime where
  custody : Store
  provider : Nat → Bool

def Sound (rules : Rules Input Zone Change Ticket) (state : Runtime) : Prop :=
  Safe rules state.custody ∧ Backed state.custody state.provider

inductive Step (rules : Rules Input Zone Change Ticket) : Runtime → Runtime → Prop
  | commit (before : Runtime) (frame : Frame Change Ticket) (after : Store)
      (chosen : apply rules before.custody frame = some after) :
      Step rules before ⟨after, before.provider⟩
  | effect (before : Runtime) (version : Nat) (issued : Issued before.custody version) :
      Step rules before ⟨before.custody, applyDelete before.provider version⟩

theorem interleaved_provider_effects_preserve_physical_backing
    (rules : Rules Input Zone Change Ticket) (first last : Runtime)
    (history : ScopeProtection.Trace (Step rules) first last) (initial : Sound rules first) :
    Sound rules last := by
  induction history with
  | nil => exact initial
  | cons event _ ih =>
    apply ih
    cases event with
    | commit frame after chosen =>
      exact ⟨each_accepted_frame_preserves_custody_and_zone_coverage rules _ after frame initial.1 chosen,
        fun version openGate => initial.2 version
          (no_chosen_frame_reopens_a_withdrawing_or_settled_version rules _ after frame chosen version openGate)⟩
    | effect version issued =>
      exact ⟨initial.1, a_provider_effect_targets_only_an_excluded_version _ _ version initial.2 issued⟩

theorem a_paid_exact_use_reads_physical_bytes
    (rules : Rules Input Zone Change Ticket) (store : Store) (provider : Nat → Bool)
    (safe : Safe rules store) (backed : Backed store provider) (version : Nat)
    (held : (∃ root, store.refs root version = .held) ∨ 0 < store.borrows version) :
    provider version = true := by
  rcases held with ⟨root, reference⟩ | borrow
  · exact backed version (safe.1.referenceGate root version reference)
  · exact backed version (safe.1.borrowGate version borrow)

theorem an_acknowledged_input_has_a_surviving_backed_version_after_interleaved_effects
    (rules : Rules Input Zone Change Ticket) (first last : Runtime)
    (history : ScopeProtection.Trace (Step rules) first last) (initial : Sound rules first)
    (input : Input) (owed : rules.owed input) (lost : Zone) (credible : rules.credible lost) :
    ∃ version, rules.zoneOf version ≠ lost ∧ rules.contains version input ∧ last.provider version = true := by
  have restored := interleaved_provider_effects_preserve_physical_backing rules first last history initial
  obtain ⟨zone, survives, version, openGate, _, exact, domain⟩ := restored.1.2 input owed lost credible
  exact ⟨version, domain ▸ survives, exact, restored.2 version openGate⟩

noncomputable def replay (rules : Rules Input Zone Change Ticket) (origin : Store) (frames : List (Frame Change Ticket)) :
    Option Store :=
  frames.foldlM (apply rules) origin

theorem replay_preserves_shared_custody_and_zone_coverage
    (rules : Rules Input Zone Change Ticket) (frames : List (Frame Change Ticket)) (origin after : Store)
    (initial : Safe rules origin) (chosen : replay rules origin frames = some after) :
    Safe rules after := by
  induction frames generalizing origin with
  | nil =>
    change some origin = some after at chosen
    cases chosen
    exact initial
  | cons frame rest ih =>
    simp only [replay, List.foldlM_cons] at chosen
    cases applied : apply rules origin frame with
    | none => simp [applied] at chosen
    | some next =>
      have tail : replay rules next rest = some after := by simpa [replay, applied] using chosen
      exact ih next (each_accepted_frame_preserves_custody_and_zone_coverage rules origin next frame initial applied) tail

theorem either_exact_checkpoint_recovers_the_chosen_withdrawal_state
    (rules : Rules Input Zone Change Ticket) (origin checkpoint after : Store)
    (journal : JournalRotation.State (Frame Change Ticket)) (view : JournalRotation.View)
    (safeMedia : JournalRotation.Safe journal) (tracked : JournalRotation.TracksNamespace journal)
    (selected : journal.namespaceChoices view)
    (base : replay rules origin (journal.history.take view.cut) = some checkpoint)
    (chosen : replay rules origin journal.history = some after)
    (safeOrigin : Safe rules origin) :
    ∃ suffix, replay rules checkpoint suffix = some after ∧ Safe rules after ∧
      ∀ offset frame, suffix[offset]? = some frame →
        journal.media (.tail (view.cut + offset)) = some [frame] := by
  obtain ⟨_, _, storedTail⟩ :=
    JournalRotation.selectable_has_exact_cut safeMedia ((tracked view).mp selected)
  have whole := chosen
  rw [← List.take_append_drop view.cut journal.history] at whole
  simp only [replay, List.foldlM_append] at whole
  change (journal.history.take view.cut).foldlM (apply rules) origin = some checkpoint at base
  rw [base] at whole
  refine ⟨journal.history.drop view.cut, whole,
    replay_preserves_shared_custody_and_zone_coverage rules journal.history origin after safeOrigin chosen, ?_⟩
  intro offset frame found
  rw [List.getElem?_drop] at found
  exact storedTail _ _ (Nat.le_add_right _ _) found

#print axioms a_receipt_identifies_its_exact_version
#print axioms a_withdrawal_requires_every_exact_hold_to_be_closed
#print axioms an_issued_withdrawal_cannot_be_used_by_a_root_or_borrow
#print axioms each_accepted_frame_preserves_custody_and_zone_coverage
#print axioms a_settlement_binds_stable_absence_to_the_original_version
#print axioms a_delayed_exact_settlement_stays_absent
#print axioms a_provider_effect_targets_only_an_excluded_version
#print axioms no_chosen_frame_reopens_a_withdrawing_or_settled_version
#print axioms interleaved_provider_effects_preserve_physical_backing
#print axioms a_paid_exact_use_reads_physical_bytes
#print axioms an_acknowledged_input_has_a_surviving_backed_version_after_interleaved_effects
#print axioms replay_preserves_shared_custody_and_zone_coverage
#print axioms either_exact_checkpoint_recovers_the_chosen_withdrawal_state

end WithdrawalRecovery
