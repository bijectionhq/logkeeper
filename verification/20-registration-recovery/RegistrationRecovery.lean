import SharedCustody

set_option warningAsError true

namespace RegistrationRecovery

open SnapshotAdmission (setSlot)

structure Binding where
  root : Nat
  manifest : Nat
  versionSet : Nat
  deriving DecidableEq

structure Issuer where
  issued : Nat
  planned : Nat → Option Binding
  terminal : Nat → Prop
  observed : Nat → Option Binding

structure Custodian where
  floor : Nat
  held : Nat → Option Binding
  spent : Nat → Bool

inductive Decision where
  | admit
  | replay
  | refuse
  deriving DecidableEq

def acquire (table : Custodian) (serial : Nat) (binding : Binding) : Decision :=
  match table.held serial with
  | some existing => if binding = existing then .replay else .refuse
  | none => if table.floor < serial ∧ table.spent serial = false then .admit else .refuse

def release (table : Custodian) (serial : Nat) : Custodian :=
  {table with
    held := setSlot table.held serial none
    spent := setSlot table.spent serial (decide (table.floor < serial))}

def compact (table : Custodian) (through : Nat) : Custodian :=
  {table with
    floor := through
    spent := fun serial => if serial ≤ through then false else table.spent serial}

def ReferenceClosed (table : Custodian) (serial : Nat) : Prop :=
  table.held serial = none ∧ (serial ≤ table.floor ∨ table.spent serial = true)

def logicalReference (table : Custodian) (serial : Nat) : SharedCustody.Reference :=
  match table.held serial with
  | some _ => .held
  | none => if serial ≤ table.floor ∨ table.spent serial = true then .closed else .unused

structure Certificate (issuer : Issuer) (through : Nat) : Prop where
  withinIssued : through ≤ issuer.issued
  accounted : ∀ serial binding, serial ≤ through → issuer.planned serial = some binding →
    issuer.terminal serial ∨ issuer.observed serial = some binding

def DurableReceipts (issuer : Issuer) (table : Custodian) : Prop :=
  ∀ serial binding, issuer.observed serial = some binding → ¬ issuer.terminal serial →
    table.held serial = some binding

inductive Step (issuer : Issuer) : Custodian → Custodian → Prop
  | acquire {table} (serial : Nat) (binding : Binding)
      (planned : issuer.planned serial = some binding)
      (empty : table.held serial = none) (fresh : table.floor < serial)
      (unspent : table.spent serial = false) :
      Step issuer table {table with held := setSlot table.held serial (some binding)}
  | release {table} (serial : Nat) (closed : issuer.terminal serial) :
      Step issuer table (RegistrationRecovery.release table serial)
  | compact {table} (through : Nat) (moves : table.floor ≤ through)
      (checked : Certificate issuer through) :
      Step issuer table (RegistrationRecovery.compact table through)

theorem retry_uses_exact_installed_binding {table : Custodian} {serial : Nat}
    {binding requested : Binding} (held : table.held serial = some binding) :
    acquire table serial binding = .replay ∧
      (requested ≠ binding → acquire table serial requested = .refuse) := by
  constructor
  · simp [acquire, held]
  · intro different
    simp [acquire, held, different]

theorem no_absent_acquire_at_or_below_floor {table : Custodian} {serial : Nat}
    (empty : table.held serial = none) (old : serial ≤ table.floor) (binding : Binding) :
    acquire table serial binding = .refuse := by
  simp [acquire, empty, Nat.not_lt_of_ge old]

theorem releasing_unknown_outcome_closes_exact_reference {table : Custodian} (serial : Nat) :
    ReferenceClosed (release table serial) serial ∧ logicalReference (release table serial) serial = .closed := by
  have empty : (release table serial).held serial = none := by simp [release, setSlot]
  have fenced : serial ≤ (release table serial).floor ∨ (release table serial).spent serial = true := by
    by_cases old : serial ≤ table.floor
    · exact .inl old
    · have fresh : table.floor < serial := Nat.lt_of_not_ge old
      exact .inr (by simp [release, setSlot, fresh])
  exact ⟨⟨empty, fenced⟩, by simp [logicalReference, empty, fenced]⟩

theorem compact_discards_markers_but_preserves_all_grants (table : Custodian) (through : Nat) :
    (compact table through).held = table.held ∧
      ∀ serial, serial ≤ through → (compact table through).spent serial = false := by
  exact ⟨rfl, fun serial gone => by simp [compact, gone]⟩

theorem closed_reference_survives_compaction {table : Custodian} {through serial : Nat}
    (closed : ReferenceClosed table serial) (advances : table.floor ≤ through) :
    ReferenceClosed (compact table through) serial := by
  refine ⟨closed.1, ?_⟩
  by_cases old : serial ≤ through
  · exact .inl old
  · have spent := closed.2.resolve_left (fun lower => old (Nat.le_trans lower advances))
    exact .inr (by simpa [compact, old] using spent)

theorem every_step_preserves_closed_references {issuer : Issuer} {before after : Custodian}
    (step : Step issuer before after) (serial : Nat) (closed : ReferenceClosed before serial) :
    ReferenceClosed after serial := by
  cases step with
  | acquire chosen _ _ _ fresh unspent =>
      have unrelated : serial ≠ chosen := by
        intro same
        subst serial
        have beyond : before.floor < chosen := fresh
        rcases closed.2 with old | marker
        · exact (Nat.not_le_of_lt beyond) old
        · exact Bool.noConfusion (marker.symm.trans unspent)
      exact ⟨by simpa [setSlot, unrelated] using closed.1, closed.2⟩
  | release chosen _ =>
      by_cases same : serial = chosen
      · subst serial
        exact (releasing_unknown_outcome_closes_exact_reference chosen).1
      · refine ⟨by simpa [release, setSlot, same] using closed.1, ?_⟩
        rcases closed.2 with old | marker
        · exact .inl old
        · exact .inr (by simpa [release, setSlot, same] using marker)
  | compact _ advances _ => exact closed_reference_survives_compaction closed advances

inductive Trace (issuer : Issuer) : Custodian → Custodian → Prop
  | same (table : Custodian) : Trace issuer table table
  | next {first before after} : Trace issuer first before → Step issuer before after →
      Trace issuer first after

theorem closed_reference_survives_arbitrary_delayed_actions {issuer : Issuer} {first last : Custodian}
    (trace : Trace issuer first last) (serial : Nat) (closed : ReferenceClosed first serial) :
    ReferenceClosed last serial := by
  induction trace with
  | same => exact closed
  | next _ effect prior => exact every_step_preserves_closed_references effect serial prior

theorem cancelled_plan_can_be_settled_on_each_shard
    (planned : Nat → Option Nat) (issuers : Nat → Issuer) (custodians : Nat → Custodian)
    (canceled : ∀ shard serial, planned shard = some serial → (issuers shard).terminal serial) :
    ∃ settled : Nat → Custodian,
      (∀ shard serial, planned shard = some serial →
        Step (issuers shard) (custodians shard) (settled shard) ∧ ReferenceClosed (settled shard) serial) ∧
      (∀ shard, planned shard = none → settled shard = custodians shard) := by
  let settled := fun shard =>
    match planned shard with
    | none => custodians shard
    | some serial => release (custodians shard) serial
  refine ⟨settled, ?_, ?_⟩
  · intro shard serial recorded
    have released : settled shard = release (custodians shard) serial := by simp [settled, recorded]
    rw [released]
    exact ⟨.release serial (canceled shard serial recorded),
      (releasing_unknown_outcome_closes_exact_reference serial).1⟩
  · intro shard unplanned
    simp [settled, unplanned]

theorem durable_receipts_survive_custodian_progress {issuer : Issuer} {before after : Custodian}
    (backed : DurableReceipts issuer before) (step : Step issuer before after) :
    DurableReceipts issuer after := by
  intro serial binding receipt live
  have original := backed serial binding receipt live
  cases step with
  | acquire chosen _ _ empty _ _ =>
      have other : serial ≠ chosen := by
        intro same
        subst serial
        have impossible : none = some binding := empty.symm.trans original
        cases impossible
      simpa [setSlot, other] using original
  | release chosen authorized =>
      have other : serial ≠ chosen := fun same => live (same.symm ▸ authorized)
      simpa [release, setSlot, other] using original
  | compact _ _ _ => exact original

theorem installing_certified_floor_does_not_strand_unclosed_preparation
    {issuer : Issuer} {table : Custodian} {through serial : Nat} {binding : Binding}
    (certificate : Certificate issuer through) (backed : DurableReceipts issuer table)
    (covered : serial ≤ through) (planned : issuer.planned serial = some binding)
    (live : ¬ issuer.terminal serial) :
    (compact table through).held serial = some binding := by
  have accounted : issuer.terminal serial ∨ issuer.observed serial = some binding :=
    certificate.accounted serial binding covered planned
  exact backed serial binding (accounted.resolve_left live) live

structure IssuerProgress (before after : Issuer) : Prop where
  grows : before.issued ≤ after.issued
  frozen : ∀ serial, serial ≤ before.issued → after.planned serial = before.planned serial
  terminal : ∀ serial, before.terminal serial → after.terminal serial
  retains : ∀ serial binding, before.observed serial = some binding →
    after.terminal serial ∨ after.observed serial = some binding

theorem delayed_floor_certificate_survives_issuer_progress {before after : Issuer} {through : Nat}
    (certificate : Certificate before through) (progress : IssuerProgress before after) :
    Certificate after through := by
  refine ⟨Nat.le_trans certificate.withinIssued progress.grows, ?_⟩
  intro serial binding covered planned
  have frozen := progress.frozen serial (Nat.le_trans covered certificate.withinIssued)
  have prior := certificate.accounted serial binding covered (frozen ▸ planned)
  rcases prior with closed | receipt
  · exact .inl (progress.terminal serial closed)
  · exact progress.retains serial binding receipt

theorem old_grant_can_replay_after_floor_advances {issuer : Issuer} {table : Custodian}
    {serial through : Nat} {binding : Binding}
    (backed : DurableReceipts issuer table) (certificate : Certificate issuer through)
    (advances : table.floor ≤ through) (covered : serial ≤ through)
    (planned : issuer.planned serial = some binding) (live : ¬ issuer.terminal serial) :
    ∃ after, Step issuer table after ∧ serial ≤ after.floor ∧
      logicalReference after serial = .held ∧ acquire after serial binding = .replay := by
  let after := compact table through
  have held : after.held serial = some binding :=
    installing_certified_floor_does_not_strand_unclosed_preparation certificate backed covered planned live
  exact ⟨after, .compact through advances certificate, covered,
    by simp [logicalReference, held], (retry_uses_exact_installed_binding (requested := binding) held).1⟩

theorem terminal_only_prefix_cannot_advance_past_a_live_root {issuer : Issuer}
    {liveSerial through : Nat} (live : ¬ issuer.terminal liveSerial)
    (drainFirst : ∀ id, id ≤ through → issuer.terminal id) :
    through < liveSerial :=
  Nat.lt_of_not_ge (fun covered => live (drainFirst liveSerial covered))

theorem credit_from_acknowledged_floor_bounds_receiver_debt {issued acknowledged receiverFloor width : Nat}
    (installed : acknowledged ≤ receiverFloor) (remaining : issued + 1 - acknowledged ≤ width) :
    issued + 1 - receiverFloor ≤ width := by
  omega

def markerIndex (serial floor issued width : Nat) (afterFloor : floor < serial)
    (allocated : serial ≤ issued) (bounded : issued - floor ≤ width) : Fin width :=
  ⟨serial - floor - 1, by omega⟩

theorem markers_above_floor_fit_in_credit_window {floor issued width : Nat}
    (bounded : issued - floor ≤ width) (left right : Nat)
    (leftFresh : floor < left) (rightFresh : floor < right)
    (leftIssued : left ≤ issued) (rightIssued : right ≤ issued) :
    markerIndex left floor issued width leftFresh leftIssued bounded =
      markerIndex right floor issued width rightFresh rightIssued bounded → left = right := by
  intro same
  have slot := congrArg Fin.val same
  change left - floor - 1 = right - floor - 1 at slot
  omega

#print axioms retry_uses_exact_installed_binding
#print axioms no_absent_acquire_at_or_below_floor
#print axioms releasing_unknown_outcome_closes_exact_reference
#print axioms compact_discards_markers_but_preserves_all_grants
#print axioms closed_reference_survives_compaction
#print axioms every_step_preserves_closed_references
#print axioms closed_reference_survives_arbitrary_delayed_actions
#print axioms cancelled_plan_can_be_settled_on_each_shard
#print axioms durable_receipts_survive_custodian_progress
#print axioms installing_certified_floor_does_not_strand_unclosed_preparation
#print axioms delayed_floor_certificate_survives_issuer_progress
#print axioms old_grant_can_replay_after_floor_advances
#print axioms terminal_only_prefix_cannot_advance_past_a_live_root
#print axioms credit_from_acknowledged_floor_bounds_receiver_debt
#print axioms markers_above_floor_fit_in_credit_window

end RegistrationRecovery
