import WithdrawalRecovery
import RegistrationRecovery

set_option warningAsError true

namespace DynamicProtection

open SnapshotAdmission (setSlot)
open SharedCustody (Store Covered)
open ScopeProtection (Protects)
open WithdrawalRecovery (Backed Issued applyDelete)

variable {Input Zone : Type}

structure Plan (Input Zone : Type) where
  needs : SharedCustody.Dependencies
  required : Nat → Input → Prop
  contains : Nat → Input → Prop
  zoneOf : Nat → Zone

def Placements (plan : Plan Input Zone) (root : Nat) : Input → Zone → Prop :=
  fun input zone => ∃ version, plan.needs root version ∧ plan.contains version input ∧ plan.zoneOf version = zone

def Qualifies (plan : Plan Input Zone) (cases : Zone → Prop) (root : Nat) : Prop :=
  Protects cases (plan.required root) (Placements plan root)

def ExactRegistrations (plan : Plan Input Zone) (store : Store) (root : Nat) : Prop :=
  ∀ version, plan.needs root version → store.refs root version = .held

def CanPublish (plan : Plan Input Zone) (store : Store) (cases : Zone → Prop) (root : Nat) : Prop :=
  store.roots root = .preparing ∧ ExactRegistrations plan store root ∧ Qualifies plan cases root

theorem publishing_requires_a_hold_for_each_exact_version
    (plan : Plan Input Zone) (store : Store) (cases : Zone → Prop) (root : Nat)
    (ready : CanPublish plan store cases root) :
    ∀ version, plan.needs root version → store.refs root version = .held := by
  exact ready.2.1

theorem a_closed_plan_cannot_publish
    (plan : Plan Input Zone) (store : Store) (cases : Zone → Prop) (root : Nat)
    (closed : store.roots root = .closed) :
    ¬ CanPublish plan store cases root := by
  intro ready
  exact SharedCustody.RootPhase.noConfusion (closed.symm.trans ready.1)

theorem narrower_envelope_keeps_the_held_plan_usable
    (plan : Plan Input Zone) (store : Store) (prior current : Zone → Prop) (root : Nat)
    (ready : CanPublish plan store prior root) (narrower : ∀ zone, current zone → prior zone) :
    CanPublish plan store current root := by
  refine ⟨ready.1, ready.2.1, ?_⟩
  exact fun input required loss credible => ready.2.2 input required loss (narrower loss credible)

theorem ordered_publication_uses_previously_observed_durable_grants
    (plan : Plan Input Zone) (store : Store) (cases : Zone → Prop) (root : Nat)
    (issuers : Nat → RegistrationRecovery.Issuer) (owners : Nat → RegistrationRecovery.Custodian)
    (serial : Nat → Nat) (binding : Nat → RegistrationRecovery.Binding)
    (preparing : store.roots root = .preparing) (covered : Qualifies plan cases root)
    (known : ∀ version, plan.needs root version →
      (issuers version).observed (serial version) = some (binding version) ∧
      ¬ (issuers version).terminal (serial version))
    (retained : ∀ version, RegistrationRecovery.DurableReceipts (issuers version) (owners version))
    (linked : ∀ version, RegistrationRecovery.logicalReference (owners version) (serial version) =
      store.refs root version) :
    CanPublish plan store cases root := by
  refine ⟨preparing, ?_, covered⟩
  intro version needed
  obtain ⟨receipt, unresolved⟩ := known version needed
  have stillHeld := retained version (serial version) (binding version) receipt unresolved
  have ownHold : store.refs root version = .held := by
    rw [← linked version]
    simp [RegistrationRecovery.logicalReference, stillHeld]
  simp [ownHold]

structure State (Zone : Type) where
  custody : Store
  provider : Nat → Bool
  credible : Zone → Prop

structure Sound (plan : Plan Input Zone) (state : State Zone) : Prop where
  custody : Covered plan.needs state.custody
  backing : Backed state.custody state.provider
  current : ∀ root, state.custody.roots root = .live → Qualifies plan state.credible root

inductive Step (plan : Plan Input Zone) (mayClose : Nat → Prop) : State Zone → State Zone → Prop
  | publish (before : State Zone) (root : Nat)
      (ready : CanPublish plan before.custody before.credible root) :
      Step plan mayClose before { before with
        custody := { before.custody with roots := setSlot before.custody.roots root .live } }
  | maintain (before : State Zone) (next : Store)
      (custody : SharedCustody.Step plan.needs mayClose before.custody next)
      (onlyExistingRoots : ∀ root, next.roots root = .live → before.custody.roots root = .live)
      (onlyExistingCopies : ∀ version, next.gates version = .open → before.custody.gates version = .open) :
      Step plan mayClose before { before with custody := next }
  | changeCases (before : State Zone) (next : Zone → Prop)
      (qualifies : ∀ root, before.custody.roots root = .live → Qualifies plan next root) :
      Step plan mayClose before { before with credible := next }
  | effect (before : State Zone) (version : Nat) (issued : Issued before.custody version) :
      Step plan mayClose before { before with provider := applyDelete before.provider version }

theorem each_step_preserves_live_roots_and_their_physical_recovery
    (plan : Plan Input Zone) (mayClose : Nat → Prop) (before after : State Zone)
    (sound : Sound plan before) (event : Step plan mayClose before after) :
    Sound plan after := by
  cases event with
  | publish root ready =>
    refine ⟨SharedCustody.every_step_keeps_dependencies (closeAllowed := mayClose) sound.custody
      (.admit root ready.1 (publishing_requires_a_hold_for_each_exact_version plan before.custody
        before.credible root ready)), sound.backing, ?_⟩
    intro selected live
    by_cases same : selected = root
    · subst selected
      exact ready.2.2
    · apply sound.current selected
      simpa [setSlot, same] using live
  | maintain _ custody roots copies =>
    exact ⟨SharedCustody.every_step_keeps_dependencies sound.custody custody,
      fun version opened => sound.backing version (copies version opened),
      fun root live => sound.current root (roots root live)⟩
  | changeCases _ qualifies =>
    exact ⟨sound.custody, sound.backing, qualifies⟩
  | effect version issued =>
    exact ⟨sound.custody, WithdrawalRecovery.a_provider_effect_targets_only_an_excluded_version
      before.custody before.provider version sound.backing issued, sound.current⟩

theorem every_interleaving_preserves_the_current_obligation_set
    (plan : Plan Input Zone) (mayClose : Nat → Prop) (first last : State Zone)
    (trace : ScopeProtection.Trace (Step plan mayClose) first last)
    (start : Sound plan first) : Sound plan last := by
  induction trace with
  | nil => exact start
  | cons event _ ih => exact ih (each_step_preserves_live_roots_and_their_physical_recovery plan mayClose _ _ start event)

theorem every_live_root_has_a_backed_version_for_every_declared_input
    (plan : Plan Input Zone) (state : State Zone) (safe : Sound plan state)
    (root : Nat) (live : state.custody.roots root = .live)
    (input : Input) (required : plan.required root input) (lost : Zone) (credible : state.credible lost) :
    ∃ version, plan.needs root version ∧ plan.contains version input ∧
      plan.zoneOf version ≠ lost ∧ state.provider version = true := by
  obtain ⟨zone, distinct, version, part, exact, placement⟩ :=
    safe.current root live input required lost credible
  have held := safe.custody.complete root version live part
  exact ⟨version, part, exact, placement ▸ distinct,
    safe.backing version (safe.custody.referenceGate root version held)⟩

theorem a_pending_deletion_cannot_supply_a_publication_hold
    (plan : Plan Input Zone) (state : State Zone) (safe : Sound plan state)
    (root version : Nat) (required : plan.needs root version)
    (pending : Issued state.custody version) :
    ¬ CanPublish plan state.custody state.credible root := by
  intro ready
  have held := publishing_requires_a_hold_for_each_exact_version plan state.custody state.credible root ready version required
  exact SharedCustody.VersionPhase.noConfusion (pending.symm.trans (safe.custody.referenceGate root version held))

theorem a_held_registration_prevents_authorizing_withdrawal
    {Change Ticket : Type} (rules : WithdrawalRecovery.Rules Input Zone Change Ticket)
    (store : Store) (root version : Nat) (held : store.refs root version = .held) :
    ¬ WithdrawalRecovery.CanReserve rules store version := by
  intro withdraw
  exact withdraw.2.1.1 root held

theorem old_scope_qualification_is_insufficient_for_a_broader_publication
    (plan : Plan Input Zone) (state : State Zone) (root : Nat) (input : Input)
    (required : plan.required root input) (newLoss : Zone) (credible : state.credible newLoss)
    (missing : ¬ ScopeProtection.Coverage (Placements plan root) input newLoss) :
    ¬ CanPublish plan state.custody state.credible root := by
  intro ready
  exact missing (ready.2.2 input required newLoss credible)

theorem cancellation_without_acquisition_reply_closes_the_original_serial
    (table : RegistrationRecovery.Custodian) (serial : Nat) :
    RegistrationRecovery.ReferenceClosed (RegistrationRecovery.release table serial) serial :=
  (RegistrationRecovery.releasing_unknown_outcome_closes_exact_reference (table := table) serial).1

theorem cancellation_fences_delayed_grants_through_custodian_progress
    (issuer : RegistrationRecovery.Issuer) (first last : RegistrationRecovery.Custodian)
    (serial : Nat)
    (later : RegistrationRecovery.Trace issuer (RegistrationRecovery.release first serial) last) :
    RegistrationRecovery.ReferenceClosed last serial :=
  RegistrationRecovery.closed_reference_survives_arbitrary_delayed_actions later serial
    (cancellation_without_acquisition_reply_closes_the_original_serial first serial)

#print axioms publishing_requires_a_hold_for_each_exact_version
#print axioms a_closed_plan_cannot_publish
#print axioms narrower_envelope_keeps_the_held_plan_usable
#print axioms ordered_publication_uses_previously_observed_durable_grants
#print axioms each_step_preserves_live_roots_and_their_physical_recovery
#print axioms every_interleaving_preserves_the_current_obligation_set
#print axioms every_live_root_has_a_backed_version_for_every_declared_input
#print axioms a_pending_deletion_cannot_supply_a_publication_hold
#print axioms a_held_registration_prevents_authorizing_withdrawal
#print axioms old_scope_qualification_is_insufficient_for_a_broader_publication
#print axioms cancellation_without_acquisition_reply_closes_the_original_serial
#print axioms cancellation_fences_delayed_grants_through_custodian_progress

end DynamicProtection
