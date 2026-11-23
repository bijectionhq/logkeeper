import ProtectionHandoff

set_option warningAsError true

namespace CoverageWithdrawal

open ScopeProtection (Protects)

variable {Input Copy Zone : Type}

abbrev Locations (Input Copy : Type) := Input → Copy → Prop

structure State (Input Copy : Type) where
  witnesses : Locations Input Copy
  physical : Locations Input Copy
  pending : Copy → Prop

def zones (zoneOf : Copy → Zone) (copies : Locations Input Copy) : Input → Zone → Prop :=
  fun input zone => ∃ copy, copies input copy ∧ zoneOf copy = zone

def Without (locations : Locations Input Copy) (removed : Copy) : Locations Input Copy :=
  fun input copy => locations input copy ∧ copy ≠ removed

def Issued (state : State Input Copy) (removed : Copy) : Prop :=
  state.pending removed

structure Safe (credibleLoss : Zone → Prop) (owed : Input → Prop) (zoneOf : Copy → Zone)
    (state : State Input Copy) : Prop where
  held : ∀ input copy, state.witnesses input copy → state.physical input copy
  excl : ∀ input copy, state.pending copy → ¬ state.witnesses input copy
  covered : Protects credibleLoss owed (zones zoneOf state.witnesses)

inductive Step (credibleLoss : Zone → Prop) (owed : Input → Prop) (zoneOf : Copy → Zone) :
    State Input Copy → State Input Copy → Prop
  | reserve (before : State Input Copy) (removed : Copy)
      (registered : ∃ input, before.witnesses input removed)
      (covered : Protects credibleLoss owed (zones zoneOf (Without before.witnesses removed))) :
      Step credibleLoss owed zoneOf before { before with
        witnesses := Without before.witnesses removed
        pending := fun copy => before.pending copy ∨ copy = removed }
  | effect (before : State Input Copy) (removed : Copy) (issued : Issued before removed) :
      Step credibleLoss owed zoneOf before { before with physical := Without before.physical removed }
  | collect (before : State Input Copy) (removed : Copy)
      (disposed : ∀ input, ¬ before.physical input removed) :
      Step credibleLoss owed zoneOf before { before with pending := fun copy => before.pending copy ∧ copy ≠ removed }

theorem an_issued_effect_excludes_its_exact_identity
    (before : State Input Copy) (credibleLoss : Zone → Prop) (owed : Input → Prop)
    (zoneOf : Copy → Zone) (safe : Safe credibleLoss owed zoneOf before)
    (removed : Copy) (issued : Issued before removed) (input : Input) :
    ¬ before.witnesses input removed :=
  safe.excl input removed issued

theorem an_ordered_reservation_keeps_a_complete_survivor_set
    (before after : State Input Copy) (credibleLoss : Zone → Prop) (owed : Input → Prop)
    (zoneOf : Copy → Zone) (safe : Safe credibleLoss owed zoneOf before)
    (event : Step credibleLoss owed zoneOf before after) :
    Protects credibleLoss owed (zones zoneOf after.witnesses) := by
  cases event with
  | reserve _ _ covered => exact covered
  | effect => exact safe.covered
  | collect => exact safe.covered

theorem reservations_and_delayed_effects_preserve_coverage
    (before after : State Input Copy) (credibleLoss : Zone → Prop) (owed : Input → Prop)
    (zoneOf : Copy → Zone) (safe : Safe credibleLoss owed zoneOf before)
    (event : Step credibleLoss owed zoneOf before after) :
    Safe credibleLoss owed zoneOf after := by
  refine ⟨?_, ?_, an_ordered_reservation_keeps_a_complete_survivor_set before after credibleLoss owed zoneOf safe event⟩
  · cases event with
    | reserve _ _ _ => exact fun input copy held => safe.held input copy held.1
    | effect removed issued =>
      intro input copy held
      refine ⟨safe.held input copy held, ?_⟩
      intro wrong
      subst copy
      exact an_issued_effect_excludes_its_exact_identity before credibleLoss owed zoneOf safe removed issued input held
    | collect => exact safe.held
  · cases event with
    | reserve _ _ _ =>
      intro input copy retiring stillWitnessed
      rcases retiring with earlier | fresh
      · exact safe.excl input copy earlier stillWitnessed.1
      · exact stillWitnessed.2 fresh
    | effect => exact safe.excl
    | collect => exact fun input copy retiring => safe.excl input copy retiring.1

theorem safe_witnesses_entail_a_physical_survivor
    (state : State Input Copy) (credibleLoss : Zone → Prop) (owed : Input → Prop)
    (zoneOf : Copy → Zone) (safe : Safe credibleLoss owed zoneOf state)
    (input : Input) (required : owed input) (lost : Zone) (scenario : credibleLoss lost) :
    ∃ copy, zoneOf copy ≠ lost ∧ state.physical input copy := by
  obtain ⟨zone, distinct, copy, recorded, exactZone⟩ := safe.covered input required lost scenario
  exact ⟨copy, exactZone ▸ distinct, safe.held input copy recorded⟩

theorem every_effect_order_protects_a_continuing_obligation
    (credibleLoss : Zone → Prop) (owed : Input → Prop) (zoneOf : Copy → Zone)
    (first last : State Input Copy) (safe : Safe credibleLoss owed zoneOf first)
    (history : ScopeProtection.Trace (Step credibleLoss owed zoneOf) first last)
    (input : Input) (required : owed input) (lost : Zone) (scenario : credibleLoss lost) :
    ∃ copy, zoneOf copy ≠ lost ∧ last.physical input copy := by
  have invariant : Safe credibleLoss owed zoneOf last := by
    induction history with
    | nil => exact safe
    | cons event _ tail => exact tail (reservations_and_delayed_effects_preserve_coverage _ _ _ _ _ safe event)
  exact safe_witnesses_entail_a_physical_survivor last credibleLoss owed zoneOf invariant input required lost scenario

theorem installation_and_reserved_withdrawals_protect_the_original_promise
    (authorized : Prop) (frozen mounted after : ProtectionHandoff.Control Zone Input)
    (destination : OrderedFaultInterval.Cut) (zoneOf : Copy → Zone)
    (first last : State Input Copy)
    (installed : ProtectionHandoff.install authorized frozen mounted destination (zones zoneOf first.witnesses) =
      some after)
    (held : ∀ input copy, first.witnesses input copy → first.physical input copy)
    (excluded : ∀ input copy, first.pending copy → ¬ first.witnesses input copy)
    (history : ScopeProtection.Trace
      (Step (OrderedFaultInterval.Credible after.image.interval) after.owed zoneOf) first last)
    (input : Input) (required : frozen.owed input) (lost : Zone)
    (scenario : OrderedFaultInterval.Credible frozen.image.interval lost) :
    ∃ copy, zoneOf copy ≠ lost ∧ last.physical input copy := by
  obtain ⟨_, _, _, exactInterval, exactDebt, protectedAtInstall⟩ :=
    ProtectionHandoff.successful_install_preserves_the_frozen_obligation authorized frozen mounted after
      destination (zones zoneOf first.witnesses) installed
  exact every_effect_order_protects_a_continuing_obligation _ _ zoneOf first last
    ⟨held, excluded, protectedAtInstall⟩ history input (by rwa [exactDebt]) lost (by rwa [exactInterval])

#print axioms an_issued_effect_excludes_its_exact_identity
#print axioms an_ordered_reservation_keeps_a_complete_survivor_set
#print axioms reservations_and_delayed_effects_preserve_coverage
#print axioms safe_witnesses_entail_a_physical_survivor
#print axioms every_effect_order_protects_a_continuing_obligation

#print axioms installation_and_reserved_withdrawals_protect_the_original_promise

end CoverageWithdrawal
