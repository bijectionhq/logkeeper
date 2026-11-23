import OrderedFaultInterval
import DurableInstall

set_option warningAsError true

namespace ProtectionHandoff

open OrderedFaultInterval (Cut Image Credible)
open ScopeProtection (Protects)

variable {Zone Input : Type}

structure Control (Zone Input : Type) where
  image : Image Zone
  owed : Input → Prop

def SameSeal (frozen mounted : Control Zone Input) : Prop :=
  frozen.image.cut = mounted.image.cut ∧
  frozen.image.interval = mounted.image.interval ∧ frozen.owed = mounted.owed

def ReopensLater (source : Image Zone) (destination : Cut) : Prop :=
  destination.lineage = source.cut.lineage ∧ source.cut.frontier < destination.frontier

def CanInstall (authorized : Prop) (frozen mounted : Control Zone Input) (destination : Cut)
    (retained : Input → Zone → Prop) : Prop :=
  authorized ∧ SameSeal frozen mounted ∧ ReopensLater mounted.image destination ∧
    Protects (Credible mounted.image.interval) mounted.owed retained

noncomputable def install (authorized : Prop) (frozen mounted : Control Zone Input) (destination : Cut)
    (retained : Input → Zone → Prop) : Option (Control Zone Input) := by
  classical
  exact if CanInstall authorized frozen mounted destination retained then
    some ⟨⟨destination, mounted.image.interval⟩, mounted.owed⟩ else none

theorem a_matching_mount_has_the_frozen_interval (frozen mounted : Control Zone Input)
    (exact : SameSeal frozen mounted) :
    frozen.image.interval = mounted.image.interval := by
  exact exact.2.1

theorem successful_install_preserves_the_frozen_obligation
    (authorized : Prop) (frozen mounted after : Control Zone Input) (destination : Cut)
    (retained : Input → Zone → Prop)
    (installed : install authorized frozen mounted destination retained = some after) :
    authorized ∧ after.image.cut = destination ∧
      after.image.cut.lineage = frozen.image.cut.lineage ∧
      after.image.interval = frozen.image.interval ∧ after.owed = frozen.owed ∧
      Protects (Credible after.image.interval) after.owed retained := by
  simp only [install] at installed
  split at installed
  · next allowed =>
    obtain ⟨authorized, exact, later, protectedAtCut⟩ := allowed
    cases installed
    exact ⟨authorized, rfl, later.1.trans (congrArg Cut.lineage exact.1.symm),
      (a_matching_mount_has_the_frozen_interval frozen mounted exact).symm, exact.2.2.symm, protectedAtCut⟩
  · cases installed

theorem a_ready_target_can_install_without_renewing_the_interval
    (authorized : Prop) (frozen : Control Zone Input) (destination : Cut)
    (retained : Input → Zone → Prop)
    (localInstall : authorized) (next : ReopensLater frozen.image destination)
    (covered : Protects (Credible frozen.image.interval) frozen.owed retained) :
    install authorized frozen frozen destination retained =
      some ⟨⟨destination, frozen.image.interval⟩, frozen.owed⟩ := by
  simp [install, CanInstall, SameSeal, localInstall, next, covered]

theorem cross_group_install_refines_the_existing_fence_and_carries_protection
    {Payload Voter : Type}
    {limits : Kernel.Limits} {prior : AuthorityRefinement.World Payload} {before : Kernel.State Payload}
    {membership : Nat → List Voter} {target : JournalRefinement.Journal Voter Payload}
    {certificate : AuthorityRefinement.Seal Payload}
    (oldFrozen : AuthorityRefinement.Refines prior before (some certificate))
    (frozen mounted after : Control Zone Input) (destination : Cut) (retained : Input → Zone → Prop)
    (namedBySeal : AuthorityRefinement.Seal Payload → Control Zone Input → Prop)
    (installed : install (DurableInstall.Activation limits prior membership target certificate ∧ namedBySeal certificate frozen)
      frozen mounted destination retained = some after) :
    Kernel.Step limits before target.logical ∧
    target.members = membership certificate.target.group ∧ namedBySeal certificate frozen ∧
    after.image.interval = frozen.image.interval ∧ after.owed = frozen.owed ∧
    Protects (Credible after.image.interval) after.owed retained := by
  obtain ⟨authorized, _, _, preserved, sameDebt, covered⟩ :=
    successful_install_preserves_the_frozen_obligation _ frozen mounted after destination retained installed
  obtain ⟨advance, _, _, voters⟩ := DurableInstall.activation_refines_and_preserves_durable_cut oldFrozen authorized.1
  exact ⟨advance, voters, authorized.2, preserved, sameDebt, covered⟩

theorem installation_refuses_control_from_another_interval
    (authorized : Prop) (frozen mounted : Control Zone Input) (destination : Cut)
    (retained : Input → Zone → Prop) (wrong : frozen.image.interval ≠ mounted.image.interval) :
    install authorized frozen mounted destination retained = none := by
  simp only [install]
  split
  · next allowed => exact False.elim (wrong (a_matching_mount_has_the_frozen_interval frozen mounted allowed.2.1))
  · rfl

theorem a_source_confirmation_can_use_the_carried_interval [DecidableEq Zone] {Proof : Type}
    (rules : OrderedFaultInterval.Rules Zone Proof)
    (before after : Control Zone Input) (ticket : OrderedFaultInterval.Confirmation Zone) (proof : Proof)
    (lineage : after.image.cut.lineage = before.image.cut.lineage)
    (carried : after.image.interval = before.image.interval)
    (matchesBefore : OrderedFaultInterval.SameInterval before.image ticket)
    (compatible : before.image.interval.loss = none ∨ before.image.interval.loss = some ticket.lost)
    (authentic : rules.confirms ticket proof) :
    ∃ changed, OrderedFaultInterval.apply rules after.image (.confirm ticket proof) = some changed := by
  have current : OrderedFaultInterval.SameInterval after.image ticket :=
    ⟨matchesBefore.1.trans lineage.symm, matchesBefore.2.trans (congrArg OrderedFaultInterval.Interval.start carried).symm⟩
  have compatibleAfter : after.image.interval.loss = none ∨ after.image.interval.loss = some ticket.lost := by
    rwa [carried]
  refine ⟨⟨OrderedFaultInterval.nextCut after.image, { after.image.interval with loss := some ticket.lost }⟩, ?_⟩
  simp [OrderedFaultInterval.apply, current, compatibleAfter, authentic]

#print axioms a_matching_mount_has_the_frozen_interval
#print axioms successful_install_preserves_the_frozen_obligation
#print axioms a_ready_target_can_install_without_renewing_the_interval
#print axioms cross_group_install_refines_the_existing_fence_and_carries_protection
#print axioms installation_refuses_control_from_another_interval
#print axioms a_source_confirmation_can_use_the_carried_interval

end ProtectionHandoff
