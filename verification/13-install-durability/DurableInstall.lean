import AuthorityRefinement
import JournalRefinement

set_option warningAsError true

namespace DurableInstall

open Kernel
open AuthorityRefinement
open JournalRefinement

structure ReadyImage (target : Journal Replica Payload) (certificate : Seal Payload) : Prop where
  exactImage : target.logical = installed certificate
  dataQuorum : CompleteCut target

inductive Activation (limits : Limits) (prior : World Payload)
    (currentMembership : Nat → List Replica) (target : Journal Replica Payload)
    (certificate : Seal Payload) : Prop
  | accepted (regionCanInstall : AuthorityRefinement.Step limits prior (installAt prior certificate))
      (matchesImage : target.logical = installed certificate)
      (copiesAtActivation : CompleteCut target)
      (adoptedMembers : target.members = currentMembership certificate.target.group) :
      Activation limits prior currentMembership target certificate

private theorem projection_points_at_state {state observed : State Payload} {group : Nat}
    (row : localAt state group = some observed) : state = observed := by
  unfold localAt at row
  split at row
  next =>
    split at row
    next => exact Option.some.inj row
    next => simp at row
  next => simp at row

theorem activation_refines_and_preserves_durable_cut
    {limits : Limits} {prior : World Payload} {before : State Payload}
    {currentMembership : Nat → List Replica}
    {target : Journal Replica Payload} {certificate : Seal Payload}
    (sealed : Refines prior before (some certificate))
    (handoff : Activation limits prior currentMembership target certificate) :
    Kernel.Step limits before target.logical ∧
      (installAt prior certificate).rows certificate.target.group = some target.logical ∧
      CompleteCut target ∧ target.members = currentMembership certificate.target.group := by
  cases handoff with
  | accepted regionCanInstall matchesImage copiesAtActivation adoptedMembers =>
      obtain ⟨after, pending, stutters | logicalStep, related⟩ :=
        AuthorityRefinement.step_refines sealed regionCanInstall
      · subst after
        have oldCut := sealed.phase.2.1
        have noRow : localAt before certificate.target.group = none := by
          simp [oldCut, frozen, localAt]
        have activeRow : (installAt prior certificate).rows certificate.target.group =
            some (installed certificate) := by simp [installAt, replace]
        rw [related.rows, noRow] at activeRow
        contradiction
      · have activeRow : (installAt prior certificate).rows certificate.target.group =
            some (installed certificate) := by simp [installAt, replace]
        have equal : after = installed certificate := by
          apply projection_points_at_state
          rwa [related.rows] at activeRow
        have certifiedImage : target.logical = installed certificate := matchesImage
        rw [← certifiedImage] at equal activeRow
        exact ⟨equal ▸ logicalStep, activeRow, copiesAtActivation, adoptedMembers⟩

theorem prepared_image_can_activate {limits : Limits} {prior : World Payload}
    {before : State Payload} {currentMembership : Nat → List Replica}
    {target : Journal Replica Payload} {certificate : Seal Payload}
    (sealed : Refines prior before (some certificate)) (ready : ReadyImage target certificate)
    (adopted : target.members = currentMembership certificate.target.group) :
    Activation limits prior currentMembership target certificate := by
  obtain ⟨authentic, _, live⟩ := sealed.phase
  exact .accepted (.install certificate authentic live) ready.exactImage ready.dataQuorum adopted

theorem every_available_quorum_recovers_after_activation
    {limits : Limits} {prior : World Payload} {before : State Payload}
    {currentMembership : Nat → List Replica}
    {target : Journal Replica Payload} {certificate : Seal Payload}
    (sealed : Refines prior before (some certificate))
    (handoff : Activation limits prior currentMembership target certificate)
    (available : Replica → Bool)
    (quorum : Majority (currentMembership certificate.target.group) available)
    {lsn : Nat} {entry : Entry Payload} (retained : target.logical.firstRetained ≤ lsn)
    (committed : target.logical.history[lsn]? = some entry) :
    ∃ replica ∈ currentMembership certificate.target.group,
      available replica = true ∧ target.copies replica lsn entry := by
  obtain ⟨_, _, cut, actual⟩ := activation_refines_and_preserves_durable_cut sealed handoff
  rw [← actual] at quorum ⊢
  exact any_recovery_quorum_can_read_exact_entry cut available quorum retained committed

theorem registered_image_stays_ready
    {limits : Limits} {prior current : Journal Replica Payload} {certificate : Seal Payload}
    (registered : ReadyImage prior certificate)
    (transitions : JournalRefinement.Trace limits prior current)
    (immutable : current.logical = prior.logical) :
    ReadyImage current certificate := by
  obtain ⟨_, cut⟩ := trace_refines_and_preserves_cut registered.dataQuorum transitions
  exact ⟨immutable.trans registered.exactImage, cut⟩

#print axioms activation_refines_and_preserves_durable_cut
#print axioms prepared_image_can_activate
#print axioms every_available_quorum_recovers_after_activation
#print axioms registered_image_stays_ready

end DurableInstall
