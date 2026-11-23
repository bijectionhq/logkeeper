import ProviderIOClosure
import CertifiedActivationReplay

set_option warningAsError true

namespace DispositionBridge

open ProviderIOClosure (State Custody Sound StableAbsence HasCustody Covers)
open CertifiedActivationReplay (OriginalReceipts CertifiedOriginal AuthenticFences)

variable {Ticket Image Replica : Type}

structure Receipt (Ticket : Type) where
  copy : CopyFence.Receipt
  observed : State Ticket

def Scoped (expected : CopyFence.Receipt) (packet : Receipt Ticket) : Prop :=
  packet.copy = expected

def fromProvider (authentic : Receipt Ticket → Prop) : CertifiedActivationReplay.Disposition where
  absent := fun copy =>
    ∃ packet, authentic packet ∧ Scoped copy packet ∧ Sound packet.observed ∧ packet.observed.erased = true
  durablyCharged := fun copy =>
    ∃ packet, authentic packet ∧ Scoped copy packet ∧ Sound packet.observed ∧ HasCustody packet.observed

theorem a_disposition_cannot_be_used_for_another_copy
    {expected : CopyFence.Receipt} {packet : Receipt Ticket}
    (matchesCopy : Scoped expected packet) (foreign : packet.copy ≠ expected) : False := by
  have same : packet.copy = expected := by
    exact matchesCopy
  exact foreign same

theorem disposition_remains_safe_under_delayed_delivery
    [DecidableEq Ticket] {authentic : Receipt Ticket → Prop} {copy : CopyFence.Receipt}
    {reserve : Custody Ticket → Prop} {current : State Ticket}
    (progress : ∀ packet, authentic packet → Scoped copy packet →
      ProviderIOClosure.Trace reserve packet.observed current)
    (received : (fromProvider authentic).absent copy ∨ (fromProvider authentic).durablyCharged copy) :
    StableAbsence current ∨ ∃ custody, current.custodian = some custody ∧ Covers current custody := by
  rcases received with ⟨packet, identity, matchesCopy, sound, erased⟩ |
    ⟨packet, identity, matchesCopy, sound, charge⟩
  · exact .inl (ProviderIOClosure.no_write_can_recreate_a_certified_erasure sound erased
      (progress packet identity matchesCopy)).2
  · have trace := progress packet identity matchesCopy
    have covered := ProviderIOClosure.sound_trace sound trace
    rcases ProviderIOClosure.a_prior_custody_receipt_stays_valid_through_erasure charge trace with erased |
      ⟨custody, installed⟩
    · exact .inl (covered.erasure erased)
    · exact .inr ⟨custody, installed, covered.custody custody installed⟩

theorem matched_provider_disposition_can_drive_target_cleanup
    {base : IntentRetirement.Evidence Image} {original : OriginalReceipts Image}
    {authority : Nat → ChannelLifecycle.Authority}
    {journalAuth : Nat → JournalRefinement.Journal Replica CustodianRecovery.Image → Prop}
    {authentic : Receipt Ticket → Prop} {state : ActivationComposition.State Image}
    {key : IntentRetirement.CopyKey} {image : Image} {owner : Nat}
    (current : ActivationComposition.CanWrite state owner)
    (planned : state.store.jobs key = some image)
    (sound : AuthenticFences
      (CertifiedActivationReplay.settleFromCustodian base original authority journalAuth (fromProvider authentic)) state)
    (registeredFence : ∃ journal, journalAuth key.custodian journal ∧
      key.custodian = (original key image).key.handle.custodian ∧ JournalRefinement.CompleteCut journal ∧
      CopyFence.CommittedRelease journal (authority key.custodian) (original key image))
    (received : (fromProvider authentic).absent (original key image) ∨
      (fromProvider authentic).durablyCharged (original key image)) :
    let evidence := CertifiedActivationReplay.settleFromCustodian base original authority journalAuth (fromProvider authentic)
    ∃ after, ActivationComposition.Trace evidence state after ∧ after.store.jobs key = none := by
  exact CertifiedActivationReplay.a_current_owner_can_order_the_certified_custodian_receipt current
    planned sound (⟨registeredFence, received⟩ : CertifiedOriginal original authority journalAuth
      (fromProvider authentic) key image)

#print axioms a_disposition_cannot_be_used_for_another_copy
#print axioms disposition_remains_safe_under_delayed_delivery
#print axioms matched_provider_disposition_can_drive_target_cleanup

end DispositionBridge
