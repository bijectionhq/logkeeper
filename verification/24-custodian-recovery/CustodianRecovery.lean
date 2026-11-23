import JournalRefinement
import ChannelLifecycle
import CheckpointReconstruction

set_option warningAsError true

namespace CustodianRecovery

open SnapshotAdmission (setSlot)
open ChannelLifecycle (Key)
open RegistrationRecovery (Binding)

structure Image where
  incarnation : Nat
  channels : ChannelLifecycle.Store
  objects : SharedCustody.Store

structure CommittedImage (journal : JournalRefinement.Journal Replica Image) (image : Image) : Prop where
  recorded : ∃ lsn entry, lsn + 1 = journal.logical.history.length ∧
    journal.logical.firstRetained ≤ lsn ∧ journal.logical.history[lsn]? = some entry ∧ entry.bytes = image

theorem latest_committed_image_is_unique {journal : JournalRefinement.Journal Replica Image} {first second : Image}
    (left : CommittedImage journal first) (right : CommittedImage journal second) : first = second := by
  obtain ⟨a, leftEntry, leftHead, _, indexedLeft, imageLeft⟩ := left.recorded
  obtain ⟨b, rightEntry, rightHead, _, indexedRight, imageRight⟩ := right.recorded
  have sameIndex : a = b := by omega
  subst b
  have sameEntry := Option.some.inj (indexedLeft.symm.trans indexedRight)
  exact imageLeft.symm.trans ((congrArg Kernel.Entry.bytes sameEntry).trans imageRight)

theorem every_recovery_quorum_reads_the_whole_committed_image
    {journal : JournalRefinement.Journal Replica Image} {image : Image}
    (covered : JournalRefinement.CompleteCut journal) (ready : CommittedImage journal image)
    (available : Replica → Bool) (quorum : JournalRefinement.Majority journal.members available) :
    ∃ replica ∈ journal.members, available replica = true ∧
      ∃ lsn entry, lsn + 1 = journal.logical.history.length ∧ journal.copies replica lsn entry ∧
        entry.bytes = image := by
  obtain ⟨lsn, entry, head, retained, chosen, exactImage⟩ := ready.recorded
  obtain ⟨replica, member, up, found⟩ :=
    JournalRefinement.any_recovery_quorum_can_read_exact_entry covered available quorum retained chosen
  exact ⟨replica, member, up, lsn, entry, head, found, exactImage⟩

theorem any_current_quorum_can_replay_exact_custody_from_its_certified_base
    {engine : CheckpointReconstruction.Engine Image Payload Root}
    {journal : JournalRefinement.Journal Replica Payload}
    {base : CheckpointReconstruction.Image Image Payload Root}
    {target : CheckpointReconstruction.Cut} {records : List (Kernel.Entry Payload)}
    (coverage : JournalRefinement.CompleteCut journal)
    (certified : CheckpointReconstruction.Certified engine journal.logical base)
    (admitted : CheckpointReconstruction.Admitted engine journal.logical base target records)
    (atHead : target.next = journal.logical.history.length)
    (available : Replica → Bool) (quorum : JournalRefinement.Majority journal.members available) :
    (∀ lsn, base.cut.next ≤ lsn → lsn < target.next →
      ∃ replica ∈ journal.members, available replica = true ∧
        ∃ entry, journal.logical.history[lsn]? = some entry ∧ journal.copies replica lsn entry) ∧
    CheckpointReconstruction.replay engine base.root records =
      some (journal.logical.history.foldl engine.apply engine.origin) := by
  constructor
  · intro lsn begins ends
    have atRecord : lsn < journal.logical.history.length := atHead ▸ ends
    have chosen := List.getElem?_eq_getElem atRecord
    obtain ⟨replica, member, up, found⟩ :=
      JournalRefinement.any_recovery_quorum_can_read_exact_entry coverage available quorum
        (Nat.le_trans admitted.anchored begins) chosen
    exact ⟨replica, member, up, _, chosen, found⟩
  · rw [CheckpointReconstruction.admitted_replay_recovers_exact_cut certified admitted,
      CheckpointReconstruction.stateAt, atHead, List.take_length]

theorem one_zone_loss_keeps_exact_custody_recoverable
    {Zone : Type} [DecidableEq Zone] {journal : JournalRefinement.Journal Replica Image} {image : Image}
    (covered : JournalRefinement.CompleteCut journal) (ready : CommittedImage journal image)
    (zone : Replica → Zone) (lost : Zone) {a b c : Replica}
    (members : journal.members = [a,b,c]) (ab : zone a ≠ zone b) (ac : zone a ≠ zone c)
    (bc : zone b ≠ zone c) :
    ∃ replica ∈ journal.members, zone replica ≠ lost ∧
      ∃ lsn entry, lsn + 1 = journal.logical.history.length ∧ journal.copies replica lsn entry ∧
        entry.bytes = image := by
  let available := fun replica => decide (zone replica ≠ lost)
  have quorum : JournalRefinement.Majority journal.members available := by
    rw [members]
    exact JournalRefinement.distinct_zone_configuration_has_majority_after_loss zone lost a b c ab ac bc
  obtain ⟨replica, enrolled, up, remaining⟩ :=
    every_recovery_quorum_reads_the_whole_committed_image covered ready available quorum
  exact ⟨replica, enrolled, of_decide_eq_true up, remaining⟩

structure MembershipInstall (before : JournalRefinement.Journal Replica Image) (members : List Replica)
    (promised staleVotes : Replica → Bool) : Prop where
  fencedOld : JournalRefinement.Majority before.members promised
  rejects : ∀ replica ∈ before.members, promised replica = true → staleVotes replica = false
  completeNew : JournalRefinement.CompleteCut {before with members := members}

theorem membership_replacement_keeps_exact_image_and_excludes_old_commits
    {limits : Kernel.Limits} {before : JournalRefinement.Journal Replica Image} {image : Image}
    {newMembers : List Replica} {promised staleVotes : Replica → Bool}
    (ready : CommittedImage before image)
    (handoff : MembershipInstall before newMembers promised staleVotes) :
    ∃ after, JournalRefinement.Step limits before after ∧ after.members = newMembers ∧
      CommittedImage after image ∧ JournalRefinement.CompleteCut after ∧
      ¬ JournalRefinement.Majority before.members staleVotes := by
  have newCoverage : JournalRefinement.CompleteCut {before with members := newMembers} :=
    handoff.completeNew
  let after := {before with members := newMembers}
  exact ⟨after, .finalizeMembership newMembers newCoverage, rfl, ⟨ready.recorded⟩, newCoverage,
    JournalRefinement.durable_fence_excludes_stale_majority before.members promised staleVotes
      handoff.fencedOld handoff.rejects⟩

theorem active_key_can_be_fenced_before_its_acquisition_arrives
    {authority : ChannelLifecycle.Authority} {store : ChannelLifecycle.Store}
    {key : Key} {binding : Binding} {channel : ChannelLifecycle.Channel}
    (found : store.channels key.handle.route = some channel) (sameHandle : channel.handle = key.handle)
    (empty : store.grants key = none) (canceled : authority.mayRelease key binding) :
    let after := ChannelLifecycle.releaseGrant store key
    ChannelLifecycle.Step authority store after ∧ after.grants key = none ∧
      ChannelLifecycle.decideAcquire after key binding = .refuse := by
  let after := ChannelLifecycle.releaseGrant store key
  have noGrant : after.grants key = none := (ChannelLifecycle.release_clears_only_the_exact_key store key).1
  let updated := {channel with control := {channel.control with
    spent := setSlot channel.control.spent key.serial (decide (channel.control.floor < key.serial))}}
  have remains : after.channels key.handle.route = some updated := by
    simp [after, updated, ChannelLifecycle.releaseGrant, ChannelLifecycle.modifyControl, ChannelLifecycle.setGrant,
      found, sameHandle, setSlot]
  have rejects : ChannelLifecycle.decideAcquire after key binding = .refuse := by
    rw [ChannelLifecycle.active_requests_use_the_registration_gate remains sameHandle]
    have entryNone : (ChannelLifecycle.channelTable after updated).held key.serial = none := by
      have exactKey : (⟨updated.handle, key.serial⟩ : Key) = key := by
        cases key
        simp [updated, sameHandle]
      change after.grants ⟨updated.handle, key.serial⟩ = none
      rwa [exactKey]
    rw [RegistrationRecovery.acquire, entryNone]
    by_cases beyond : channel.control.floor < key.serial
    · simp [ChannelLifecycle.channelTable, updated, setSlot, beyond]
    · simp [ChannelLifecycle.channelTable, updated, beyond]
  exact ⟨.release key binding (.inl empty) canceled, noGrant, rejects⟩

theorem recovered_cancellation_keeps_refusing_the_exact_delayed_key
    {journal : JournalRefinement.Journal Replica Image} {before after : Image}
    {authority : ChannelLifecycle.Authority} {key : Key} {binding : Binding}
    {channel : ChannelLifecycle.Channel}
    (scopedChannel : before.channels.channels key.handle.route = some channel)
    (sameHandle : channel.handle = key.handle) (absent : before.channels.grants key = none)
    (canceled : authority.mayRelease key binding)
    (committed : CommittedImage journal {before with channels := ChannelLifecycle.releaseGrant before.channels key})
    (recovered : CommittedImage journal after) :
    after.channels.grants key = none ∧ ChannelLifecycle.decideAcquire after.channels key binding = .refuse := by
  have release := active_key_can_be_fenced_before_its_acquisition_arrives scopedChannel sameHandle absent canceled
  have matching := latest_committed_image_is_unique committed recovered
  subst after
  exact release.2

structure DeleteRequest where
  residence : Nat
  version : Nat

def permitsDeletion (image : Image) (request : DeleteRequest) : Prop :=
  request.residence = image.incarnation ∧ image.objects.gates request.version ≠ .open

theorem foreign_residence_is_refused {image : Image} {request : DeleteRequest}
    (foreignScope : request.residence ≠ image.incarnation) : ¬ permitsDeletion image request :=
  fun permit => foreignScope permit.1

theorem authorization_must_come_from_the_committed_residence_and_cut
    {journal : JournalRefinement.Journal Replica Image} {authorizing latest : Image}
    (proof : CommittedImage journal authorizing) (recovered : CommittedImage journal latest)
    (covered : JournalRefinement.CompleteCut journal) (request : DeleteRequest)
    (fenced : authorizing.objects.gates request.version = .deleting)
    (scope : request.residence = authorizing.incarnation)
    (available : Replica → Bool) (quorum : JournalRefinement.Majority journal.members available) :
    permitsDeletion latest request ∧
      ∃ replica ∈ journal.members, available replica = true ∧
        ∃ lsn entry, journal.copies replica lsn entry ∧ entry.bytes = latest := by
  have identical := latest_committed_image_is_unique proof recovered
  have negative : authorizing.objects.gates request.version ≠ .open := by
    rw [fenced]
    decide
  obtain ⟨replica, member, up, lsn, entry, _, found, bytes⟩ :=
    every_recovery_quorum_reads_the_whole_committed_image covered recovered available quorum
  exact ⟨identical ▸ ⟨scope, negative⟩, replica, member, up, lsn, entry, found, bytes⟩

theorem recovered_existing_reference_or_borrow_forbids_delete
    {needs : SharedCustody.Dependencies} {image : Image} {request : DeleteRequest}
    (valid : SharedCustody.Covered needs image.objects)
    (needed : (∃ root, image.objects.refs root request.version = .held) ∨
      0 < image.objects.borrows request.version) :
    ¬ permitsDeletion image request := by
  intro permit
  rcases needed with ⟨root, grant⟩ | borrowed
  · exact permit.2 (valid.referenceGate root request.version grant)
  · exact permit.2 (valid.borrowGate request.version borrowed)

theorem prior_committed_deletion_survives_later_custody_transitions
    {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop} {before after : Image}
    {request : DeleteRequest} (identity : after.incarnation = before.incarnation)
    (trace : SharedCustody.Trace needs closeAllowed before.objects after.objects)
    (permit : permitsDeletion before request) : permitsDeletion after request :=
  ⟨permit.1.trans identity.symm,
    SharedCustody.fenced_version_never_readmits trace request.version permit.2⟩

structure ProviderView where
  image : Image
  bytes : Nat → Bool

structure SoundMedia (view : ProviderView) : Prop where
  openPresent : ∀ version, view.image.objects.gates version = .open → view.bytes version = true
  goneAbsent : ∀ version, view.image.objects.gates version = .gone → view.bytes version = false

def deliver (view : ProviderView) (request : DeleteRequest) : ProviderView :=
  {view with bytes := setSlot view.bytes request.version false}

theorem authorized_provider_delete_preserves_every_open_version
    {view : ProviderView} {request : DeleteRequest}
    (sound : SoundMedia view) (permit : permitsDeletion view.image request) : SoundMedia (deliver view request) := by
  constructor
  · intro version openGate
    have fenced : view.image.objects.gates request.version ≠ .open := permit.2
    have other : version ≠ request.version :=
      fun alias => fenced (alias ▸ openGate)
    simpa [deliver, setSlot, other] using sound.openPresent version openGate
  · intro version gone
    by_cases same : version = request.version
    · simp [deliver, setSlot, same]
    · simpa [deliver, setSlot, same] using sound.goneAbsent version gone

theorem provider_delete_retry_is_idempotent (view : ProviderView) (request : DeleteRequest) :
    deliver (deliver view request) request = deliver view request := by
  unfold deliver
  congr 1
  funext version
  by_cases same : version = request.version <;> simp [setSlot, same]

def confirmed (view : ProviderView) (version : Nat) : ProviderView :=
  {view with image := {view.image with objects := {view.image.objects with
    gates := setSlot view.image.objects.gates version .gone
    physical := setSlot view.image.objects.physical version false}}}

theorem observed_exact_absence_can_commit_disposal
    {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop} {view : ProviderView} {version : Nat}
    (sound : SoundMedia view) (fenced : view.image.objects.gates version = .deleting)
    (receipt : view.bytes version = false) :
    SharedCustody.Step needs closeAllowed view.image.objects (confirmed view version).image.objects ∧
      SoundMedia (confirmed view version) := by
  refine ⟨.erase version fenced, ⟨?_, ?_⟩⟩
  · intro current openGate
    by_cases same : current = version
    · simp [confirmed, setSlot, same] at openGate
    · exact sound.openPresent current (by simpa [confirmed, setSlot, same] using openGate)
  · intro current gone
    by_cases same : current = version
    · exact same.symm ▸ receipt
    · exact sound.goneAbsent current (by simpa [confirmed, setSlot, same] using gone)

theorem recovering_metadata_preserves_inflight_provider_disposal
    {journal : JournalRefinement.Journal Replica Image} {view : ProviderView} {recovered : Image}
    {request : DeleteRequest} (before : CommittedImage journal view.image)
    (after : CommittedImage journal recovered)
    (sound : SoundMedia view) (permit : permitsDeletion view.image request) :
    permitsDeletion recovered request ∧ SoundMedia (deliver {view with image := recovered} request) := by
  have exactImage := latest_committed_image_is_unique before after
  subst recovered
  exact ⟨permit, authorized_provider_delete_preserves_every_open_version sound permit⟩

theorem provider_effect_completes_safely_after_exact_recovery
    {needs : SharedCustody.Dependencies} {closeAllowed : Nat → Prop}
    {journal : JournalRefinement.Journal Replica Image} {original : ProviderView} {loaded : Image}
    {request : DeleteRequest}
    (wasCommitted : CommittedImage journal original.image) (loadedAtHead : CommittedImage journal loaded)
    (sound : SoundMedia original) (scope : request.residence = original.image.incarnation)
    (fence : original.image.objects.gates request.version = .deleting) :
    let recovered := {original with image := loaded}
    let afterIO := deliver recovered request
    let verified := confirmed afterIO request.version
    permitsDeletion loaded request ∧ SharedCustody.Step needs closeAllowed loaded.objects verified.image.objects ∧
      SoundMedia verified ∧ verified.bytes request.version = false := by
  have exactImage := latest_committed_image_is_unique wasCommitted loadedAtHead
  subst loaded
  have permit : permitsDeletion original.image request :=
    ⟨scope, by rw [fence]; decide⟩
  have safeDelivery := authorized_provider_delete_preserves_every_open_version sound permit
  have absent : (deliver original request).bytes request.version = false := by simp [deliver, setSlot]
  have recorded := observed_exact_absence_can_commit_disposal (needs := needs)
    (closeAllowed := closeAllowed) safeDelivery fence absent
  exact ⟨permit, recorded.1, recorded.2, absent⟩

#print axioms latest_committed_image_is_unique
#print axioms every_recovery_quorum_reads_the_whole_committed_image
#print axioms any_current_quorum_can_replay_exact_custody_from_its_certified_base
#print axioms one_zone_loss_keeps_exact_custody_recoverable
#print axioms membership_replacement_keeps_exact_image_and_excludes_old_commits
#print axioms active_key_can_be_fenced_before_its_acquisition_arrives
#print axioms recovered_cancellation_keeps_refusing_the_exact_delayed_key
#print axioms foreign_residence_is_refused
#print axioms authorization_must_come_from_the_committed_residence_and_cut
#print axioms recovered_existing_reference_or_borrow_forbids_delete
#print axioms prior_committed_deletion_survives_later_custody_transitions
#print axioms authorized_provider_delete_preserves_every_open_version
#print axioms provider_delete_retry_is_idempotent
#print axioms observed_exact_absence_can_commit_disposal
#print axioms recovering_metadata_preserves_inflight_provider_disposal
#print axioms provider_effect_completes_safely_after_exact_recovery

end CustodianRecovery
