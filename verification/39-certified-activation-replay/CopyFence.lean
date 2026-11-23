import CustodianRecovery

set_option warningAsError true

namespace CopyFence

open SnapshotAdmission (setSlot)
open ChannelLifecycle (Key Handle Channel Control Store Authority)
open RegistrationRecovery (Binding)

def ClosedSerial (control : Control) (serial : Nat) : Prop :=
  serial ≤ control.floor ∨ control.spent serial = true

structure Closed (store : Store) (key : Key) : Prop where
  empty : store.grants key = none
  issued : key.handle.nonce ≤ store.issued
  fenced : ∀ channel, store.channels key.handle.route = some channel →
    channel.handle = key.handle → ClosedSerial channel.control key.serial

theorem closed_copy_refuses_every_binding {store : Store} {key : Key}
    (closed : Closed store key) (binding : Binding) :
    ChannelLifecycle.decideAcquire store key binding = .refuse := by
  cases found : store.channels key.handle.route with
  | none => simp [ChannelLifecycle.decideAcquire, closed.empty, found]
  | some channel =>
      by_cases same : channel.handle = key.handle
      · rw [ChannelLifecycle.active_requests_use_the_registration_gate found same]
        have empty : (ChannelLifecycle.channelTable store channel).held key.serial = none := by
          change store.grants ⟨channel.handle, key.serial⟩ = none
          simpa [same] using closed.empty
        rw [RegistrationRecovery.acquire, empty]
        rcases closed.fenced channel found same with below | spent
        · simp [ChannelLifecycle.channelTable, Nat.not_lt.mpr below]
        · simp [ChannelLifecycle.channelTable, spent]
      · simp [ChannelLifecycle.decideAcquire, closed.empty, found, same]

private theorem changing_control_preserves_closed_key {store : Store} {key : Key}
    (closed : Closed store key) (handle : Handle) (update : Control → Control)
    (keeps : ∀ control, ClosedSerial control key.serial → ClosedSerial (update control) key.serial) :
    Closed (ChannelLifecycle.modifyControl store handle update) key := by
  cases found : store.channels handle.route with
  | none => simpa [ChannelLifecycle.modifyControl, found] using closed
  | some channel =>
      by_cases matchesHandle : channel.handle = handle
      · let updated := {channel with control := update channel.control}
        have modified : ChannelLifecycle.modifyControl store handle update =
            {store with channels := setSlot store.channels handle.route (some updated)} := by
          simp [ChannelLifecycle.modifyControl, found, matchesHandle, updated]
        rw [modified]
        refine ⟨closed.empty, closed.issued, ?_⟩
        intro other observed matchesKey
        by_cases sameRoute : key.handle.route = handle.route
        · have equal : updated = other := by
            simpa [setSlot, sameRoute] using observed
          subst other
          exact keeps _ (closed.fenced channel (by simpa [sameRoute] using found) matchesKey)
        · exact closed.fenced other (by simpa [setSlot, sameRoute] using observed) matchesKey
      · simpa [ChannelLifecycle.modifyControl, found, matchesHandle] using closed

private theorem channel_close_only_removes_rows {store : Store} {handle : Handle} {route : Nat}
    {channel : Channel} (found : (ChannelLifecycle.closeChannel store handle).channels route = some channel) :
    store.channels route = some channel := by
  by_cases exact : ChannelLifecycle.activeHandle store handle.route = some handle
  · by_cases sameRoute : route = handle.route
    · simp [ChannelLifecycle.closeChannel, exact, setSlot, sameRoute] at found
    · simpa [ChannelLifecycle.closeChannel, exact, setSlot, sameRoute] using found
  · simpa [ChannelLifecycle.closeChannel, exact] using found

private theorem spending_keeps_other_fences (control : Control) (closing observed : Nat)
    (closed : ClosedSerial control observed) :
    ClosedSerial {control with spent := setSlot control.spent closing (decide (control.floor < closing))} observed := by
  by_cases same : observed = closing
  · subst observed
    by_cases above : control.floor < closing
    · exact Or.inr (by simp [setSlot, above])
    · exact Or.inl (Nat.le_of_not_gt above)
  · rcases closed with below | spent
    · exact Or.inl below
    · exact Or.inr (by simpa [setSlot, same] using spent)

theorem a_copy_fence_survives_every_custodian_step {authority : Authority} {before after : Store} {key : Key}
    (closed : Closed before key) (step : ChannelLifecycle.Step authority before after) : Closed after key := by
  cases step with
  | mint route issuer _ _ _ =>
      refine ⟨closed.empty, Nat.le_trans closed.issued (Nat.le_succ _), ?_⟩
      intro channel found same
      by_cases sameRoute : key.handle.route = route
      · have equal :
            (⟨ChannelLifecycle.freshHandle before authority.custodian route issuer, ⟨0, fun _ => false⟩⟩ :
              Channel) = channel := by
            simpa [ChannelLifecycle.openChannel, setSlot, sameRoute] using found
        subst channel
        have fresh := congrArg Handle.nonce same
        change before.issued + 1 = key.handle.nonce at fresh
        have within := closed.issued
        omega
      · exact closed.fenced channel (by simpa [ChannelLifecycle.openChannel, setSlot, sameRoute] using found) same
  | close handle _ =>
      refine ⟨by simpa [ChannelLifecycle.channel_close_preserves_all_pins] using closed.empty, ?_, ?_⟩
      · unfold ChannelLifecycle.closeChannel
        split <;> exact closed.issued
      · exact fun channel found same => closed.fenced channel (channel_close_only_removes_rows found) same
  | credit receipt _ =>
      apply changing_control_preserves_closed_key closed
      intro control prior
      by_cases below : key.serial ≤ max control.floor receipt.through
      · exact Or.inl below
      · rcases prior with oldFloor | spent
        · exact False.elim (below (Nat.le_trans oldFloor (Nat.le_max_left ..)))
        · exact Or.inr (by simp [below, spent])
  | acquire added binding _ _ eligible =>
      have different : key ≠ added := by
        intro same
        subst added
        rw [closed_copy_refuses_every_binding closed binding] at eligible
        cases eligible
      exact ⟨by simp [ChannelLifecycle.setGrant, different, closed.empty], closed.issued, closed.fenced⟩
  | release original _ _ _ =>
      have cleared : Closed (ChannelLifecycle.setGrant before original none) key := by
        refine ⟨?_, closed.issued, closed.fenced⟩
        by_cases same : key = original <;> simp [ChannelLifecycle.setGrant, same, closed.empty]
      exact changing_control_preserves_closed_key cleared original.handle _
        (fun control prior => spending_keeps_other_fences control original.serial key.serial prior)

theorem a_copy_fence_survives_arbitrary_custodian_traces {authority : Authority} {first last : Store} {key : Key}
    (closed : Closed first key) (trace : ChannelLifecycle.Trace authority first last) : Closed last key := by
  induction trace with
  | same => exact closed
  | next _ step prior => exact a_copy_fence_survives_every_custodian_step prior step

theorem releasing_an_issued_key_establishes_a_fence {store : Store} {key : Key}
    (issued : key.handle.nonce ≤ store.issued) : Closed (ChannelLifecycle.releaseGrant store key) key := by
  refine ⟨(ChannelLifecycle.release_clears_only_the_exact_key store key).1, ?_, ?_⟩
  · cases found : store.channels key.handle.route with
    | none => simpa [ChannelLifecycle.releaseGrant, ChannelLifecycle.modifyControl, ChannelLifecycle.setGrant, found] using issued
    | some channel =>
        by_cases same : channel.handle = key.handle <;>
          simpa [ChannelLifecycle.releaseGrant, ChannelLifecycle.modifyControl, ChannelLifecycle.setGrant, found, same] using issued
  · intro observed foundAfter matchesKey
    cases found : store.channels key.handle.route with
    | none =>
        simp [ChannelLifecycle.releaseGrant, ChannelLifecycle.modifyControl, ChannelLifecycle.setGrant, found] at foundAfter
    | some channel =>
        by_cases same : channel.handle = key.handle
        · let spent := setSlot channel.control.spent key.serial (decide (channel.control.floor < key.serial))
          have equal : {channel with control := {channel.control with spent}} = observed := by
            simpa [ChannelLifecycle.releaseGrant, ChannelLifecycle.modifyControl,
              ChannelLifecycle.setGrant, found, same, spent, setSlot] using foundAfter
          subst observed
          by_cases above : channel.control.floor < key.serial
          · exact Or.inr (by simp [spent, setSlot, above])
          · exact Or.inl (Nat.le_of_not_gt above)
        · have equal : channel = observed := by
            simpa [ChannelLifecycle.releaseGrant, ChannelLifecycle.modifyControl, ChannelLifecycle.setGrant, found, same] using foundAfter
          subst observed
          exact False.elim (same matchesKey)

structure Receipt where
  key : Key
  binding : Binding
  deriving DecidableEq

def MatchesPlan (original evidence : Receipt) : Prop :=
  evidence = original

structure CommittedRelease (journal : JournalRefinement.Journal Replica CustodianRecovery.Image)
    (authority : Authority) (receipt : Receipt) : Prop where
  proof : ∃ before : CustodianRecovery.Image,
    before.incarnation = receipt.key.handle.custodian ∧ authority.custodian = before.incarnation ∧
    receipt.key.handle.nonce ≤ before.channels.issued ∧
    (before.channels.grants receipt.key = none ∨ before.channels.grants receipt.key = some receipt.binding) ∧
    authority.mayRelease receipt.key receipt.binding ∧
    CustodianRecovery.CommittedImage journal
      {before with channels := ChannelLifecycle.releaseGrant before.channels receipt.key}

theorem recovered_original_receipt_closes_the_exact_copy
    {journal : JournalRefinement.Journal Replica CustodianRecovery.Image} {authority : Authority}
    {original evidence : Receipt} (matchesPlan : MatchesPlan original evidence)
    (released : CommittedRelease journal authority evidence) {loaded : CustodianRecovery.Image}
    (atHead : CustodianRecovery.CommittedImage journal loaded)
    (coverage : JournalRefinement.CompleteCut journal)
    (available : Replica → Bool) (quorum : JournalRefinement.Majority journal.members available) :
    Closed loaded.channels original.key ∧ loaded.incarnation = original.key.handle.custodian ∧
    ∃ voter ∈ journal.members, available voter = true ∧
      ∃ lsn entry, journal.copies voter lsn entry ∧ entry.bytes = loaded := by
  obtain ⟨before, residence, _, issued, _, _, committed⟩ := released.proof
  have exact := CustodianRecovery.latest_committed_image_is_unique committed atHead
  obtain ⟨voter, member, up, lsn, entry, _, copied, bytes⟩ :=
    CustodianRecovery.every_recovery_quorum_reads_the_whole_committed_image coverage atHead available quorum
  have closed : Closed loaded.channels evidence.key :=
    exact ▸ releasing_an_issued_key_establishes_a_fence issued
  have exactReceipt : evidence = original := by
    exact matchesPlan
  exact ⟨exactReceipt ▸ closed, exactReceipt ▸ (exact ▸ residence), voter, member, up, lsn, entry, copied, bytes⟩

#print axioms closed_copy_refuses_every_binding
#print axioms a_copy_fence_survives_every_custodian_step
#print axioms a_copy_fence_survives_arbitrary_custodian_traces
#print axioms releasing_an_issued_key_establishes_a_fence
#print axioms recovered_original_receipt_closes_the_exact_copy

end CopyFence
