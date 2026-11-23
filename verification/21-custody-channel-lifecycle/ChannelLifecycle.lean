import RegistrationRecovery

set_option warningAsError true

namespace ChannelLifecycle

open SnapshotAdmission (setSlot)
open RegistrationRecovery (Binding Decision)

structure Handle where
  custodian : Nat
  route : Nat
  issuer : Nat
  nonce : Nat
  deriving DecidableEq

structure Key where
  handle : Handle
  serial : Nat
  deriving DecidableEq

structure Control where
  floor : Nat
  spent : Nat → Bool

structure Channel where
  handle : Handle
  control : Control

structure Store where
  issued : Nat
  channels : Nat → Option Channel
  grants : Key → Option Binding

structure FloorReceipt where
  handle : Handle
  through : Nat

structure Authority where
  custodian : Nat
  routeLimit : Nat
  mayOpen : Nat → Nat → Prop
  mayClose : Handle → Prop
  planned : Key → Binding → Prop
  mayPin : Store → Prop
  mayRelease : Key → Binding → Prop
  installedFloor : FloorReceipt → Prop

def activeHandle (store : Store) (route : Nat) : Option Handle :=
  (store.channels route).map Channel.handle

def freshHandle (store : Store) (custodian route issuer : Nat) : Handle :=
  ⟨custodian, route, issuer, store.issued + 1⟩

def openChannel (store : Store) (custodian route issuer : Nat) : Store :=
  {store with
    issued := store.issued + 1
    channels := setSlot store.channels route
      (some ⟨freshHandle store custodian route issuer, ⟨0, fun _ => false⟩⟩)}

def closeChannel (store : Store) (handle : Handle) : Store :=
  if activeHandle store handle.route = some handle then
    {store with channels := setSlot store.channels handle.route none}
  else store

def modifyControl (store : Store) (handle : Handle) (update : Control → Control) : Store :=
  match store.channels handle.route with
  | some channel =>
      if channel.handle = handle then
        {store with
          channels := setSlot store.channels handle.route (some {channel with control := update channel.control})}
      else store
  | none => store

def receiveFloor (store : Store) (receipt : FloorReceipt) : Store :=
  modifyControl store receipt.handle fun control =>
    let floor := max control.floor receipt.through
    ⟨floor, fun id => if id ≤ floor then false else control.spent id⟩

def channelTable (store : Store) (channel : Channel) : RegistrationRecovery.Custodian :=
  ⟨channel.control.floor, fun serial => store.grants ⟨channel.handle, serial⟩, channel.control.spent⟩

def decideAcquire (store : Store) (key : Key) (binding : Binding) : Decision :=
  match store.grants key with
  | some held => if binding = held then .replay else .refuse
  | none =>
      match store.channels key.handle.route with
      | some channel =>
          if channel.handle = key.handle then
            RegistrationRecovery.acquire (channelTable store channel) key.serial binding
          else .refuse
      | none => .refuse

def setGrant (store : Store) (key : Key) (binding : Option Binding) : Store :=
  {store with grants := fun candidate => if candidate = key then binding else store.grants candidate}

def releaseGrant (store : Store) (key : Key) : Store :=
  modifyControl (setGrant store key none) key.handle fun control =>
    {control with spent := setSlot control.spent key.serial (decide (control.floor < key.serial))}

inductive Step (authority : Authority) : Store → Store → Prop
  | mint {store} (route issuer : Nat) (empty : store.channels route = none)
      (room : route < authority.routeLimit) (authorized : authority.mayOpen route issuer) :
      Step authority store (openChannel store authority.custodian route issuer)
  | close {store} (handle : Handle) (authorized : authority.mayClose handle) :
      Step authority store (closeChannel store handle)
  | credit {store} (receipt : FloorReceipt) (authenticated : authority.installedFloor receipt) :
      Step authority store (receiveFloor store receipt)
  | acquire {store} (key : Key) (binding : Binding)
      (planned : authority.planned key binding) (room : authority.mayPin store)
      (granted : decideAcquire store key binding = .admit) :
      Step authority store (setGrant store key (some binding))
  | release {store} (key : Key) (binding : Binding)
      (compatible : store.grants key = none ∨ store.grants key = some binding)
      (closed : authority.mayRelease key binding) :
      Step authority store (releaseGrant store key)

inductive Trace (authority : Authority) : Store → Store → Prop
  | same (store : Store) : Trace authority store store
  | next {first before after} : Trace authority first before → Step authority before after →
      Trace authority first after

theorem stale_close_changes_nothing {store : Store} {handle : Handle}
    (mismatch : activeHandle store handle.route ≠ some handle) : closeChannel store handle = store := by
  simp [closeChannel, mismatch]

theorem stale_credit_changes_nothing {store : Store} {receipt : FloorReceipt}
    (mismatch : activeHandle store receipt.handle.route ≠ some receipt.handle) :
    receiveFloor store receipt = store := by
  cases found : store.channels receipt.handle.route with
  | none => simp [receiveFloor, modifyControl, found]
  | some channel =>
      have different : channel.handle ≠ receipt.handle := by
        simpa [activeHandle, found] using mismatch
      simp [receiveFloor, modifyControl, found, different]

theorem active_requests_use_the_registration_gate {store : Store} {key : Key} {binding : Binding}
    {channel : Channel} (found : store.channels key.handle.route = some channel)
    (sameHandle : channel.handle = key.handle) :
    decideAcquire store key binding =
      RegistrationRecovery.acquire (channelTable store channel) key.serial binding := by
  cases held : store.grants key <;> simp [decideAcquire, held, found, sameHandle, channelTable,
    RegistrationRecovery.acquire]

theorem existing_grant_retries_without_channel_metadata {store : Store} {key : Key}
    {binding other : Binding} (held : store.grants key = some binding) :
    decideAcquire store key binding = .replay ∧
      (other ≠ binding → decideAcquire store key other = .refuse) := by
  simp [decideAcquire, held]

private theorem absent_grant_with_stale_handle_is_refused {store : Store} {key : Key}
    (empty : store.grants key = none)
    (stale : activeHandle store key.handle.route ≠ some key.handle) (binding : Binding) :
    decideAcquire store key binding = .refuse := by
  cases found : store.channels key.handle.route with
  | none => simp [decideAcquire, empty, found]
  | some channel =>
      have different : channel.handle ≠ key.handle := by
        simpa [activeHandle, found] using stale
      simp [decideAcquire, empty, found, different]

private theorem fresh_admission_requires_an_empty_matching_channel {store : Store} {key : Key}
    {binding : Binding} (accepted : decideAcquire store key binding = .admit) :
    store.grants key = none ∧ activeHandle store key.handle.route = some key.handle := by
  cases held : store.grants key with
  | some current =>
      by_cases bindingMatches : binding = current <;> simp [decideAcquire, held, bindingMatches] at accepted
  | none =>
      refine ⟨rfl, ?_⟩
      by_cases current : activeHandle store key.handle.route = some key.handle
      · exact current
      · exact Decision.noConfusion (accepted.symm.trans (absent_grant_with_stale_handle_is_refused held current binding))

private theorem modify_control_keeps_handle (store : Store) (handle : Handle)
    (update : Control → Control) (route : Nat) :
    activeHandle (modifyControl store handle update) route = activeHandle store route := by
  cases found : store.channels handle.route with
  | none => simp [modifyControl, found]
  | some channel =>
      by_cases sameHandle : channel.handle = handle
      · by_cases same : route = handle.route
        · simp [modifyControl, found, sameHandle, activeHandle, setSlot, same]
        · simp [modifyControl, found, sameHandle, activeHandle, setSlot, same]
      · simp [modifyControl, found, sameHandle]

private theorem modify_control_keeps_grants (store : Store) (handle : Handle)
    (update : Control → Control) : (modifyControl store handle update).grants = store.grants := by
  cases found : store.channels handle.route with
  | none => simp [modifyControl, found]
  | some channel =>
      by_cases sameHandle : channel.handle = handle <;> simp [modifyControl, found, sameHandle]

private theorem modify_control_keeps_issued (store : Store) (handle : Handle)
    (update : Control → Control) : (modifyControl store handle update).issued = store.issued := by
  cases found : store.channels handle.route with
  | none => simp [modifyControl, found]
  | some channel =>
      by_cases sameHandle : channel.handle = handle <;> simp [modifyControl, found, sameHandle]

private theorem close_only_removes_a_handle {store : Store} {closing existing : Handle} {route : Nat}
    (after : activeHandle (closeChannel store closing) route = some existing) :
    activeHandle store route = some existing := by
  by_cases sameHandle : activeHandle store closing.route = some closing
  · have closed : closeChannel store closing =
        {store with channels := setSlot store.channels closing.route none} := by simp [closeChannel, sameHandle]
    rw [closed] at after
    by_cases same : route = closing.route
    · simp [activeHandle, setSlot, same] at after
    · simpa [activeHandle, setSlot, same] using after
  · simpa [closeChannel, sameHandle] using after

theorem channel_close_preserves_all_pins (store : Store) (handle : Handle) :
    (closeChannel store handle).grants = store.grants := by
  by_cases sameHandle : activeHandle store handle.route = some handle <;> simp [closeChannel, sameHandle]

theorem release_clears_only_the_exact_key (store : Store) (key : Key) :
    (releaseGrant store key).grants key = none ∧
      ∀ other, other ≠ key → (releaseGrant store key).grants other = store.grants other := by
  unfold releaseGrant
  rw [modify_control_keeps_grants]
  exact ⟨by simp [setGrant], fun other different => by simp [setGrant, different]⟩

private theorem release_keeps_active_handle (store : Store) (key : Key) (route : Nat) :
    activeHandle (releaseGrant store key) route = activeHandle store route := by
  unfold releaseGrant
  rw [modify_control_keeps_handle]
  rfl

theorem grant_survives_each_step_or_has_exact_release_authority {authority : Authority}
    {before after : Store} (effect : Step authority before after)
    {key : Key} {binding : Binding} (held : before.grants key = some binding) :
    after.grants key = some binding ∨ authority.mayRelease key binding := by
  cases effect with
  | mint _ _ _ _ _ => exact .inl held
  | close _ _ => exact .inl (by simpa [channel_close_preserves_all_pins] using held)
  | credit _ _ => exact .inl (by simpa [receiveFloor, modify_control_keeps_grants] using held)
  | acquire added _ _ _ accepted =>
      have different : key ≠ added := by
        intro same
        subst added
        have empty := (fresh_admission_requires_an_empty_matching_channel accepted).1
        have impossible : some binding = none := held.symm.trans empty
        cases impossible
      exact .inl (by simpa [setGrant, different] using held)
  | release released prior receipt permitted =>
      by_cases same : key = released
      · subst released
        rcases receipt with absent | exactBinding
        · have impossible : some binding = none := held.symm.trans absent
          cases impossible
        · have identical : binding = prior := Option.some.inj (held.symm.trans exactBinding)
          have certified : authority.mayRelease key prior := permitted
          exact .inr (identical.symm ▸ certified)
      · rw [(release_clears_only_the_exact_key before released).2 key same]
        exact .inl held

theorem retirement_discards_the_control_row {store : Store} {handle : Handle}
    (sameHandle : activeHandle store handle.route = some handle) :
    (closeChannel store handle).channels handle.route = none ∧
      (closeChannel store handle).issued = store.issued := by
  simp [closeChannel, sameHandle, setSlot]

private theorem close_keeps_issued (store : Store) (handle : Handle) :
    (closeChannel store handle).issued = store.issued := by
  by_cases sameHandle : activeHandle store handle.route = some handle <;> simp [closeChannel, sameHandle]

def Retired (store : Store) (handle : Handle) : Prop :=
  handle.nonce ≤ store.issued ∧ activeHandle store handle.route ≠ some handle

theorem retired_handles_stay_retired_at_every_step {authority : Authority} {before after : Store}
    (effect : Step authority before after) {handle : Handle} (old : Retired before handle) :
    Retired after handle := by
  cases effect with
  | mint route issuer _ _ _ =>
      refine ⟨Nat.le_trans old.1 (Nat.le_succ _), ?_⟩
      by_cases same : handle.route = route
      · intro active
        have alias : freshHandle before authority.custodian route issuer = handle :=
          Option.some.inj (by simpa [activeHandle, openChannel, setSlot, same] using active)
        have advances : before.issued + 1 = handle.nonce := congrArg Handle.nonce alias
        have prior : handle.nonce ≤ before.issued := old.1
        omega
      · simpa [activeHandle, openChannel, setSlot, same] using old.2
  | close closing _ =>
      exact ⟨(close_keeps_issued before closing) ▸ old.1, fun active => old.2 (close_only_removes_a_handle active)⟩
  | credit receipt _ =>
      exact ⟨by simpa [receiveFloor, modify_control_keeps_issued] using old.1,
        by simpa [receiveFloor, modify_control_keeps_handle] using old.2⟩
  | acquire _ _ _ _ _ => exact old
  | release key _ _ _ =>
      exact ⟨by simpa [releaseGrant, modify_control_keeps_issued, setGrant] using old.1,
        by simpa only [release_keeps_active_handle] using old.2⟩

theorem retired_handles_stay_retired_across_renewals {authority : Authority} {first last : Store}
    (history : Trace authority first last) {handle : Handle} (retired : Retired first handle) :
    Retired last handle := by
  induction history with
  | same => exact retired
  | next _ effect prior => exact retired_handles_stay_retired_at_every_step effect prior

theorem retired_missing_grant_cannot_be_created {authority : Authority} {before after : Store}
    (effect : Step authority before after) {key : Key} (retired : Retired before key.handle)
    (missing : before.grants key = none) : after.grants key = none := by
  cases effect with
  | mint _ _ _ _ _ => exact missing
  | close closing _ =>
      rw [channel_close_preserves_all_pins]
      exact missing
  | credit _ _ =>
      simpa [receiveFloor, modify_control_keeps_grants] using missing
  | acquire admitted _ _ _ accepted =>
      have other : key ≠ admitted := by
        intro alias
        subst admitted
        exact retired.2 (fresh_admission_requires_an_empty_matching_channel accepted).2
      simpa [setGrant, other] using missing
  | release closing _ _ _ =>
      by_cases same : key = closing
      · subst closing
        exact (release_clears_only_the_exact_key before key).1
      · rw [(release_clears_only_the_exact_key before closing).2 key same]
        exact missing

theorem old_delayed_acquire_stays_refused_after_reclaim {authority : Authority} {first last : Store}
    (history : Trace authority first last) {key : Key} (retired : Retired first key.handle)
    (missing : first.grants key = none) (binding : Binding) :
    last.grants key = none ∧ decideAcquire last key binding = .refuse := by
  have forever : Retired last key.handle ∧ last.grants key = none := by
    induction history with
    | same => exact ⟨retired, missing⟩
    | next _ effect prior =>
        exact ⟨retired_handles_stay_retired_at_every_step effect prior.1,
          retired_missing_grant_cannot_be_created effect prior.1 prior.2⟩
  exact ⟨forever.2, absent_grant_with_stale_handle_is_refused forever.2 forever.1.2 binding⟩

def BoundedRoutes (authority : Authority) (store : Store) : Prop :=
  ∀ route handle, activeHandle store route = some handle → route < authority.routeLimit

theorem arbitrary_lifetime_uses_only_bounded_control_slots {authority : Authority}
    {first last : Store} (initial : BoundedRoutes authority first) (history : Trace authority first last) :
    BoundedRoutes authority last := by
  induction history with
  | same => exact initial
  | next _ effect prior =>
      intro route handle active
      cases effect with
      | mint opened _ _ room _ =>
          have inside : opened < authority.routeLimit := room
          by_cases same : route = opened
          · exact same.symm ▸ inside
          · exact prior route handle (by simpa [openChannel, activeHandle, setSlot, same] using active)
      | close _ _ => exact prior route handle (close_only_removes_a_handle active)
      | credit _ _ =>
          exact prior route handle (by simpa [receiveFloor, modify_control_keeps_handle] using active)
      | acquire _ _ _ _ _ => exact prior route handle active
      | release _ _ _ _ =>
          exact prior route handle (by simpa only [release_keeps_active_handle] using active)

theorem active_handle_never_exceeds_durable_issuance {authority : Authority} {first last : Store}
    (initial : ∀ route handle, activeHandle first route = some handle → handle.nonce ≤ first.issued)
    (history : Trace authority first last) :
    ∀ route handle, activeHandle last route = some handle → handle.nonce ≤ last.issued := by
  induction history with
  | same => exact initial
  | next _ effect prior =>
      intro route handle active
      cases effect with
      | mint opened issuer _ _ _ =>
          by_cases same : route = opened
          · have alias : freshHandle _ authority.custodian opened issuer = handle :=
              Option.some.inj (by simpa [openChannel, activeHandle, setSlot, same] using active)
            exact (congrArg Handle.nonce alias) ▸ Nat.le_refl _
          · have previous := prior route handle (by simpa [openChannel, activeHandle, setSlot, same] using active)
            exact Nat.le_trans previous (Nat.le_succ _)
      | close closing _ =>
          rw [close_keeps_issued]
          exact prior route handle (close_only_removes_a_handle active)
      | credit _ _ =>
          simpa [receiveFloor, modify_control_keeps_issued] using
            prior route handle (by simpa [receiveFloor, modify_control_keeps_handle] using active)
      | acquire _ _ _ _ _ => exact prior route handle active
      | release _ _ _ _ =>
          simpa [releaseGrant, modify_control_keeps_issued, setGrant] using
            prior route handle (by simpa only [release_keeps_active_handle] using active)

theorem rotates_with_live_grant_and_settles_it_afterward {authority : Authority} {store : Store}
    {key : Key} {binding : Binding} (current : activeHandle store key.handle.route = some key.handle)
    (issued : key.handle.nonce ≤ store.issued) (held : store.grants key = some binding)
    (room : key.handle.route < authority.routeLimit)
    (closeAuthorized : authority.mayClose key.handle)
    (openAuthorized : authority.mayOpen key.handle.route key.handle.issuer)
    (releaseAuthorized : authority.mayRelease key binding) :
    ∃ reopened settled successor, Trace authority store reopened ∧ Step authority reopened settled ∧
      activeHandle reopened key.handle.route = some successor ∧ successor.nonce > key.handle.nonce ∧
      decideAcquire reopened key binding = .replay ∧
      activeHandle settled key.handle.route = some successor ∧ settled.grants key = none := by
  let route := key.handle.route
  let detached := closeChannel store key.handle
  let successor := freshHandle detached authority.custodian route key.handle.issuer
  let reopened := openChannel detached authority.custodian route key.handle.issuer
  obtain ⟨free, counter⟩ := retirement_discards_the_control_row current
  have opens : Step authority detached reopened := .mint route key.handle.issuer free room openAuthorized
  have pin : reopened.grants key = some binding :=
    (channel_close_preserves_all_pins store key.handle).symm ▸ held
  have higher : successor.nonce > key.handle.nonce := by
    change key.handle.nonce < detached.issued + 1
    exact Nat.lt_succ_of_le (counter.symm ▸ issued)
  have liveSlot : activeHandle reopened route = some successor := by
    simp [reopened, openChannel, activeHandle, setSlot, successor]
  refine ⟨reopened, releaseGrant reopened key, successor, .next (.next (.same _) (.close key.handle closeAuthorized)) opens,
    .release key binding (.inr pin) releaseAuthorized, liveSlot, higher,
    (existing_grant_retries_without_channel_metadata (other := binding) pin).1, ?_,
    (release_clears_only_the_exact_key reopened key).1⟩
  simpa only [release_keeps_active_handle] using liveSlot

#print axioms stale_close_changes_nothing
#print axioms stale_credit_changes_nothing
#print axioms active_requests_use_the_registration_gate
#print axioms existing_grant_retries_without_channel_metadata
#print axioms channel_close_preserves_all_pins
#print axioms release_clears_only_the_exact_key
#print axioms grant_survives_each_step_or_has_exact_release_authority
#print axioms retirement_discards_the_control_row
#print axioms retired_handles_stay_retired_at_every_step
#print axioms retired_handles_stay_retired_across_renewals
#print axioms retired_missing_grant_cannot_be_created
#print axioms old_delayed_acquire_stays_refused_after_reclaim
#print axioms arbitrary_lifetime_uses_only_bounded_control_slots
#print axioms active_handle_never_exceeds_durable_issuance
#print axioms rotates_with_live_grant_and_settles_it_afterward

end ChannelLifecycle
