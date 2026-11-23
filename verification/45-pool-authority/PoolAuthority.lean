import JournalRefinement
import ChannelLifecycle
import CustodianRecovery

set_option warningAsError true

namespace PoolAuthority

open RegistrationRecovery (Binding)
open ChannelLifecycle (Key Store)

structure Image where
  pool : Nat
  book : Store
  debitKeys : List Key
  ordinary : Nat
  limit : Nat

def liveBytes (book : Store) (cost : Binding → Nat) (keys : List Key) : Nat :=
  (keys.map fun key => ((book.grants key).map cost).getD 0).sum

def used (cost : Binding → Nat) (image : Image) : Nat :=
  image.ordinary + liveBytes image.book cost image.debitKeys

def OrdinaryFits (cost : Binding → Nat) (image : Image) (bytes : Nat) : Prop :=
  used cost image + bytes ≤ image.limit

def ResizeFits (cost : Binding → Nat) (image : Image) (newLimit : Nat) : Prop :=
  used cost image ≤ newLimit

structure ServingPool where
  owner : Nat
  image : Image

def MayPrepare (cost : Binding → Nat) (localPool : ServingPool) (recipient : Nat)
    (key : Key) (binding : Binding) : Prop :=
  recipient = localPool.owner ∧ key.handle.custodian = localPool.image.pool ∧
  ChannelLifecycle.decideAcquire localPool.image.book key binding = .admit ∧
  OrdinaryFits cost localPool.image (cost binding)

theorem old_owner_cannot_prepare {cost : Binding → Nat} {localPool : ServingPool}
    {recipient : Nat} {key : Key} {binding : Binding}
    (admitted : MayPrepare cost localPool recipient key binding) : recipient = localPool.owner := by
  exact admitted.1

def Latest (journal : JournalRefinement.Journal Replica Image) (image : Image) : Prop :=
  ∃ lsn entry, lsn + 1 = journal.logical.history.length ∧ journal.logical.firstRetained ≤ lsn ∧
    journal.logical.history[lsn]? = some entry ∧ entry.bytes = image

theorem chosen_cut_determines_the_entire_pool_book
    {journal : JournalRefinement.Journal Replica Image} {before after : Image}
    (committed : Latest journal before) (recovered : Latest journal after) : after = before := by
  obtain ⟨oldLsn, oldEntry, oldHead, _, oldValue, oldImage⟩ := committed
  obtain ⟨newLsn, newEntry, newHead, _, newValue, newImage⟩ := recovered
  have sameLsn : oldLsn = newLsn := by omega
  subst newLsn
  have sameEntry := Option.some.inj (newValue.symm.trans oldValue)
  exact newImage.symm.trans ((congrArg Kernel.Entry.bytes sameEntry).trans oldImage)

theorem recovery_majority_reads_the_exact_pool_obligations
    {journal : JournalRefinement.Journal Replica Image} {image : Image}
    (latest : Latest journal image) (covered : JournalRefinement.CompleteCut journal)
    (available : Replica → Bool) (quorum : JournalRefinement.Majority journal.members available) :
    ∃ replica ∈ journal.members, available replica = true ∧
      ∃ lsn entry, lsn + 1 = journal.logical.history.length ∧
        journal.copies replica lsn entry ∧ entry.bytes = image := by
  obtain ⟨lsn, entry, atHead, retained, reported, exactImage⟩ := latest
  obtain ⟨replica, member, up, copy⟩ :=
    JournalRefinement.any_recovery_quorum_can_read_exact_entry covered available quorum retained reported
  exact ⟨replica, member, up, lsn, entry, atHead, copy, exactImage⟩

theorem installed_pool_preserves_live_and_closed_keys_and_admission
    {journal : JournalRefinement.Journal Replica Image} {before after : Image}
    {key : Key} {binding : Binding} (cost : Binding → Nat)
    (committed : Latest journal before) (recovered : Latest journal after) :
    before.book.grants key = after.book.grants key ∧
    ChannelLifecycle.decideAcquire before.book key binding =
      ChannelLifecycle.decideAcquire after.book key binding ∧
    ∀ bytes, OrdinaryFits cost before bytes ↔ OrdinaryFits cost after bytes := by
  rw [chosen_cut_determines_the_entire_pool_book committed recovered]
  exact ⟨rfl, rfl, fun _ => Iff.rfl⟩

theorem installing_floor_preserves_each_debit (book : Store) (receipt : ChannelLifecycle.FloorReceipt) :
    (ChannelLifecycle.receiveFloor book receipt).grants = book.grants := by
  cases found : book.channels receipt.handle.route with
  | none => simp [ChannelLifecycle.receiveFloor, ChannelLifecycle.modifyControl, found]
  | some channel =>
      by_cases same : channel.handle = receipt.handle <;>
        simp [ChannelLifecycle.receiveFloor, ChannelLifecycle.modifyControl, found, same]

theorem installing_floor_preserves_numeric_occupancy
    (cost : Binding → Nat) (image : Image) (receipt : ChannelLifecycle.FloorReceipt) :
    used cost {image with book := ChannelLifecycle.receiveFloor image.book receipt} = used cost image := by
  unfold used liveBytes
  simp only [installing_floor_preserves_each_debit]

theorem release_never_adds_capacity_charges
    (cost : Binding → Nat) (book : Store) (key : Key) (keys : List Key) :
    liveBytes (ChannelLifecycle.releaseGrant book key) cost keys ≤ liveBytes book cost keys := by
  induction keys with
  | nil => simp [liveBytes]
  | cons candidate rest prior =>
      have exactRelease := ChannelLifecycle.release_clears_only_the_exact_key book key
      by_cases same : candidate = key
      · subst candidate
        simp only [liveBytes, List.map_cons, List.sum_cons, exactRelease.1, Option.map_none,
          Option.getD_none, Nat.zero_add] at *
        omega
      · simpa only [liveBytes, List.map_cons, List.sum_cons, exactRelease.2 candidate same] using
          Nat.add_le_add_left prior ((book.grants candidate).map cost |>.getD 0)

theorem cancellation_of_an_empty_pool_key_prevents_a_delayed_hold_after_recovery
    {journal : JournalRefinement.Journal Replica Image} {before after : Image}
    {authority : ChannelLifecycle.Authority} {key : Key} {binding : Binding}
    {channel : ChannelLifecycle.Channel}
    (active : before.book.channels key.handle.route = some channel)
    (same : channel.handle = key.handle) (absent : before.book.grants key = none)
    (canceled : authority.mayRelease key binding)
    (committed : Latest journal {before with book := ChannelLifecycle.releaseGrant before.book key})
    (recovered : Latest journal after) :
    after.book.grants key = none ∧ ChannelLifecycle.decideAcquire after.book key binding = .refuse := by
  rw [chosen_cut_determines_the_entire_pool_book committed recovered]
  exact (CustodianRecovery.active_key_can_be_fenced_before_its_acquisition_arrives
    active same absent canceled).2

theorem cancellation_row_has_one_slot_in_the_installed_window
    {issued acknowledged floor width : Nat} (acknowledgedInstalled : acknowledged ≤ floor)
    (remaining : issued + 1 - acknowledged ≤ width) :
    ∃ slot : {serial : Nat // floor < serial ∧ serial ≤ issued + 1} → Fin width,
      ∀ a b, slot a = slot b → a = b := by
  have bounded := RegistrationRecovery.credit_from_acknowledged_floor_bounds_receiver_debt acknowledgedInstalled remaining
  let slot (row : {serial : Nat // floor < serial ∧ serial ≤ issued + 1}) :=
    RegistrationRecovery.markerIndex row.val floor (issued + 1) width row.property.1 row.property.2 bounded
  refine ⟨slot, ?_⟩
  intro a b same
  apply Subtype.ext
  exact RegistrationRecovery.markers_above_floor_fit_in_credit_window
    bounded a.val b.val a.property.1 b.property.1 a.property.2 b.property.2 same

theorem reduction_cannot_consume_reserved_capacity (cost : Binding → Nat) (image : Image)
    (limit : Nat) (admitted : ResizeFits cost image limit) :
    OrdinaryFits cost {image with limit := limit} 0 := by
  simpa [OrdinaryFits, used, ResizeFits] using admitted

#print axioms old_owner_cannot_prepare
#print axioms chosen_cut_determines_the_entire_pool_book
#print axioms recovery_majority_reads_the_exact_pool_obligations
#print axioms installed_pool_preserves_live_and_closed_keys_and_admission
#print axioms installing_floor_preserves_each_debit
#print axioms installing_floor_preserves_numeric_occupancy
#print axioms release_never_adds_capacity_charges
#print axioms cancellation_of_an_empty_pool_key_prevents_a_delayed_hold_after_recovery
#print axioms cancellation_row_has_one_slot_in_the_installed_window
#print axioms reduction_cannot_consume_reserved_capacity

end PoolAuthority
