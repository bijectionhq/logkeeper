import Logkeeper.StreamRead

namespace Logkeeper.StreamRecovery

open PrefixAgreement StreamJournal StreamIO StreamHead StreamRpc StreamRead StreamWriter

set_option autoImplicit false
set_option warningAsError true

variable {Payload : Type}

/-- The compressed run stores the epoch of each position in its inclusive range.
    Model offsets are zero-based, while the wire's first and last are LSNs. -/
structure Run where
  epoch : Nat
  first : Nat
  last : Nat

def Run.covers (run : Run) (lsn : Nat) : Prop := run.first ≤ lsn ∧ lsn ≤ run.last

/-- Appending, truncating or discarding a run must leave these facts about the
    retained image. Adjacent runs may be compressed without changing lookup. -/
def Describes (runs : List Run) (history : History Payload) (floor : Nat) : Prop :=
  (∀ run ∈ runs, ∀ lsn, run.covers lsn →
    floor ≤ lsn ∧ ∃ record, history[lsn - 1]? = some record ∧ record.epoch = run.epoch) ∧
  ∀ lsn, floor ≤ lsn → lsn ≤ history.length → ∃ run ∈ runs, run.covers lsn

theorem covering_run_epoch {runs : List Run} {history : History Payload} {floor lsn : Nat}
    (described : Describes runs history floor)
    {run : Run} (member : run ∈ runs) (covers : run.covers lsn)
    {record : Record Payload} (atLsn : history[lsn - 1]? = some record) :
    run.epoch = record.epoch := by
  obtain ⟨_, other, exactRecord, epoch⟩ := described.1 run member lsn covers
  rw [atLsn] at exactRecord
  exact (Option.some.inj exactRecord ▸ epoch).symm

/-- The partition point used by epoch_at selects the last run whose first LSN
    is at most the requested LSN. A covering run's last bound makes that lookup
    exact when run starts are ordered and successive runs do not overlap. -/
theorem last_run_covers {earlier chosen : Run} {lsn : Nat}
    (covers : earlier.covers lsn) (candidate : chosen.first ≤ lsn)
    (noOverlap : earlier = chosen ∨ earlier.last < chosen.first) :
    chosen.covers lsn := by
  rcases noOverlap with same | gap
  · exact same ▸ covers
  · exact False.elim (Nat.not_lt_of_ge covers.2 (Nat.lt_of_lt_of_le gap candidate))

def Run.clip (first last : Nat) (run : Run) : Option Run :=
  let start := max first run.first
  let stop := min last run.last
  if start ≤ stop then some ⟨run.epoch, start, stop⟩ else none

theorem clipped_run_exact {first last lsn : Nat} {run clipped : Run}
    (built : run.clip first last = some clipped) :
    clipped.epoch = run.epoch ∧ (clipped.covers lsn ↔ run.covers lsn ∧ first ≤ lsn ∧ lsn ≤ last) := by
  dsimp only [Run.clip] at built
  split at built
  · cases built
    simp only [true_and, Run.covers, Nat.max_le, Nat.le_min]
    grind
  · cases built

theorem discarded_runs_exact {runs : List Run} {history : History Payload} {oldFloor floor tail : Nat}
    (described : Describes runs history oldFloor) (above : oldFloor ≤ floor) (positive : 0 < floor) :
    Describes (runs.filterMap (Run.clip floor tail)) (history.take tail) floor := by
  constructor
  · intro clipped member lsn covers
    obtain ⟨run, oldMember, built⟩ := List.mem_filterMap.mp member
    obtain ⟨epoch, exactRange⟩ := clipped_run_exact (lsn := lsn) built
    obtain ⟨prior, floorBound, tailBound⟩ := exactRange.mp covers
    obtain ⟨_, record, exactRecord, stamped⟩ := described.1 run oldMember lsn prior
    exact ⟨floorBound, record, by simpa [List.getElem?_take, show lsn - 1 < tail by omega] using exactRecord,
      stamped.trans epoch.symm⟩
  · intro lsn retained existsAt
    simp only [List.length_take, Nat.le_min] at existsAt
    obtain ⟨run, member, covers⟩ := described.2 lsn (Nat.le_trans above retained) existsAt.2
    have intersects : max floor run.first ≤ min tail run.last := by
      exact Nat.le_trans (Nat.max_le.mpr ⟨retained, covers.1⟩) (Nat.le_min.mpr ⟨existsAt.1, covers.2⟩)
    let clipped : Run := ⟨run.epoch, max floor run.first, min tail run.last⟩
    have built : run.clip floor tail = some clipped := by simp [Run.clip, intersects, clipped]
    exact ⟨clipped, List.mem_filterMap.mpr ⟨run, member, built⟩,
      (clipped_run_exact built).2.mpr ⟨covers, retained, existsAt.1⟩⟩

theorem local_promise_grows (trace : Timeline Payload) {first last : Nat}
    (ordered : first ≤ last) (keeper : KeeperId) :
    ((trace.state first).keeper keeper).promised ≤ ((trace.state last).keeper keeper).promised := by
  induction ordered with
  | refl => exact Nat.le_refl _
  | @step time _ prior =>
      obtain ⟨_, next⟩ := trace.next time
      obtain ⟨_, keeps, _⟩ := next_inv (reachable_inv (trace.reachable time)) next
      rcases keeps keeper |>.2 with step | unchanged
      · exact Nat.le_trans prior (promised_mono (keeps keeper).1 step)
      · rwa [unchanged]

/-- A keeper that still promises an epoch but has yet to complete Sync at that
    epoch reports the same vote as at its Seal. Staging may change in between. -/
theorem unsynced_history_stable (trace : Timeline Payload) {first last epoch : Nat}
    (ordered : first ≤ last) (keeper : KeeperId)
    (sealed : ((trace.state first).keeper keeper).promised = epoch)
    (promised : ((trace.state last).keeper keeper).promised = epoch)
    (unsynced : ((trace.state last).keeper keeper).synced ≠ epoch) :
    ((trace.state last).keeper keeper).latest = ((trace.state first).keeper keeper).latest := by
  induction ordered with
  | refl => rfl
  | @step time before prior =>
      obtain ⟨_, next⟩ := trace.next time
      rcases (every_action_refines (trace.reachable time) next).2 keeper with step | unchanged
      · have notFenced := local_promise_grows trace before keeper
        rw [sealed] at notFenced
        obtain ⟨still, exactVote, _⟩ := quiet_step step notFenced promised unsynced
        refine exactVote.trans (prior still ?_)
        intro synced
        exact unsynced ((congrArg Vote.ballot exactVote).trans synced)
      · simp only [unchanged] at promised unsynced ⊢
        exact prior promised unsynced

/-- A successful Recover sees the visible image. If the keeper completed Sync
    since the earlier Seal, its new image contains the elected seed. Otherwise
    the earlier matching epoch still identifies the returned record. -/
theorem recover_after_seal {trace : Timeline Payload} {first last epoch index : Nat}
    (order : first ≤ last) (keeper : KeeperId)
    (sealed : ((trace.state first).keeper keeper).promised = epoch)
    (admitted : ((trace.state last).keeper keeper).promised = epoch)
    {old wanted : Record Payload}
    (earlier : ((trace.state first).keeper keeper).history[index]? = some old)
    (seedAt : ((trace.state last).writer.seed epoch)[index]? = some wanted)
    (matched : old.epoch = wanted.epoch) :
    ((trace.state last).keeper keeper).history[index]? = some wanted := by
  by_cases synced : ((trace.state last).keeper keeper).synced = epoch
  · let inv := reachable_inv (trace.reachable last)
    have cutHistory := (synced_history (inv.reached keeper) inv.reserved (inv.unelected 0 inv.reserved) synced).1
    obtain ⟨_, extendsSeed⟩ := cutHistory
    rw [← extendsSeed, List.getElem?_append_left (List.getElem?_eq_some_iff.mp seedAt |>.1)]
    exact seedAt
  · have same := unsynced_history_stable trace order keeper sealed admitted synced
    have sameHistory : ((trace.state last).keeper keeper).history =
        ((trace.state first).keeper keeper).history := congrArg Vote.history same
    rw [sameHistory, earlier]
    congr 1
    exact recovery_record ((keeper_origins (trace.reachable first) keeper).grows (writer_grows trace order))
      (seed_origins (trace.reachable last) epoch) earlier seedAt (congrArg some matched)

/-- Transport associates each Recover response with the position, epoch and
    caller of its own observation. The keeper reads only its visible image. -/
structure RecoverReply (trace : Timeline Payload) (keeper : KeeperId) (epoch : Nat) where
  caller : Nat
  rpc : Exchange trace keeper caller (.observe : Request Payload)
  start : Nat
  count : Nat
  promised : ((trace.state rpc.sample).keeper keeper).promised = epoch
  owner : ((trace.state rpc.sample).keeper keeper).identity = caller
  retained : ((trace.state rpc.sample).keeper keeper).floor ≤ start

def RecoverReply.records {trace : Timeline Payload} {keeper : KeeperId} {epoch : Nat}
    (response : RecoverReply trace keeper epoch) : History Payload :=
  (((trace.state response.rpc.sample).keeper keeper).history.drop (response.start - 1)).take response.count

theorem recover_reply_exact {trace : Timeline Payload} {keeper : KeeperId} {epoch first : Nat}
    (response : RecoverReply trace keeper epoch)
    (order : first ≤ response.rpc.sample)
    (sealed : ((trace.state first).keeper keeper).promised = epoch)
    (single : response.count = 1) {old wanted : Record Payload}
    (earlier : ((trace.state first).keeper keeper).history[response.start - 1]? = some old)
    (seedAt : ((trace.state response.rpc.sample).writer.seed epoch)[response.start - 1]? = some wanted)
    (matched : old.epoch = wanted.epoch) : response.records = [wanted] := by
  have exactRecord := recover_after_seal order keeper sealed response.promised earlier seedAt matched
  apply List.ext_getElem?
  intro i
  cases i with
  | zero => simpa [RecoverReply.records, single, List.getElem?_take, List.getElem?_drop] using exactRecord
  | succ i => simp [RecoverReply.records, single, List.getElem?_take]

/-- A retained reply from a synced keeper carries the selected exact slice of
    the epoch's issued history. The bound comes from the captured source slot. -/
theorem recover_issued_slice {state : State Payload} (reached : StreamIO.Reachable state)
    (keeper : KeeperId) {epoch start count : Nat}
    (synced : (state.keeper keeper).synced = epoch)
    (bounds : start + count ≤ (state.keeper keeper).tail) :
    ((state.keeper keeper).history.drop start).take count =
      ((state.writer.issued epoch).drop start).take count := by
  let inv := reachable_inv reached
  have prefixed := (synced_history (inv.reached keeper) inv.reserved (inv.unelected 0 inv.reserved) synced).2
  rw [List.take_drop, List.take_drop, take_of_prefix prefixed bounds]

/-- A lagging lane fetches from a keeper already known to have accepted at
    this epoch. A later successful Recover still samples a keeper synced at
    that epoch and supplies exact assigned bytes. -/
theorem recover_committed_reply {trace : Timeline Payload} {keeper : KeeperId} {epoch accepted : Nat}
    (response : RecoverReply trace keeper epoch)
    (ordered : accepted ≤ response.rpc.sample)
    (voted : Synced ((trace.state accepted).keeper keeper) epoch)
    (bounded : response.start - 1 + response.count ≤ ((trace.state response.rpc.sample).keeper keeper).tail) :
    response.records = (((trace.state response.rpc.sample).writer.issued epoch).drop
      (response.start - 1)).take response.count := by
  have synced : ((trace.state response.rpc.sample).keeper keeper).synced = epoch := by
    by_cases installed : ((trace.state response.rpc.sample).keeper keeper).synced = epoch
    · exact installed
    · have same := unsynced_history_stable trace ordered keeper voted.1 response.promised installed
      exact (congrArg Vote.ballot same).trans voted.2
  exact recover_issued_slice (trace.reachable response.rpc.sample) keeper synced bounded

/-- Each entry copied from the pending or committed map matches its assigned
    position. The consecutive scan then yields the exact combined byte slice. -/
theorem lane_scan_exact (issued run : History Payload) (offset : Nat)
    (slot : ∀ i, i < run.length → run[i]? = issued[offset + i]?) :
    run = (issued.drop offset).take run.length := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split
  · rw [List.getElem?_drop]
    exact slot i ‹_›
  · have outside : run.length ≤ i := by omega
    exact List.getElem?_eq_none outside

/-- The same exact accepted slots that choose a cut justify advertising any
    earlier cut. This includes inherited records before an epoch's first append. -/
theorem certify_lane_cut {state : State Payload} {epoch cut : Nat} {a b : KeeperId}
    {left right : History Payload}
    (distinct : a ≠ b)
    (leftSlot : state.votes epoch a = some left) (rightSlot : state.votes epoch b = some right)
    (leftBytes : left <+: state.writer.issued epoch) (rightBytes : right <+: state.writer.issued epoch)
    (covered : cut ≤ left.length ∧ cut ≤ right.length) :
    let cutHistory := (state.writer.issued epoch).take cut
    let after := { state with writer := advertise state.writer cutHistory }
    Next state (.certify epoch cutHistory) after ∧ after.writer.advertised cutHistory := by
  intro cutHistory after
  have leftPrefix : cutHistory <+: left := by
    change (state.writer.issued epoch).take cut <+: left
    rw [← take_of_prefix leftBytes covered.1]
    exact List.take_prefix _ _
  have rightPrefix : cutHistory <+: right := by
    change (state.writer.issued epoch).take cut <+: right
    rw [← take_of_prefix rightBytes covered.2]
    exact List.take_prefix _ _
  exact ⟨Next.certify a b distinct leftSlot rightSlot leftPrefix rightPrefix, Or.inr rfl⟩

/-- Local dispatch evidence for the writer's request constructors. These
    constructors use seed offsets, contiguous lane slots and certified cuts. -/
inductive Dispatch (w : Writer Payload) (k : Keeper Payload) (caller : Nat) :
    Request Payload → Prop
  | create : Dispatch w k caller .create
  | observe : Dispatch w k caller .observe
  | delete : Dispatch w k caller .delete
  | promise (wireEpoch : Nat) : Dispatch w k caller (.promise (wireEpoch + 1))
  | stage {epoch floor start : Nat} {record : Record Payload} :
      Elected w epoch caller → epoch ≤ k.promised →
      Agrees k epoch (w.seed epoch) floor start →
      (w.seed epoch)[start - 1]? = some record →
      Dispatch w k caller (.stage epoch floor start [record])
  | complete {epoch floor head : Nat} :
      Elected w epoch caller → epoch ≤ k.promised →
      Agrees k epoch (w.seed epoch) floor ((w.seed epoch).length + 1) →
      head ≤ (w.seed epoch).length → w.advertised ((w.seed epoch).take head) →
      Dispatch w k caller (.sync epoch floor ((w.seed epoch).length + 1) [] head)
  | installFloor {epoch head : Nat} :
      Elected w epoch caller → head ≤ (w.issued epoch).length →
      w.advertised ((w.issued epoch).take head) →
      Dispatch w k caller (.installFloor epoch head)
  | append {epoch start head : Nat} {payloads : List Payload} :
      Elected w epoch caller → start - 1 + payloads.length ≤ (w.issued epoch).length →
      (∀ i, i < payloads.length →
        (stamp epoch payloads)[i]? = (w.issued epoch)[start - 1 + i]?) →
      w.advertised ((w.issued epoch).take (AppendHead head (start - 1 + payloads.length))) →
      Dispatch w k caller (.append epoch start payloads (AppendHead head (start - 1 + payloads.length)))
  | publish {epoch head : Nat} :
      Elected w epoch caller → head ≤ (w.issued epoch).length →
      w.advertised ((w.issued epoch).take head) →
      Dispatch w k caller (.publish epoch head)
  | trim {epoch through : Nat} :
      Elected w epoch caller → Dispatch w k caller (.trim epoch through)

theorem dispatch_sendable {w : Writer Payload} {k : Keeper Payload} {caller : Nat}
    {request : Request Payload} (dispatch : Dispatch w k caller request) :
    Sendable w k caller request := by
  cases dispatch with
  | create | observe | delete => trivial
  | promise => exact Nat.zero_lt_succ _
  | @stage epoch floor start record elected promised agrees seedAt =>
      apply sendable_stage elected promised agrees
      have current : ((w.seed epoch).drop (start - 1))[0]? = some record := by
        simp only [List.getElem?_drop, Nat.add_zero]
        exact seedAt
      cases list : (w.seed epoch).drop (start - 1) with
      | nil => simp [list] at current
      | cons first rest =>
          rw [list, List.getElem?_cons_zero] at current
          cases current
          exact ⟨rest, rfl⟩
  | complete elected promised agrees bounded certified =>
      refine ⟨elected, promised, ?_, agrees, bounded, certified⟩
      simp
  | installFloor elected bounded certified | publish elected bounded certified =>
      exact ⟨elected, bounded, certified⟩
  | append elected bounded slots certified =>
      apply sendable_append elected bounded _ certified
      simpa [stamp] using lane_scan_exact (slot := fun i bound => slots i (by simpa [stamp] using bound))
  | trim elected => exact elected

/-- Reassigning a sent position to different bytes cannot refine two ordinary
    sends in the monotone issued-history model, even if all earlier replies refused. -/
theorem issued_position_cannot_be_reassigned {before after : Writer Payload}
    (growth : Grows before after) {source target : Keeper Payload} {caller epoch position : Nat}
    {old new : Payload}
    (first : Sendable before source caller (.append epoch position [old] 0))
    (second : Sendable after target caller (.append epoch position [new] 0)) : old = new := by
  have oldAt : (before.issued epoch)[position - 1]? = some ⟨epoch, old⟩ := by
    have exactSlice := congrArg (fun (h : History Payload) => h[0]?) first.2.2.1
    simpa [stamp, List.getElem?_take, List.getElem?_drop] using exactSlice.symm
  have newAt : (after.issued epoch)[position - 1]? = some ⟨epoch, new⟩ := by
    have exactSlice := congrArg (fun (h : History Payload) => h[0]?) second.2.2.1
    simpa [stamp, List.getElem?_take, List.getElem?_drop] using exactSlice.symm
  obtain ⟨_, issuedExtension⟩ := growth.issued epoch
  rw [← issuedExtension, List.getElem?_append_left (List.getElem?_eq_some_iff.mp oldAt).1, oldAt] at newAt
  exact congrArg Record.payload (Option.some.inj newAt)

#print axioms dispatch_sendable
#print axioms covering_run_epoch
#print axioms discarded_runs_exact
#print axioms recover_after_seal
#print axioms recover_reply_exact
#print axioms recover_issued_slice
#print axioms recover_committed_reply
#print axioms lane_scan_exact
#print axioms certify_lane_cut
#print axioms issued_position_cannot_be_reassigned

end Logkeeper.StreamRecovery
