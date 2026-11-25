import Logkeeper.LeaderJournal.Recovery

namespace Logkeeper.LeaderJournal.PeerBudget

set_option warningAsError true

inductive ControlWork where
  | vote
  | confirmRead
  | heartbeat
  | durableProtocol
  deriving DecidableEq

inductive Lane where
  | control (work : ControlWork)
  | maintenance
  | replication
  | application
  | bulk
  deriving DecidableEq

structure Counts where
  control : Nat
  maintenance : Nat
  replication : Nat
  application : Nat
  bulk : Nat
  deriving DecidableEq

def Counts.get (counts : Counts) : Lane → Nat
  | .control _ => counts.control
  | .maintenance => counts.maintenance
  | .replication => counts.replication
  | .application => counts.application
  | .bulk => counts.bulk

def Counts.change (counts : Counts) (f : Nat → Nat) : Lane → Counts
  | .control _ => { counts with control := f counts.control }
  | .maintenance => { counts with maintenance := f counts.maintenance }
  | .replication => { counts with replication := f counts.replication }
  | .application => { counts with application := f counts.application }
  | .bulk => { counts with bulk := f counts.bulk }

structure Limits where
  capacity : Counts
  reserved : 0 < capacity.control
  maintenanceReserved : 0 < capacity.maintenance

def Valid (limits : Limits) (counts : Counts) : Prop :=
  counts.control ≤ limits.capacity.control ∧ counts.maintenance ≤ limits.capacity.maintenance ∧
    counts.replication ≤ limits.capacity.replication ∧
    counts.application ≤ limits.capacity.application ∧ counts.bulk ≤ limits.capacity.bulk

/-- A control token lasts through its required durable work. The scheduler
    returns it on completion, cancellation or delivery failure. -/
inductive Step (limits : Limits) : Counts → Counts → Prop
  | admit {counts} (lane : Lane) (space : counts.get lane < limits.capacity.get lane) :
    Step limits counts (counts.change (· + 1) lane)
  | release {counts} (lane : Lane) (present : 0 < counts.get lane) :
    Step limits counts (counts.change (· - 1) lane)

theorem step_preserves_budget {limits : Limits} {before after : Counts}
    (valid : Valid limits before) (step : Step limits before after) : Valid limits after := by
  cases step with
  | admit lane space =>
    cases lane <;> (simp only [Valid, Counts.get, Counts.change] at valid space ⊢; omega)
  | release lane present =>
    cases lane <;> (simp only [Valid, Counts.get, Counts.change] at valid present ⊢; omega)

theorem admit_control_with_other_lanes_full (limits : Limits) (counts : Counts)
    (work : ControlWork) (space : counts.control < limits.capacity.control) :
    ∃ admitted, Step limits counts admitted ∧ admitted.control = counts.control + 1 ∧
      admitted.application = counts.application ∧ admitted.bulk = counts.bulk :=
  ⟨counts.change (· + 1) (.control work), .admit (.control work) space, rfl, rfl, rfl⟩

theorem saturated_load_still_admits_peer_control (limits : Limits) (counts : Counts)
    (work : ControlWork) (idleControl : counts.control = 0)
    (applicationsFull : counts.application = limits.capacity.application)
    (bulkFull : counts.bulk = limits.capacity.bulk) :
    ∃ admitted, Step limits counts admitted ∧ admitted.control = 1 ∧
      admitted.application = limits.capacity.application ∧ admitted.bulk = limits.capacity.bulk := by
  have available : counts.control < limits.capacity.control := idleControl.symm ▸ limits.reserved
  obtain ⟨admitted, step, stays, applications, bulk⟩ :=
    admit_control_with_other_lanes_full limits counts work available
  exact ⟨admitted, step, by simpa [idleControl] using stays,
    applications.trans applicationsFull, bulk.trans bulkFull⟩

theorem app_and_bulk_do_not_spend_control (counts : Counts) (f : Nat → Nat) :
    (counts.change f .application).control = counts.control ∧
      (counts.change f .bulk).control = counts.control := ⟨rfl, rfl⟩

theorem pressure_does_not_spend_reserves (counts : Counts) (f : Nat → Nat)
    {lane : Lane} (data : lane = .application ∨ lane = .bulk ∨ lane = .replication) :
    (counts.change f lane).control = counts.control ∧
      (counts.change f lane).maintenance = counts.maintenance := by
  rcases data with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem saturated_data_admits_control_and_maintenance (limits : Limits) (counts : Counts)
    (work : ControlWork) (idleControl : counts.control = 0) (idleMaintenance : counts.maintenance = 0) :
    let control := counts.change (· + 1) (.control work)
    let maintenance := control.change (· + 1) .maintenance
    Step limits counts control ∧ Step limits control maintenance ∧
      maintenance.application = counts.application ∧ maintenance.bulk = counts.bulk ∧
      maintenance.replication = counts.replication :=
  ⟨.admit (.control work) (by simpa [Counts.get, idleControl] using limits.reserved),
    .admit .maintenance (by simpa [Counts.get, Counts.change, idleMaintenance] using limits.maintenanceReserved),
    rfl, rfl, rfl⟩

/-- Each abstract recovery control operation can enter, and a completed
    operation returns its permit with the application and bulk loads intact.
    The completion step does not assert scheduler, delivery or disk progress. -/
theorem peer_control_permit_reusable (limits : Limits) (counts : Counts)
    (work : ControlWork) (space : counts.control < limits.capacity.control) :
    Step limits counts (counts.change (· + 1) (.control work)) ∧
      Step limits (counts.change (· + 1) (.control work)) counts := by
  let busy := counts.change (· + 1) (.control work)
  have acquired : Step limits counts busy := .admit (.control work) space
  have present : 0 < busy.get (.control work) := by
    simp [busy, Counts.get, Counts.change]
  have released : Step limits busy (busy.change (· - 1) (.control work)) := .release (.control work) present
  have restores : busy.change (· - 1) (.control work) = counts := by
    cases counts
    simp [busy, Counts.change]
  exact ⟨acquired, restores ▸ released⟩

/-- An abstract protocol schedule with a reusable permit available at every
    step. One protocol step may expand to several serial control operations. -/
inductive ReservedTrace [DecidableEq Application] (limits : Limits) (counts : Counts) :
    State Application → State Application → Prop
  | nil {state} : ReservedTrace limits counts state state
  | next {first before after} :
      ReservedTrace limits counts first before → LeaderJournal.Step before after →
      (∀ work : ControlWork, Step limits counts (counts.change (· + 1) (.control work)) ∧
        Step limits (counts.change (· + 1) (.control work)) counts) →
      ReservedTrace limits counts first after

theorem reserve_protocol_trace [DecidableEq Application] {before after : State Application}
    (trace : LeaderJournal.Trace before after) (limits : Limits) (counts : Counts)
    (space : counts.control < limits.capacity.control) : ReservedTrace limits counts before after := by
  induction trace with
  | nil => exact .nil
  | snoc _ step prior => exact .next prior step (fun work => peer_control_permit_reusable limits counts work space)

/-- Conditional composition. Recovery is feasible under an available
    eligible election and delivery/durable service of the scheduled steps;
    competing admissions cannot consume the vote permit. -/
theorem saturated_budget_allows_recovery_schedule [DecidableEq Payload] {core : Cluster Payload}
    (sound : Sound core) (election : Election core) (limits : Limits) (counts : Counts)
    (idleControl : counts.control = 0)
    (applicationsFull : counts.application = limits.capacity.application)
    (bulkFull : counts.bulk = limits.capacity.bulk) :
    (∃ scheduled, Step limits counts scheduled ∧ scheduled.control = 1 ∧
      scheduled.application = limits.capacity.application ∧ scheduled.bulk = limits.capacity.bulk) ∧
    ∃ recovered : Cluster Payload, ∃ call : HeadRead core recovered,
      core.committed <+: recovered.committed ∧ call.captured = recovered ∧
        ReservedTrace limits counts core call.captured := by
  refine ⟨saturated_load_still_admits_peer_control limits counts .vote idleControl
    applicationsFull bulkFull, ?_⟩
  obtain ⟨recovered, call, preserved, _, capture, _⟩ := recover_and_serve sound election
  have space : counts.control < limits.capacity.control := idleControl.symm ▸ limits.reserved
  exact ⟨recovered, call, preserved, capture,
    reserve_protocol_trace call.invokedBeforeCapture limits counts space⟩

inductive WireClass where
  | control
  | replication
  | bulk
  deriving DecidableEq, Repr

inductive PeerWork (Payload : Type) where
  | vote
  | append (entries : Log (Request Payload))
  | snapshot

def carriesUserRecord (entry : Entry (Request Payload)) : Bool :=
  match entry.command with
  | .apply (.append ..) => true
  | _ => false

def classify : PeerWork Payload → WireClass
  | .vote => .control
  | .append entries => if entries.any carriesUserRecord then .replication else .control
  | .snapshot => .bulk

structure FrameLimits where
  control : Nat
  replication : Nat
  bulk : Nat

structure Header where
  lane : WireClass
  bytes : Nat

def Header.allowed (header : Header) (limits : FrameLimits) : Prop :=
  0 < header.bytes ∧ header.bytes ≤ match header.lane with
    | .control => limits.control
    | .replication => limits.replication
    | .bulk => limits.bulk

/-- Header length and charge are checked before allocation. Classification is
    checked against the *whole* decoded operation before dispatch. -/
def Header.matches (header : Header) (work : PeerWork Payload) : Prop :=
  header.lane = classify work

theorem append_with_user_record_uses_data {entries : Log (Request Payload)}
    (hasRecord : entries.any carriesUserRecord = true) :
    classify (.append entries) = .replication := by simp [classify, hasRecord]

theorem control_header_cannot_dispatch_payload {header : Header} {entries : Log (Request Payload)}
    (claimed : header.lane = .control) (hasRecord : entries.any carriesUserRecord = true) :
    ¬ header.matches (.append entries) := by
  simp [Header.matches, claimed, append_with_user_record_uses_data hasRecord]

theorem vote_and_empty_append_are_control :
    classify (PeerWork.vote : PeerWork Payload) = .control ∧
      classify (PeerWork.append [] : PeerWork Payload) = .control := ⟨rfl, rfl⟩

structure BodyCharge where
  sender : KeeperId
  bytes : Nat
  deriving DecidableEq, Repr

def BodyCharge.weight (charge : BodyCharge) (sender : Option KeeperId) : Nat :=
  if sender = none ∨ sender = some charge.sender then charge.bytes else 0

abbrev Bodies := List (Option BodyCharge)

def bodyLoad (sender : Option KeeperId) : Bodies → Nat
  | [] => 0
  | slot :: rest => (slot.map (·.weight sender)).getD 0 + bodyLoad sender rest

structure BodyLimits where
  frames : FrameLimits
  keeper : Nat
  sender : Nat

def BodyValid (limits : BodyLimits) (bodies : Bodies) : Prop :=
  bodyLoad none bodies ≤ limits.keeper ∧
    ∀ sender, bodyLoad (some sender) bodies ≤ limits.sender

def CanReceiveBody (limits : BodyLimits) (bodies : Bodies) (authenticated : KeeperId)
    (header : Header) : Prop :=
  header.lane = .replication ∧ header.allowed limits.frames ∧
    bodyLoad none bodies + header.bytes ≤ limits.keeper ∧
    bodyLoad (some authenticated) bodies + header.bytes ≤ limits.sender

private theorem body_load_append (sender : Option KeeperId) (bodies : Bodies) (charge : BodyCharge) :
    bodyLoad sender (bodies ++ [some charge]) = bodyLoad sender bodies + charge.weight sender := by
  induction bodies with
  | nil => simp [bodyLoad]
  | cons slot rest ih => simp only [List.cons_append, bodyLoad, ih, Nat.add_assoc]

theorem reserve_body_preserves_budget {limits : BodyLimits} {bodies : Bodies} {authenticated : KeeperId}
    {header : Header} (valid : BodyValid limits bodies)
    (allowed : CanReceiveBody limits bodies authenticated header) :
    BodyValid limits (bodies ++ [some ⟨authenticated, header.bytes⟩]) := by
  refine ⟨by simpa [body_load_append, BodyCharge.weight] using allowed.2.2.1, fun sender => ?_⟩
  by_cases same : sender = authenticated
  · subst sender
    simpa [body_load_append, BodyCharge.weight] using allowed.2.2.2
  · simpa [body_load_append, BodyCharge.weight, same] using valid.2 sender

private theorem body_load_set_none_le (sender : Option KeeperId) (bodies : Bodies) (ticket : Nat) :
    bodyLoad sender (bodies.set ticket none) ≤ bodyLoad sender bodies := by
  induction bodies generalizing ticket with
  | nil => exact Nat.le_refl _
  | cons slot rest ih =>
    cases ticket with
    | zero =>
      simp only [List.set_cons_zero, bodyLoad, Option.map_none, Option.getD_none, Nat.zero_add]
      exact Nat.le_add_left _ _
    | succ index => exact Nat.add_le_add_left (ih index) _

theorem release_body_preserves_budget {limits : BodyLimits} {bodies : Bodies} {ticket : Nat}
    (valid : BodyValid limits bodies) : BodyValid limits (bodies.set ticket none) :=
  ⟨Nat.le_trans (body_load_set_none_le none bodies ticket) valid.1,
    fun sender => Nat.le_trans (body_load_set_none_le (some sender) bodies ticket) (valid.2 sender)⟩

theorem closed_body_cannot_release_twice {bodies : Bodies} {ticket : Nat} {charge : BodyCharge}
    (held : bodies[ticket]? = some (some charge)) :
    (bodies.set ticket none)[ticket]? = some none := by
  have present := (List.getElem?_eq_some_iff.mp held).1
  simp [present]

private def exampleBodyLimits : BodyLimits := ⟨⟨2, 8, 16⟩, 12, 6⟩
private def exampleFullSender : Bodies := [some ⟨7, 6⟩]
private def exampleFullKeeper : Bodies := [some ⟨7, 6⟩, some ⟨8, 6⟩]

theorem one_sender_cannot_spend_others_remaining_body_capacity :
    ¬ CanReceiveBody exampleBodyLimits exampleFullSender 7 ⟨.replication, 1⟩ ∧
      CanReceiveBody exampleBodyLimits exampleFullSender 8 ⟨.replication, 6⟩ ∧
      ¬ CanReceiveBody exampleBodyLimits exampleFullKeeper 9 ⟨.replication, 1⟩ := by
  unfold CanReceiveBody Header.allowed
  decide

/-- The worker checks one lane per opportunity. Empty lanes advance without
    I/O. A nonempty lane gets one bounded quantum, possibly a group commit. -/
inductive ServiceLane where
  | control
  | maintenance
  | replication
  | application
  | bulk
  deriving DecidableEq, Repr

def ServiceLane.slot : ServiceLane → Nat
  | .control => 0
  | .maintenance => 1
  | .replication => 2
  | .application => 3
  | .bulk => 4

def laneAt (turn : Nat) : ServiceLane :=
  match turn % 5 with
  | 0 => .control
  | 1 => .maintenance
  | 2 => .replication
  | 3 => .application
  | _ => .bulk

def serve (pending : Nat → ServiceLane → Bool) (turn : Nat) : Option ServiceLane :=
  let lane := laneAt turn
  if pending turn lane then some lane else none

private theorem slot_within_rotation {width slot : Nat} (start : Nat) (valid : slot < width) :
    ∃ delay < width, (start + delay) % width = slot := by
  have startSmall := Nat.mod_lt start (by omega : 0 < width)
  by_cases ahead : start % width ≤ slot
  · refine ⟨slot - start % width, by omega, ?_⟩
    rw [← Nat.mod_add_mod]
    have exactSlot : start % width + (slot - start % width) = slot := by omega
    rw [exactSlot, Nat.mod_eq_of_lt valid]
  · refine ⟨width + slot - start % width, by omega, ?_⟩
    rw [← Nat.mod_add_mod]
    have exactSlot : start % width + (width + slot - start % width) = width + slot := by omega
    rw [exactSlot, Nat.add_mod_left, Nat.mod_eq_of_lt valid]

theorem persistent_lane_served_within_five (pending : Nat → ServiceLane → Bool)
    (turn : Nat) (lane : ServiceLane)
    (staysPending : ∀ delay < 5, pending (turn + delay) lane = true) :
    ∃ delay < 5, serve pending (turn + delay) = some lane := by
  have slotSmall : lane.slot < 5 := by cases lane <;> decide
  obtain ⟨delay, within, slotExact⟩ := slot_within_rotation turn slotSmall
  have chooses : laneAt (turn + delay) = lane := by
    unfold laneAt
    rw [slotExact]
    cases lane <;> rfl
  exact ⟨delay, within, by simp [serve, chooses, staysPending delay within]⟩

/-- A lane can give each admitted sender/stream queue a stable slot while it
    waits. One bounded quantum is drawn from that slot when it is ready. -/
def serveQueue (width : ServiceLane → Nat)
    (pending : Nat → ServiceLane → Nat → Bool) (turn : Nat) : Option (ServiceLane × Nat) :=
  let lane := laneAt turn
  let slot := (turn / 5) % width lane
  if pending turn lane slot then some (lane, slot) else none

theorem persistent_queue_served_within_rotation (width : ServiceLane → Nat)
    (pending : Nat → ServiceLane → Nat → Bool) (turn : Nat) (lane : ServiceLane) (slot : Nat)
    (assigned : slot < width lane)
    (staysPending : ∀ delay < 5 * width lane, pending (turn + delay) lane slot = true) :
    ∃ delay < 5 * width lane, serveQueue width pending (turn + delay) = some (lane, slot) := by
  have laneSmall : lane.slot < 5 := by cases lane <;> decide
  obtain ⟨first, firstSmall, firstLane⟩ := slot_within_rotation turn laneSmall
  obtain ⟨rounds, roundsSmall, roundSlot⟩ := slot_within_rotation ((turn + first) / 5) assigned
  let delay := first + 5 * rounds
  have within : delay < 5 * width lane := by dsimp [delay]; omega
  have atLane : laneAt (turn + delay) = lane := by
    unfold laneAt
    rw [show turn + delay = (turn + first) + 5 * rounds by simp [delay, Nat.add_assoc],
      Nat.add_comm (turn + first) (5 * rounds), Nat.mul_add_mod_self_left, firstLane]
    cases lane <;> rfl
  have atSlot : ((turn + delay) / 5) % width lane = slot := by
    rw [show turn + delay = (turn + first) + 5 * rounds by simp [delay, Nat.add_assoc],
      Nat.add_mul_div_left _ _ (by decide : 0 < 5), roundSlot]
  exact ⟨delay, within, by simp [serveQueue, atLane, atSlot, staysPending delay within]⟩

#print axioms step_preserves_budget
#print axioms saturated_load_still_admits_peer_control
#print axioms app_and_bulk_do_not_spend_control
#print axioms peer_control_permit_reusable
#print axioms reserve_protocol_trace
#print axioms saturated_budget_allows_recovery_schedule
#print axioms control_header_cannot_dispatch_payload
#print axioms reserve_body_preserves_budget
#print axioms persistent_queue_served_within_rotation

end Logkeeper.LeaderJournal.PeerBudget
