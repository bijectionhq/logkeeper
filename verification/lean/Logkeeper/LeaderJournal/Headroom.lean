import Logkeeper.LeaderJournal.Media
import Logkeeper.LeaderJournal.PeerBudget
import Logkeeper.LeaderJournal.ReplicaGate

namespace Logkeeper.LeaderJournal.Headroom

set_option warningAsError true

structure Allocation where
  bytes : Nat
  entries : Nat
  deriving DecidableEq, Repr

def tally (weight : Allocation → Nat) : List (Option Allocation) → Nat
  | [] => 0
  | entry :: rest => (entry.map weight).getD 0 + tally weight rest

abbrev booked := tally Allocation.bytes

private theorem tally_append (weight : Allocation → Nat) (slots : List (Option Allocation)) (allocation : Allocation) :
    tally weight (slots ++ [some allocation]) = tally weight slots + weight allocation := by
  induction slots with
  | nil => simp [tally]
  | cons slot rest ih => simp only [List.cons_append, tally, ih, Nat.add_assoc]

private theorem tally_clear (weight : Allocation → Nat) {slots : List (Option Allocation)} {ticket : Nat} {allocation : Allocation}
    (openTicket : slots[ticket]? = some (some allocation)) :
    tally weight (slots.set ticket none) + weight allocation = tally weight slots := by
  induction slots generalizing ticket with
  | nil => cases openTicket
  | cons slot rest ih =>
    cases ticket with
    | zero =>
      simp at openTicket
      subst slot
      simp [tally, Nat.add_comm]
    | succ index =>
      simp only [List.getElem?_cons_succ] at openTicket
      simp only [List.set_cons_succ, tally]
      rw [Nat.add_assoc, ih openTicket]

structure Pool where
  used : Nat
  /-- Never recycle a ticket number, even after completion or cancel. -/
  tickets : List (Option Allocation)
  deriving DecidableEq, Repr

def Pool.charged (p : Pool) : Nat := p.used + booked p.tickets

def Pool.openSlots (p : Pool) : Nat := tally Allocation.entries p.tickets

def Pool.reserveBatch (p : Pool) (allocation : Allocation) : Pool :=
  { p with tickets := p.tickets ++ [some allocation] }

def Pool.reserve (p : Pool) (bytes : Nat) : Pool := p.reserveBatch ⟨bytes, 1⟩

def Pool.settle (p : Pool) (ticket actual : Nat) : Pool :=
  ⟨p.used + actual, p.tickets.set ticket none⟩

theorem Pool.reserve_batch_charge (p : Pool) (allocation : Allocation) :
    (p.reserveBatch allocation).charged = p.charged + allocation.bytes := by
  simp [reserveBatch, charged, tally_append, Nat.add_assoc]

theorem Pool.reserve_batch_slots (p : Pool) (allocation : Allocation) :
    (p.reserveBatch allocation).openSlots = p.openSlots + allocation.entries :=
  tally_append _ _ _

theorem Pool.batch_ticket_is_fresh (p : Pool) (allocation : Allocation) :
    (p.reserveBatch allocation).tickets[p.tickets.length]? = some (some allocation) ∧
      ∀ ticket held, p.tickets[ticket]? = some (some held) →
        ticket < p.tickets.length ∧ (p.reserveBatch allocation).tickets[ticket]? = some (some held) := by
  refine ⟨by simp [reserveBatch], fun ticket held occupied => ?_⟩
  have earlier := (List.getElem?_eq_some_iff.mp occupied).1
  exact ⟨earlier, by simpa only [reserveBatch, List.getElem?_append_left earlier] using occupied⟩

theorem Pool.reserve_charge (p : Pool) (bytes : Nat) :
    (p.reserve bytes).charged = p.charged + bytes :=
  p.reserve_batch_charge _

theorem Pool.reserve_slot (p : Pool) (bytes : Nat) :
    (p.reserve bytes).openSlots = p.openSlots + 1 :=
  p.reserve_batch_slots _

theorem Pool.settle_slot {p : Pool} {ticket actual : Nat} {reserved : Allocation}
    (openTicket : p.tickets[ticket]? = some (some reserved)) :
    (p.settle ticket actual).openSlots + reserved.entries = p.openSlots :=
  tally_clear _ openTicket

theorem Pool.settle_charge {p : Pool} {ticket actual : Nat} {reserved : Allocation}
    (openTicket : p.tickets[ticket]? = some (some reserved)) (within : actual ≤ reserved.bytes) :
    (p.settle ticket actual).charged ≤ p.charged := by
  have balance := tally_clear Allocation.bytes openTicket
  simp only [charged, settle]
  change booked (p.tickets.set ticket none) + reserved.bytes = booked p.tickets at balance
  omega

theorem Pool.settling_twice_refused {p : Pool} {ticket actual : Nat} {reserved : Allocation}
    (openTicket : p.tickets[ticket]? = some (some reserved)) :
    (p.settle ticket actual).tickets[ticket]? = some none := by
  have present := (List.getElem?_eq_some_iff.mp openTicket).1
  simp [settle, present]

inductive Class where
  | ordinary
  | control
  | transfer
  deriving DecidableEq

structure Limits where
  volume : Nat
  ordinary : Nat
  control : Nat
  maintenanceControl : Nat
  maintenanceScratch : Nat
  transfer : Nat
  external : Nat
  suffix : Nat
  metadataUpdates : Nat
  extentOperations : Nat
  provisioned : ordinary + control + maintenanceControl + maintenanceScratch + transfer + external ≤ volume

/-- A conservative sum of bytes simultaneously charged during a batch. Transfers
    use their own independent pool. -/
structure Batch where
  walCopy : Nat
  retainedSnapshot : Nat
  manifest : Nat
  overlap : Nat
  oldBytes : Nat
  replacementBytes : Nat
  purgeEntries : Nat
  controlBytes : Nat
  metadataUpdates : Nat
  extentOperations : Nat
  deriving DecidableEq, Repr

def Batch.peak (b : Batch) : Nat := b.walCopy + b.retainedSnapshot + b.manifest + b.overlap

inductive Phase where
  | copying
  | filesDurable
  | published
  | purged
  | failed
  deriving DecidableEq, Repr

structure Job where
  batch : Batch
  oldBasis : Nat
  phase : Phase
  deriving DecidableEq, Repr

structure Volume where
  ordinary : Pool
  control : Pool
  transfers : Pool
  maintenanceUsed : Nat
  external : Nat
  suffix : Nat
  basis : Nat
  pins : Nat → Nat
  job : Option Job

def Volume.pool (s : Volume) : Class → Pool
  | .ordinary => s.ordinary
  | .control => s.control
  | .transfer => s.transfers

def Volume.withPool (s : Volume) (pool : Pool) : Class → Volume
  | .ordinary => { s with ordinary := pool }
  | .control => { s with control := pool }
  | .transfer => { s with transfers := pool }

def Volume.scratch (s : Volume) : Nat := (s.job.map (·.batch.peak)).getD 0

def Volume.suffixLoad (s : Volume) : Nat := s.suffix + s.ordinary.openSlots

def Volume.maintenance (s : Volume) : Nat :=
  s.maintenanceUsed + match s.job with
  | some job => if job.phase = .purged then 0 else job.batch.controlBytes
  | none => 0

def Volume.charged (s : Volume) : Nat :=
  s.ordinary.charged + s.control.charged + s.maintenance + s.scratch + s.transfers.charged + s.external

def Valid (limits : Limits) (s : Volume) : Prop :=
  s.ordinary.charged ≤ limits.ordinary ∧ s.control.charged ≤ limits.control ∧
    s.maintenance ≤ limits.maintenanceControl ∧ s.scratch ≤ limits.maintenanceScratch ∧
    s.transfers.charged ≤ limits.transfer ∧ s.external ≤ limits.external

def CanReserve (limits : Limits) (s : Volume) (bytes : Nat) : Class → Prop
  | .ordinary => s.ordinary.charged + bytes ≤ limits.ordinary ∧ s.suffixLoad < limits.suffix
  | .control => s.control.charged + bytes ≤ limits.control
  | .transfer => s.transfers.charged + bytes ≤ limits.transfer

/-- One receiving disk reservation for an ordered batch, using the same pool
    as local append. The reserved entries bound new physical suffix occupancy. -/
def CanReserveBatch (limits : Limits) (s : Volume) (allocation : Allocation) : Prop :=
  s.ordinary.charged + allocation.bytes ≤ limits.ordinary ∧
    s.suffixLoad + allocation.entries ≤ limits.suffix

def Volume.reserveBatch (s : Volume) (allocation : Allocation) : Volume :=
  { s with ordinary := s.ordinary.reserveBatch allocation }

def Volume.completeBatch (s : Volume) (ticket : Nat) (actual : Allocation) : Volume :=
  { s with ordinary := s.ordinary.settle ticket actual.bytes, suffix := s.suffix + actual.entries }

def FitsScratch (limits : Limits) (b : Batch) : Prop :=
  b.peak ≤ limits.maintenanceScratch

def CanPurge (limits : Limits) (s : Volume) (b : Batch) : Prop :=
  s.maintenanceUsed + b.controlBytes ≤ limits.maintenanceControl ∧ b.purgeEntries ≤ s.suffix

def BoundedLocalWork (limits : Limits) (b : Batch) : Prop :=
  b.retainedSnapshot = 0 ∧ b.metadataUpdates ≤ limits.metadataUpdates ∧
    b.extentOperations ≤ limits.extentOperations

def CanStart (limits : Limits) (s : Volume) (b : Batch) : Prop :=
  s.job = none ∧ FitsScratch limits b ∧ BoundedLocalWork limits b ∧ CanPurge limits s b ∧
    b.oldBytes ≤ s.ordinary.used ∧ b.replacementBytes ≤ b.oldBytes ∧ b.replacementBytes ≤ b.peak

def Volume.start (s : Volume) (b : Batch) : Volume :=
  { s with job := some ⟨b, s.basis, .copying⟩ }

def Volume.advance (s : Volume) (job : Job) (phase : Phase) : Volume :=
  { s with job := some { job with phase } }

def Volume.publish (s : Volume) (job : Job) : Volume :=
  { s.advance job .published with basis := s.basis + 1 }

def Volume.purge (s : Volume) (job : Job) : Volume :=
  { s.advance job .purged with
    suffix := s.suffix - job.batch.purgeEntries
    maintenanceUsed := s.maintenanceUsed + job.batch.controlBytes }

def Volume.finish (s : Volume) (job : Job) : Volume :=
  { s with
    ordinary := { s.ordinary with used := s.ordinary.used - job.batch.oldBytes + job.batch.replacementBytes }
    job := none }

/-- Each success transition is the recorded outcome of the specified durable
    I/O. Jobs and charges survive crash or are reconstructed pessimistically. -/
inductive Step (limits : Limits) : Volume → Volume → Prop
  | reserve {s} (kind : Class) (bytes : Nat) (allowed : CanReserve limits s bytes kind) :
    Step limits s (s.withPool ((s.pool kind).reserve bytes) kind)
  | settle {s} (kind : Class) (ticket : Nat) (reserved : Allocation) (actual : Nat)
      (held : (s.pool kind).tickets[ticket]? = some (some reserved)) (within : actual ≤ reserved.bytes) :
    Step limits s (s.withPool ((s.pool kind).settle ticket actual) kind)
  | reserveBatch {s} (allocation : Allocation) (allowed : CanReserveBatch limits s allocation) :
    Step limits s (s.reserveBatch allocation)
  | completeBatch {s} (ticket : Nat) (reserved actual : Allocation)
      (held : s.ordinary.tickets[ticket]? = some (some reserved))
      (bytes : actual.bytes ≤ reserved.bytes) (slots : actual.entries ≤ reserved.entries) :
    Step limits s (s.completeBatch ticket actual)
  | start {s} (b : Batch) (allowed : CanStart limits s b) : Step limits s (s.start b)
  | syncFiles {s job} (pending : s.job = some job) (phase : job.phase = .copying) :
    Step limits s (s.advance job .filesDurable)
  | publish {s job} (pending : s.job = some job) (phase : job.phase = .filesDurable) :
    Step limits s (s.publish job)
  | purge {s job} (pending : s.job = some job) (phase : job.phase = .published)
      (controlSpace : CanPurge limits s job.batch) :
    Step limits s (s.purge job)
  | releaseObsoleteControl {s} (bytes : Nat) (allocated : bytes ≤ s.maintenanceUsed) :
    Step limits s { s with maintenanceUsed := s.maintenanceUsed - bytes }
  | finishUnlink {s job} (pending : s.job = some job) (phase : job.phase = .purged)
      (unreferenced : s.pins job.oldBasis = 0) (oldCharged : job.batch.oldBytes ≤ s.ordinary.used)
      (net : job.batch.replacementBytes ≤ job.batch.oldBytes) :
    Step limits s (s.finish job)
  | failCopy {s job} (pending : s.job = some job)
      (phase : job.phase = .copying ∨ job.phase = .filesDurable) :
    Step limits s (s.advance job .failed)
  | cleanedFailure {s job} (pending : s.job = some job) (phase : job.phase = .failed) :
    Step limits s { s with job := none }
  | pin {s} : Step limits s { s with pins := update s.pins s.basis (s.pins s.basis + 1) }
  | unpin {s} (basis : Nat) (outstanding : 0 < s.pins basis) :
    Step limits s { s with pins := update s.pins basis (s.pins basis - 1) }
  | crash {s} : Step limits s s

inductive Trace (limits : Limits) : Volume → Volume → Prop
  | refl (s : Volume) : Trace limits s s
  | next {a b c} : Trace limits a b → Step limits b c → Trace limits a c

theorem physical_bound {limits : Limits} {s : Volume} (valid : Valid limits s) :
    s.charged ≤ limits.volume := by
  have cap := limits.provisioned
  obtain ⟨ordinary, control, maintenance, scratch, transfers, external⟩ := valid
  unfold Volume.charged
  omega

theorem step_preserves_separate_budgets {limits : Limits} {s t : Volume}
    (valid : Valid limits s) (step : Step limits s t) : Valid limits t := by
  obtain ⟨ordinary, control, maintenance, scratch, transfers, external⟩ := valid
  cases step with
  | reserve kind bytes allowed =>
    cases kind with
    | ordinary => exact ⟨by simpa [Volume.withPool, Volume.pool, Pool.reserve_charge] using allowed.1,
        control, maintenance, scratch, transfers, external⟩
    | control => exact ⟨ordinary, by simpa [Volume.withPool, Volume.pool, Pool.reserve_charge, CanReserve] using allowed,
        maintenance, scratch, transfers, external⟩
    | transfer => exact ⟨ordinary, control, maintenance, scratch,
        by simpa [Volume.withPool, Volume.pool, Pool.reserve_charge, CanReserve] using allowed, external⟩
  | settle kind ticket reserved actual held within =>
    have smaller := Pool.settle_charge held within
    cases kind with
    | ordinary => exact ⟨Nat.le_trans smaller ordinary, control, maintenance, scratch, transfers, external⟩
    | control => exact ⟨ordinary, Nat.le_trans smaller control, maintenance, scratch, transfers, external⟩
    | transfer => exact ⟨ordinary, control, maintenance, scratch, Nat.le_trans smaller transfers, external⟩
  | reserveBatch allocation allowed =>
    exact ⟨by simpa [Volume.reserveBatch, Pool.reserve_batch_charge] using allowed.1,
      control, maintenance, scratch, transfers, external⟩
  | completeBatch _ _ _ held bytes _ =>
    exact ⟨Nat.le_trans (Pool.settle_charge held bytes) ordinary, control, maintenance, scratch, transfers, external⟩
  | start b allowed => exact ⟨ordinary, control, allowed.2.2.2.1.1, allowed.2.1, transfers, external⟩
  | syncFiles pending phase =>
    exact ⟨ordinary, control, by simpa [Volume.maintenance, Volume.advance, pending, phase] using maintenance,
      by simpa [Volume.scratch, Volume.advance, pending] using scratch, transfers, external⟩
  | failCopy pending phase =>
    rcases phase with phase | phase <;>
      exact ⟨ordinary, control, by simpa [Volume.maintenance, Volume.advance, pending, phase] using maintenance,
        by simpa [Volume.scratch, Volume.advance, pending] using scratch, transfers, external⟩
  | publish pending phase =>
    exact ⟨ordinary, control, by simpa [Volume.maintenance, Volume.publish, Volume.advance, pending, phase] using maintenance,
      by simpa [Volume.scratch, Volume.publish, Volume.advance, pending] using scratch, transfers, external⟩
  | purge pending _ controlSpace =>
    exact ⟨ordinary, control, by simpa [Volume.maintenance, Volume.purge, Volume.advance] using controlSpace.1,
      by simpa [Volume.scratch, Volume.purge, Volume.advance, pending] using scratch, transfers, external⟩
  | releaseObsoleteControl bytes _ =>
    refine ⟨ordinary, control, ?_, scratch, transfers, external⟩
    exact Nat.le_trans (Nat.add_le_add_right (Nat.sub_le _ bytes) _) maintenance
  | finishUnlink pending phase _ oldCharged net =>
    refine ⟨?_, control, ?_, Nat.zero_le _, transfers, external⟩
    · simp only [Volume.finish, Pool.charged] at ordinary ⊢
      omega
    · simpa [Volume.maintenance, Volume.finish, pending, phase] using maintenance
  | cleanedFailure =>
    exact ⟨ordinary, control, Nat.le_trans (Nat.le_add_right _ _) maintenance, Nat.zero_le _, transfers, external⟩
  | pin | unpin | crash => exact ⟨ordinary, control, maintenance, scratch, transfers, external⟩

theorem trace_preserves_physical_bound {limits : Limits} {s t : Volume}
    (valid : Valid limits s) (trace : Trace limits s t) : Valid limits t ∧ t.charged ≤ limits.volume := by
  have preserved : Valid limits t := by
    induction trace with
    | refl => exact valid
    | next _ step prior => exact step_preserves_separate_budgets prior step
  exact ⟨preserved, physical_bound preserved⟩

theorem step_preserves_suffix_limit {limits : Limits} {s t : Volume}
    (valid : s.suffixLoad ≤ limits.suffix) (step : Step limits s t) : t.suffixLoad ≤ limits.suffix := by
  cases step with
  | reserve kind bytes allowed =>
    cases kind with
    | ordinary =>
      have openSlot := allowed.2
      simpa [Volume.suffixLoad, Volume.withPool, Volume.pool, Pool.reserve_slot, Nat.add_assoc]
        using Nat.succ_le_of_lt openSlot
    | control | transfer => exact valid
  | settle kind ticket _ actual held _ =>
    cases kind with
    | ordinary =>
      have slots := Pool.settle_slot (actual := actual) held
      change (s.ordinary.settle ticket actual).openSlots + _ = s.ordinary.openSlots at slots
      change s.suffix + (s.ordinary.settle ticket actual).openSlots ≤ limits.suffix
      unfold Volume.suffixLoad at valid
      omega
    | control | transfer => exact valid
  | reserveBatch allocation allowed =>
    simpa [Volume.reserveBatch, Volume.suffixLoad, Pool.reserve_batch_slots, Nat.add_assoc] using allowed.2
  | completeBatch ticket _ actual held _ count =>
    have slots := Pool.settle_slot (actual := actual.bytes) held
    change s.suffix + actual.entries + (s.ordinary.settle ticket actual.bytes).openSlots ≤ limits.suffix
    unfold Volume.suffixLoad at valid
    omega
  | purge =>
    exact Nat.le_trans (Nat.add_le_add_right (Nat.sub_le _ _) _) valid
  | _ => exact valid

theorem transfers_cannot_consume_maintenance {limits : Limits} {s : Volume} {b : Batch}
    (allowed : CanStart limits s b) (bytes : Nat) :
    CanStart limits (s.withPool (s.transfers.reserve bytes) .transfer) b := allowed

theorem trace_preserves_suffix_limit {limits : Limits} {s t : Volume}
    (valid : s.suffixLoad ≤ limits.suffix) (trace : Trace limits s t) : t.suffixLoad ≤ limits.suffix := by
  induction trace with
  | refl => exact valid
  | next _ step prior => exact step_preserves_suffix_limit prior step

theorem failed_publication_keeps_old_basis (s : Volume) (job : Job) :
    (s.advance job .failed).basis = s.basis ∧ (s.advance job .failed).scratch = job.batch.peak := ⟨rfl, rfl⟩

theorem pinned_basis_cannot_finish_unlink {s : Volume} {job : Job}
    (pinned : 0 < s.pins job.oldBasis) : s.pins job.oldBasis ≠ 0 := Nat.ne_of_gt pinned

theorem snapshot_alone_can_exceed_a_wal_only_bound {limits : Limits} {b : Batch}
    (snapshotTooLarge : limits.maintenanceScratch < b.retainedSnapshot) :
    ¬ FitsScratch limits b := by
  intro room
  unfold FitsScratch Batch.peak at room
  omega

/-- Purge advances the Raft floor independently of old readers and physical
    unlink. The current job still owns its scratch and obsolete blocks. -/
theorem purge_reopens_suffix_while_pinned {limits : Limits} {s : Volume} {job : Job}
    (pending : s.job = some job) (published : job.phase = .published)
    (controlSpace : CanPurge limits s job.batch)
    (enough : s.suffix - job.batch.purgeEntries + s.ordinary.openSlots < limits.suffix) :
    Step limits s (s.purge job) ∧ (s.purge job).suffixLoad < limits.suffix ∧
      (s.purge job).ordinary = s.ordinary ∧ (s.purge job).pins = s.pins :=
  ⟨.purge pending published controlSpace, enough, rfl, rfl⟩

/-- A finite progress witness, conditional on the batch's physical peak,
    reclaimable unpinned bytes and schedule of successful durable effects.
    Purge is independent of foreground suffix admission. -/
theorem reclaim_then_admit {limits : Limits} {s : Volume} {b : Batch} (bytes : Nat)
    (valid : Valid limits s) (allowed : CanStart limits s b)
    (unreferenced : s.pins s.basis = 0)
    (freed : s.ordinary.charged - b.oldBytes + b.replacementBytes + bytes ≤ limits.ordinary)
    (suffixReopens : s.suffix - b.purgeEntries + s.ordinary.openSlots < limits.suffix) :
    ∃ after, Trace limits s after ∧ Valid limits after ∧ CanReserve limits after bytes .ordinary := by
  let job : Job := ⟨b, s.basis, .copying⟩
  let copying := s.start b
  let synced := copying.advance job .filesDurable
  let ready : Job := { job with phase := .filesDurable }
  let published := synced.publish ready
  let selected : Job := { job with phase := .published }
  let purged := published.purge selected
  let drained : Job := { job with phase := .purged }
  let after := purged.finish drained
  have start : Step limits s copying := .start b allowed
  have sync : Step limits copying synced := .syncFiles rfl rfl
  have publish : Step limits synced published := .publish rfl rfl
  have purge : Step limits published purged := .purge rfl rfl allowed.2.2.2.1
  have unlink : Step limits purged after :=
    .finishUnlink rfl rfl unreferenced allowed.2.2.2.2.1 allowed.2.2.2.2.2.1
  have trace : Trace limits s after :=
    .next (.next (.next (.next (.next (.refl _) start) sync) publish) purge) unlink
  refine ⟨after, trace, (trace_preserves_physical_bound valid trace).1, ?_, suffixReopens⟩
  change s.ordinary.used - b.oldBytes + b.replacementBytes + booked s.ordinary.tickets + bytes ≤ limits.ordinary
  have old := allowed.2.2.2.2.1
  simp only [Pool.charged] at freed
  omega

/-- The adapter binds the physical job to the exact authenticated image.
    Purge coverage counts additional entries in that durable applied cut. -/
theorem checked_publish_and_purge {limits : Limits} {s : Volume} {job : Job}
    {core : Cluster Payload} {keeper : KeeperId} {disk : Media.Disk Payload}
    {cut : Log (Request Payload)} (pending : s.job = some job) (filesDurable : job.phase = .filesDurable)
    (synced : disk.prepared = some ⟨cut, true⟩) (applied : cut <+: core.applied keeper)
    (represents : disk.selected.history = core.durable keeper) (sound : Sound core)
    (coversPurge : disk.selected.snapshot.length + job.batch.purgeEntries ≤ cut.length)
    (controlSpace : CanPurge limits s job.batch) :
    let selected := s.publish job
    let media := { disk with selected := Media.Image.install disk.selected.history cut, prepared := none }
    Step limits s selected ∧ Step limits selected (selected.purge { job with phase := .published }) ∧
      Media.Step disk media ∧ media.selected.history = core.durable keeper ∧
      core.applied keeper <+: media.selected.history ∧
      disk.selected.snapshot.length + job.batch.purgeEntries ≤ media.selected.snapshot.length := by
  dsimp only
  have available : cut <+: disk.selected.history := applied.trans (represents.symm ▸ (sound.applied keeper).2)
  have publish : Media.Step disk _ := .publish synced available
  have exactBasis := Media.compaction_refines_durable_replica (.snoc (.nil _) publish) represents sound
  exact ⟨.publish pending filesDurable, .purge rfl rfl controlSpace, publish, exactBasis.1, exactBasis.2, coversPurge⟩

private def exampleLimits : Limits := ⟨120, 80, 4, 4, 20, 10, 2, 4, 2, 2, by decide⟩
private def exampleBatch : Batch := ⟨12, 0, 6, 2, 24, 12, 1, 2, 2, 2⟩

private def saturated : Volume :=
  ⟨⟨80, []⟩, ⟨0, []⟩, ⟨0, [some ⟨10, 1⟩]⟩, 0, 2, 4, 7, fun _ => 0, none⟩

theorem full_writes_and_transfers_leave_maintenance_available :
    ¬ CanReserve exampleLimits saturated 1 .ordinary ∧
      ¬ CanReserve exampleLimits saturated 1 .transfer ∧
      CanStart exampleLimits saturated exampleBatch ∧
      ∃ after, Trace exampleLimits saturated after ∧ Valid exampleLimits after ∧
        CanReserve exampleLimits after 12 .ordinary := by
  have valid : Valid exampleLimits saturated := by
    unfold Valid
    decide
  have allowed : CanStart exampleLimits saturated exampleBatch := by
    unfold CanStart FitsScratch BoundedLocalWork CanPurge
    decide
  refine ⟨by unfold CanReserve; decide, by unfold CanReserve; decide, allowed, ?_⟩
  exact reclaim_then_admit 12 valid allowed (by decide) (by decide) (by decide)

namespace Follower

structure Batch (Payload : Type) where
  stream : Installation.StreamId
  sender : KeeperId
  term : Nat
  previous : Log (Request Payload)
  entries : Log (Request Payload)

def Batch.cut (batch : Batch Payload) : Log (Request Payload) := batch.previous ++ batch.entries

structure Write (Payload : Type) where
  batch : Batch Payload
  diskTicket : Nat
  reserved : Allocation
  uncertain : Bool := false

structure Limits where
  volume : Headroom.Limits
  ingress : PeerBudget.BodyLimits
  lanes : PeerBudget.Limits

structure State (Payload : Type) where
  volume : Volume
  bodies : PeerBudget.Bodies
  lanes : PeerBudget.Counts
  writes : Nat → Option (Write Payload)
  cores : Installation.StreamId → Cluster Payload

def State.receive (s : State Payload) (charge : PeerBudget.BodyCharge) : State Payload :=
  { s with bodies := s.bodies ++ [some charge], lanes := s.lanes.change (· + 1) .replication }

def State.submit (s : State Payload) (body : Nat) (batch : Batch Payload) (reserve : Allocation) :
    State Payload :=
  { s with volume := s.volume.reserveBatch reserve
           writes := update s.writes body (some ⟨batch, s.volume.ordinary.tickets.length, reserve, false⟩) }

def State.release (s : State Payload) (body : Nat) : State Payload :=
  { s with bodies := s.bodies.set body none, writes := update s.writes body none,
           lanes := s.lanes.change (· - 1) .replication }

def State.finish (s : State Payload) (body : Nat) (diskTicket : Nat) (actual : Allocation) :
    State Payload :=
  { s.release body with volume := s.volume.completeBatch diskTicket actual }

def State.markUncertain (s : State Payload) (body : Nat) (write : Write Payload) : State Payload :=
  { s with writes := update s.writes body (some { write with uncertain := true }) }

def State.recordDurable [DecidableEq Payload] (s : State Payload) (keeper : KeeperId)
    (batch : Batch Payload) : State Payload :=
  { s with cores := update s.cores batch.stream ((s.cores batch.stream).replicate keeper batch.cut) }

def CanReceive (limits : Limits) (s : State Payload) (sender : KeeperId)
    (header : PeerBudget.Header) : Prop :=
  PeerBudget.CanReceiveBody limits.ingress s.bodies sender header ∧
    s.lanes.replication < limits.lanes.capacity.replication

def Valid (limits : Limits) (s : State Payload) : Prop :=
  Headroom.Valid limits.volume s.volume ∧ s.volume.suffixLoad ≤ limits.volume.suffix ∧
    PeerBudget.BodyValid limits.ingress s.bodies ∧ PeerBudget.Valid limits.lanes s.lanes

/-- The durable callback is tied to a specific receiving keeper, stream and
    operation by the adapter. This certificate checks the protocol cut on
    that success path. A learner may persist the cut before it can vote. -/
structure Accepted (core : Cluster Payload) (keeper : KeeperId) (batch : Batch Payload) : Prop where
  active : core.active
  sender : core.leader = some batch.sender
  term : batch.term = core.term
  online : core.online keeper = true
  issued : batch.cut <+: core.issued

inductive Output (Payload : Type) where
  | pending
  | rejected
  | backpressure
  | unknown
  | storageFailure
  | reconciled
  | durableAck (body : Nat) (batch : Batch Payload)

def Output.evidence : Output Payload → Option (Batch Payload)
  | .durableAck _ batch => some batch
  | _ => none

/-- The bridge runs at one authenticated receiving keeper, sharing body and
    physical volume state across streams. Body IDs are append-only;
    the storage owner supplies the uniquely owned physical ticket. -/
inductive Step [DecidableEq Payload] (limits : Limits) (keeper : KeeperId) :
    State Payload → Output Payload → State Payload → Prop
  | receive {s} (sender : KeeperId) (header : PeerBudget.Header)
      (allowed : CanReceive limits s sender header) :
    Step limits keeper s .pending (s.receive ⟨sender, header.bytes⟩)
  | refuseIngress {s} (sender : KeeperId) (header : PeerBudget.Header)
      (full : ¬ CanReceive limits s sender header) :
    Step limits keeper s .backpressure s
  | refuseDisk {s} (body : Nat) (charge : PeerBudget.BodyCharge) (reserve : Allocation)
      (held : s.bodies[body]? = some (some charge)) (unsubmitted : s.writes body = none)
      (full : ¬ CanReserveBatch limits.volume s.volume reserve) :
    Step limits keeper s .backpressure (s.release body)
  | rejectOrCancel {s} (body : Nat) (charge : PeerBudget.BodyCharge)
      (held : s.bodies[body]? = some (some charge)) (unsubmitted : s.writes body = none) :
    Step limits keeper s .rejected (s.release body)
  | submit {s} (body : Nat) (charge : PeerBudget.BodyCharge) (batch : Batch Payload) (reserve : Allocation)
      (held : s.bodies[body]? = some (some charge)) (sender : charge.sender = batch.sender)
      (classMatches : PeerBudget.classify (.append batch.entries) = .replication)
      (unsubmitted : s.writes body = none) (positive : 0 < reserve.bytes)
      (allowed : CanReserveBatch limits.volume s.volume reserve) :
    Step limits keeper s .pending (s.submit body batch reserve)
  | timeout {s} (body : Nat) (write : Write Payload)
      (pending : s.writes body = some write) :
    Step limits keeper s .unknown (s.markUncertain body write)
  | syncFailed {s} (body : Nat) (write : Write Payload)
      (pending : s.writes body = some write) :
    Step limits keeper s .storageFailure (s.markUncertain body write)
  | crash {s} : Step limits keeper s .unknown s
  /-- Restart/cleanup has established actual allocations. This returns a
      resource ticket with zero or known charges and emits no new ack. -/
  | reconcile {s} (body : Nat) (charge : PeerBudget.BodyCharge) (write : Write Payload) (actual : Allocation)
      (bodyHeld : s.bodies[body]? = some (some charge)) (pending : s.writes body = some write)
      (diskHeld : s.volume.ordinary.tickets[write.diskTicket]? = some (some write.reserved))
      (bytes : actual.bytes ≤ write.reserved.bytes) (entries : actual.entries ≤ write.reserved.entries) :
    Step limits keeper s .reconciled (s.finish body write.diskTicket actual)
  /-- This transition is the successful durable write callback, including
      the required sync. Receipt of bytes or queue completion cannot use it. -/
  | synced {s} (body : Nat) (charge : PeerBudget.BodyCharge) (write : Write Payload) (actual : Allocation)
      (bodyHeld : s.bodies[body]? = some (some charge)) (pending : s.writes body = some write)
      (diskHeld : s.volume.ordinary.tickets[write.diskTicket]? = some (some write.reserved))
      (bytes : actual.bytes ≤ write.reserved.bytes) (entries : actual.entries ≤ write.reserved.entries)
      (waiting : write.uncertain = false) (accepted : Accepted (s.cores write.batch.stream) keeper write.batch) :
    Step limits keeper s (.durableAck body write.batch)
      ((s.finish body write.diskTicket actual).recordDurable keeper write.batch)

inductive Trace [DecidableEq Payload] (limits : Limits) (keeper : KeeperId) :
    State Payload → State Payload → Prop
  | refl (s : State Payload) : Trace limits keeper s s
  | next {a b c output} :
    Trace limits keeper a b → Step limits keeper b output c → Trace limits keeper a c

theorem admission_preserves_budgets [DecidableEq Payload] {limits : Limits} {keeper : KeeperId}
    {s t : State Payload} {output : Output Payload}
    (valid : Valid limits s) (step : Step limits keeper s output t) : Valid limits t := by
  obtain ⟨volume, suffix, bodies, lanes⟩ := valid
  have releaseBody (body : Nat) : PeerBudget.BodyValid limits.ingress (s.bodies.set body none) :=
    PeerBudget.release_body_preserves_budget bodies
  have releaseLane : PeerBudget.Valid limits.lanes (s.lanes.change (· - 1) .replication) := by
    obtain ⟨control, maintenance, data, ordinary, bulk⟩ := lanes
    exact ⟨control, maintenance, Nat.le_trans (Nat.sub_le _ _) data, ordinary, bulk⟩
  have settle {reserved actual : Allocation} {ticket : Nat}
      (held : s.volume.ordinary.tickets[ticket]? = some (some reserved))
      (bytes : actual.bytes ≤ reserved.bytes) (entries : actual.entries ≤ reserved.entries) :
      Headroom.Valid limits.volume (s.volume.completeBatch ticket actual) ∧
        (s.volume.completeBatch ticket actual).suffixLoad ≤ limits.volume.suffix := by
    have completed : Headroom.Step limits.volume s.volume (s.volume.completeBatch ticket actual) :=
      .completeBatch ticket reserved actual held bytes entries
    exact ⟨step_preserves_separate_budgets volume completed, step_preserves_suffix_limit suffix completed⟩
  cases step with
  | receive sender header allowed =>
    exact ⟨volume, suffix, PeerBudget.reserve_body_preserves_budget bodies allowed.1,
      PeerBudget.step_preserves_budget lanes (.admit .replication allowed.2)⟩
  | submit body charge batch reserve _ _ _ _ _ allowed =>
    have reserved : Headroom.Step limits.volume s.volume (s.volume.reserveBatch reserve) :=
      .reserveBatch reserve allowed
    exact ⟨step_preserves_separate_budgets volume reserved, step_preserves_suffix_limit suffix reserved, bodies, lanes⟩
  | refuseDisk body | rejectOrCancel body =>
    exact ⟨volume, suffix, releaseBody body, releaseLane⟩
  | reconcile body _ _ _ _ _ held bytes entries | synced body _ _ _ _ _ held bytes entries =>
    have after := settle held bytes entries
    exact ⟨after.1, after.2, releaseBody body, releaseLane⟩
  | refuseIngress | timeout | syncFailed | crash =>
    exact ⟨volume, suffix, bodies, lanes⟩

theorem replication_preserves_maintenance_and_control [DecidableEq Payload]
    {limits : Limits} {keeper : KeeperId} {s t : State Payload} {output : Output Payload}
    (step : Step limits keeper s output t) :
    t.lanes.control = s.lanes.control ∧ t.lanes.maintenance = s.lanes.maintenance ∧
      t.volume.control = s.volume.control ∧
      ∀ batch, CanStart limits.volume s.volume batch → CanStart limits.volume t.volume batch := by
  cases step with
  | reconcile body charge write actual | synced body charge write actual =>
    refine ⟨rfl, rfl, rfl, fun batch allowed => ?_⟩
    obtain ⟨idle, scratch, bounded, ⟨control, covered⟩, used, replacement, peak⟩ := allowed
    have usedGrows : s.volume.ordinary.used ≤ (s.finish body write.diskTicket actual).volume.ordinary.used :=
      Nat.le_add_right _ _
    have suffixGrows : s.volume.suffix ≤ (s.finish body write.diskTicket actual).volume.suffix :=
      Nat.le_add_right _ _
    exact ⟨idle, scratch, bounded, ⟨control, Nat.le_trans covered suffixGrows⟩,
      Nat.le_trans used usedGrows, replacement, peak⟩
  | _ => exact ⟨rfl, rfl, rfl, fun _ allowed => allowed⟩

theorem trace_preserves_all_budgets [DecidableEq Payload] {limits : Limits} {keeper : KeeperId}
    {s t : State Payload} (valid : Valid limits s) (trace : Trace limits keeper s t) :
    Valid limits t ∧ t.volume.charged ≤ limits.volume.volume := by
  have preserved : Valid limits t := by
    induction trace with
    | refl => exact valid
    | next _ step prior => exact admission_preserves_budgets prior step
  exact ⟨preserved, physical_bound preserved.1⟩

theorem refused_has_no_evidence [DecidableEq Payload] {limits : Limits} {keeper : KeeperId}
    {s t : State Payload} (refused : Step limits keeper s .backpressure t) :
    Output.evidence (.backpressure : Output Payload) = none ∧
      t.cores = s.cores ∧ t.volume = s.volume := by
  cases refused <;> exact ⟨rfl, rfl, rfl⟩

theorem replication_does_not_commit_or_apply [DecidableEq Payload] {limits : Limits} {keeper : KeeperId}
    {s t : State Payload} {output : Output Payload} (step : Step limits keeper s output t)
    (stream : Installation.StreamId) :
    (t.cores stream).committed = (s.cores stream).committed ∧
      (t.cores stream).applied = (s.cores stream).applied := by
  cases step with
  | synced _ _ write =>
    by_cases same : stream = write.batch.stream
    · subst stream
      simp [State.recordDurable, State.finish, State.release, LeaderJournal.State.replicate]
    · simp [State.recordDurable, State.finish, State.release, update, same]
  | _ => exact ⟨rfl, rfl⟩

theorem timeout_or_sync_failure_keeps_charges [DecidableEq Payload]
    {limits : Limits} {keeper : KeeperId} {s t : State Payload} {output : Output Payload}
    (step : Step limits keeper s output t) (uncertain : output = .unknown ∨ output = .storageFailure) :
    output.evidence = none ∧ t.volume = s.volume ∧ t.bodies = s.bodies ∧ t.lanes = s.lanes := by
  rcases uncertain with rfl | rfl <;> cases step <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem finishing_closes_both_tickets {s : State Payload} {body : Nat} {charge : PeerBudget.BodyCharge}
    {write : Write Payload} {actual : Allocation}
    (bodyHeld : s.bodies[body]? = some (some charge))
    (diskHeld : s.volume.ordinary.tickets[write.diskTicket]? = some (some write.reserved)) :
    let t := s.finish body write.diskTicket actual
    t.writes body = none ∧ t.bodies[body]? = some none ∧
      t.volume.ordinary.tickets[write.diskTicket]? = some none :=
  ⟨by simp [State.finish, State.release, update_same], PeerBudget.closed_body_cannot_release_twice bodyHeld,
    Pool.settling_twice_refused diskHeld⟩

theorem uncertain_write_cannot_ack [DecidableEq Payload] {limits : Limits}
    {s t : State Payload} {keeper body : Nat} {batch : Batch Payload} {write : Write Payload}
    (pending : s.writes body = some write) (uncertain : write.uncertain = true) :
    ¬ Step limits keeper s (.durableAck body batch) t := by
  intro reply
  cases reply with
  | synced body charge found actual bodyHeld alsoPending diskHeld bytes entries waiting accepted =>
    have same := Option.some.inj (alsoPending.symm.trans pending)
    subst found
    rw [uncertain] at waiting
    contradiction

theorem closed_write_cannot_ack_again [DecidableEq Payload] {limits : Limits}
    {s t : State Payload} {keeper body : Nat} {batch : Batch Payload}
    (closed : s.writes body = none) : ¬ Step limits keeper s (.durableAck body batch) t := by
  intro reply
  cases reply with
  | synced body charge write actual bodyHeld pending diskHeld bytes entries waiting accepted =>
    rw [closed] at pending
    contradiction

theorem durable_ack_carries_exact_cut [DecidableEq Payload]
    {limits : Limits} {keeper : KeeperId} {s t : State Payload} {body : Nat} {batch : Batch Payload}
    (reply : Step limits keeper s (.durableAck body batch) t) :
    LeaderJournal.Step (s.cores batch.stream) (t.cores batch.stream) ∧
      batch.cut <+: (t.cores batch.stream).durable keeper ∧
      (t.cores batch.stream).committed = (s.cores batch.stream).committed ∧
      t.writes body = none := by
  cases reply with
  | synced body charge write actual bodyHeld pending diskHeld bytes entries waiting accepted =>
    have replicated : LeaderJournal.Step (s.cores write.batch.stream)
        ((s.cores write.batch.stream).replicate keeper write.batch.cut) :=
      .replicate keeper write.batch.term write.batch.cut accepted.active accepted.term accepted.online accepted.issued
    have covers := replicate_to_covers (s.cores write.batch.stream) (keepers := [keeper])
      (history := write.batch.cut) (keeper := keeper) (by simp)
    refine ⟨by simpa [State.recordDurable, State.finish, State.release] using replicated, ?_, ?_,
      (finishing_closes_both_tickets (actual := actual) bodyHeld diskHeld).1⟩
    · simpa [State.recordDurable, State.finish, State.release, LeaderJournal.State.replicate, LeaderJournal.State.replicateTo, update_same]
        using covers
    · simp [State.recordDurable, State.finish, State.release, LeaderJournal.State.replicate]

theorem ack_leaves_other_streams_unchanged [DecidableEq Payload] {limits : Limits}
    {s t : State Payload} {keeper body : Nat} {batch : Batch Payload}
    (reply : Step limits keeper s (.durableAck body batch) t) {stream : Installation.StreamId}
    (other : stream ≠ batch.stream) : t.cores stream = s.cores stream := by
  cases reply
  simp [State.recordDurable, State.finish, State.release, update, other]

theorem durable_reply_counts_only_as_eligible_voter [DecidableEq Payload] {limits : Limits}
    {s t : State Payload} {keeper body : Nat} {batch : Batch Payload}
    {fleet : Installation.Fleet (Request Payload)}
    (reply : Step limits keeper s (.durableAck body batch) t)
    (coupled : Installation.Coupled fleet batch.stream (t.cores batch.stream))
    (member : (t.cores batch.stream).effectiveConfiguration.contains keeper = true) :
    Installation.CanAcknowledge fleet batch.stream (t.cores batch.stream)
      (t.cores batch.stream).effectiveConfiguration keeper batch.cut := by
  have covers := (durable_ack_carries_exact_cut reply).2.1
  have online : (t.cores batch.stream).online keeper = true := by
    cases reply with
    | synced _ _ _ _ _ _ _ _ _ _ accepted =>
      simpa [State.recordDurable, State.finish, State.release, LeaderJournal.State.replicate] using accepted.online
  let votes : KeeperId → Bool := fun voter => voter == keeper
  exact Installation.checked_commit_ack (votes := votes) coupled
    (fun voter yes => by
      have same : voter = keeper := by simpa [votes] using yes
      exact same.symm ▸ covers)
    (fun voter yes => by
      have same : voter = keeper := by simpa [votes] using yes
      exact same.symm ▸ online)
    (by simp [votes]) member

end Follower

#print axioms Pool.settle_charge
#print axioms Pool.settling_twice_refused
#print axioms trace_preserves_physical_bound
#print axioms failed_publication_keeps_old_basis
#print axioms snapshot_alone_can_exceed_a_wal_only_bound
#print axioms reclaim_then_admit
#print axioms step_preserves_suffix_limit
#print axioms transfers_cannot_consume_maintenance
#print axioms purge_reopens_suffix_while_pinned
#print axioms checked_publish_and_purge
#print axioms Follower.trace_preserves_all_budgets
#print axioms Follower.replication_preserves_maintenance_and_control
#print axioms Follower.refused_has_no_evidence
#print axioms Follower.timeout_or_sync_failure_keeps_charges
#print axioms Follower.durable_reply_counts_only_as_eligible_voter

end Logkeeper.LeaderJournal.Headroom
