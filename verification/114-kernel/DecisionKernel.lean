import Logkeeper.Reducer

set_option warningAsError true

namespace Logkeeper.DecisionKernel

open Kernel (Writer)
open Protocol (ChargeClass Credit)
open Protocol.Ordered (RetainedReceipt retains_receipt replay record_after_apply)
open Kernel.Ordered (Image ImageStep WellFormed)
open Reducer (Limits Owner Principal RequestId Key Cut Checkpoint Record Preparation
  HoldKind Hold Window AppliedOutcome Refusal Receipt Book Holds Leases Roster Checkpoints
  replace leaseOwner pruneLeases ownsHold pruneBook decision_time canVacate vacate fundWindow commitAppend
  registerReferences dropReferences trimCredit commitWithdrawal publishSelection removesOwner
  Related Writes)

structure State where
  placement : Nat
  position : Nat
  time : Nat
  commandHistory : Nat
  voterScope : Nat
  successor : Option Nat
  history : Image Record
  authority : ErasureCommit.Authority Owner
  budget : OrderedBudgets.State
  window : Window
  floor : Cut
  head : Cut
  checkpoints : Checkpoints
  roster : Roster
  lastSerial : Nat
  holds : Holds
  leases : Leases
  objects : ObjectWithdrawal.State Nat Nat
  book : Book

/-- How an ordinary hold is selected. The recovery-root route transfers
custody from a named recovery hold and has its own admission rule. -/
inductive Basis where
  | read
  | writer (grant : Writer) (through : Cut)
  | range (start through : Nat)
  | checkpoint (root start through : Nat)
  | recoveryRoot (source : RequestId)

inductive Release where
  | exact (hold : Hold) (id : RequestId)
  | read (id : RequestId)

inductive Renewal where
  | writer (grant : Writer)
  | read (hold : Hold) (id : RequestId)

inductive Lease where
  | acquire (basis : Basis)
  | release (target : Release)
  | renew (scope : Renewal)

inductive Reconfiguration where
  | enroll (worker : Nat) (expected : Option Owner)
  | withdraw (owner : Owner)
  | transfer (expectedEpoch : Nat) (expected : Option Writer) (owner : Owner)
  | vacate (grant : Writer)
  | seal (expected successor : Nat)
  | rotate (grant : Writer) (checkpoint : Checkpoint)

inductive Publication where
  | prepare (preparation : Preparation) (references : Option (List Nat))
  | select (checkpoint : Checkpoint)
  | close (checkpoint : Checkpoint)

inductive Collection where
  | prefix (selected : Checkpoint) (through : Cut)
  | root (checkpoint : Checkpoint) (disposition erasureFloor : Nat)

inductive Disposition where
  | certified (evidence : Nat)
  | expired

/-- These families have distinct postconditions. In particular the fence map,
funding window and worker custody are not outputs of a mark-and-sweep. -/
inductive Action where
  | append (grant : Writer) (expected : Nat) (lane : ChargeClass)
      (payload bytes : Nat) (references : Option (List Nat))
  | lease (change : Lease)
  | reconfigure (change : Reconfiguration)
  | checkpoint (change : Publication)
  | collect (target : Collection)
  | fund (window : Window)
  | fence (name version : Nat)
  | dispose (owner : Owner) (basis : Disposition)

def Action.isRead : Action → Bool
  | .lease (.acquire .read) => true
  | _ => false

structure Request where
  placement : Nat
  principal : Principal
  id : RequestId
  action : Action
  fingerprint : Nat

def Request.key (r : Request) : Key := (r.principal, r.id)

def projectKernel (s : State) : Kernel.State Record := Kernel.Ordered.abstract_state s.history

def currentReceipt (placement position : Nat) (request : Request) (outcome : Except Refusal AppliedOutcome) :
    Receipt := ⟨placement, request.key, position, outcome⟩

def recordReceipt (placement position : Nat) (request : Request) (outcome : Except Refusal AppliedOutcome)
    (book : Book) : Book :=
  if record_after_apply request.action.isRead outcome then
    replace book request.key (some ⟨request.fingerprint, currentReceipt placement position request outcome⟩)
  else book

def erasurePending (s : State) : Bool := s.checkpoints.preparing.any (·.erasure)

def retainedCut (s : State) (next : Nat) : Option Cut :=
  if next = s.floor.nextLsn then some s.floor
  else if s.floor.nextLsn < next then
    s.history.records[next - s.floor.nextLsn - 1]?.map (·.bytes.cut)
  else none

def checkpointOpen (s : State) (checkpoint : Checkpoint) : Prop :=
  s.checkpoints.erasureFloor ≤ checkpoint.cut.nextLsn ∧
    (checkpoint = s.checkpoints.selected ∨
      s.checkpoints.oldRoots checkpoint.revision = some (checkpoint, false) ∨
      (checkpoint.root = 0 ∧ checkpoint.manifest = 0 ∧ checkpoint.cut.nextLsn = 0 ∧
        checkpoint.revision = 1 ∧
        ∃ id hold, s.holds id = some hold ∧ hold.checkpoint = checkpoint))

def exactRange (s : State) (start through : Cut) : Prop :=
  s.checkpoints.erasureFloor ≤ start.nextLsn ∧ start.nextLsn ≤ through.nextLsn ∧
    retainedCut s start.nextLsn = some start ∧ retainedCut s through.nextLsn = some through

def insertsHold (s : State) (r : Request) (hold : Hold) (after : Holds) : Prop :=
  s.holds r.id = none ∧ hold.origin = r.principal ∧ hold.admittedAt = s.position ∧
    after = replace s.holds r.id (some hold)

def renewsLease (s : State) (limits : Limits) (owner : Owner) (issuedAt leaseEnd : Nat)
    (after : Leases) : Prop :=
  issuedAt = s.time ∧ leaseEnd = s.time + limits.leaseDuration ∧ leaseEnd ≤ limits.maxTime ∧
    after = replace s.leases owner (some (DisposalLease.retained_end (s.leases owner) leaseEnd))

def frame (w : Writes) (before after : State) : Prop :=
  (w.writer = false → after.history = before.history ∧ after.authority = before.authority) ∧
  (w.budget = false → after.budget = before.budget ∧ after.window = before.window) ∧
  (w.head = false → after.head = before.head) ∧
  (w.floor = false → after.floor = before.floor) ∧
  (w.checkpoints = false → after.checkpoints = before.checkpoints) ∧
  (w.roster = false → after.roster = before.roster ∧ after.lastSerial = before.lastSerial) ∧
  (w.holds = false → after.holds = before.holds) ∧
  (w.leases = false → after.leases = before.leases) ∧
  (w.objects = false → after.objects = before.objects) ∧
  (w.cohortSeal = false → after.successor = before.successor) ∧
  after.voterScope = before.voterScope ∧ after.placement = before.placement ∧
  after.position = before.position ∧ after.time = before.time ∧
  after.commandHistory = before.commandHistory

def writerUpdate (s t : State) (incumbentRemoved : Bool) : Prop :=
  if incumbentRemoved then
    t.history = { s.history with active := false } ∧ t.authority = vacate s.authority
  else t.history = s.history ∧ t.authority = s.authority

def successor (s t : State) (writer : Writer) (authority : ErasureCommit.Authority Owner) : Prop :=
  t.history = { s.history with writer, active := true } ∧
  writer.placement = s.history.writer.placement ∧ writer.epoch = s.history.writer.epoch + 1 ∧
  t.authority = authority

def matchesPreparation (p : Preparation) (checkpoint : Checkpoint) : Prop :=
  p.cut = checkpoint.cut ∧ p.root = checkpoint.root ∧ p.revision = checkpoint.revision ∧
  checkpoint.manifest ≠ 0

def appendEffect (limits : Limits) (s t : State) (grant : Writer) (expected : Nat)
    (lane : ChargeClass) (payload bytes : Nat) (references : Option (List Nat)) (cut : Cut) :
    Prop :=
  s.history.active = true ∧ s.history.writer = grant ∧
  Kernel.Ordered.append_next_lsn s.history.head expected
    (min limits.history.recovery limits.history.retained) = some cut.nextLsn ∧
  t.authority = s.authority ∧ t.head = cut ∧ t.window = s.window ∧
  (let charge := OrderedBudgets.recordCharge bytes (references.map List.length)
   t.history = commitAppend s.history grant ⟨payload, cut, ⟨lane, charge⟩, references⟩ cut.nextLsn ∧
   OrderedBudgets.admitsAppend s.budget.budget lane charge s.budget.window
      limits.ordinaryCapacity limits.reserve ∧
   t.budget = { s.budget with budget := OrderedBudgets.appendBudget s.budget.budget lane charge })

def Basis.outcome (basis : Basis) (hold : Hold) : AppliedOutcome :=
  match basis with
  | .read => .barrier hold
  | _ => .protectedHold hold

def admitsHold (s : State) (basis : Basis) (hold : Hold) : Prop :=
  match basis with
  | .read =>
    s.roster hold.owner.1 = some hold.owner ∧ hold.kind = .ordinary ∧
    hold.checkpoint = s.checkpoints.selected ∧ hold.start = s.checkpoints.selected.cut ∧
    hold.through = s.head ∧ exactRange s hold.start hold.through
  | .writer writer through =>
    hold.kind = .ordinary ∧ s.history.active = true ∧ s.history.writer = writer ∧
    s.authority.holder = some hold.owner ∧ hold.checkpoint = s.checkpoints.selected ∧
    hold.start = s.checkpoints.selected.cut ∧ hold.through = through ∧
    exactRange s hold.start hold.through
  | .range start through =>
    s.roster hold.owner.1 = some hold.owner ∧ hold.kind = .ordinary ∧
    hold.checkpoint = s.checkpoints.selected ∧ hold.start.nextLsn = start ∧
    hold.through.nextLsn = through ∧ exactRange s hold.start hold.through
  | .checkpoint root start through =>
    s.roster hold.owner.1 = some hold.owner ∧ hold.kind = .ordinary ∧ hold.checkpoint.root = root ∧
    hold.start = hold.checkpoint.cut ∧ hold.start.nextLsn = start ∧
    hold.through.nextLsn = through ∧ checkpointOpen s hold.checkpoint ∧
    (hold.start = hold.through ∨ exactRange s hold.start hold.through)
  | .recoveryRoot source =>
    hold.kind = .root source ∧
    (∃ recovery, s.holds source = some recovery ∧ recovery.kind = .recovery ∧
      recovery.owner = hold.owner ∧ recovery.checkpoint = hold.checkpoint) ∧
    checkpointOpen s hold.checkpoint ∧
    (∀ id old, s.holds id = some old → old.kind ≠ .root source) ∧
    hold.start = hold.checkpoint.cut ∧ hold.through = hold.start

def dispositionAuthorized (s : State) (r : Request) (limits : Limits)
    (owner : Owner) (basis : Disposition) : Prop :=
  let enrolled := decide (s.roster owner.1 = some owner)
  match basis with
  | .certified evidence =>
    r.principal = .administrator ∧ evidence ≠ 0 ∧
      DisposalLease.withdrawn owner.2 s.lastSerial enrolled = true
  | .expired =>
    DisposalLease.may_dispose (decide (r.principal = .administrator ∨ r.principal = .custodian))
      owner.2 s.lastSerial enrolled s.time (s.leases owner) limits.drift limits.maxTime = true

def effect (limits : Limits) (s : State) (r : Request) (out : AppliedOutcome) (t : State) : Prop :=
  match r.action, out with
  | .append grant expected lane payload bytes references, .appended cut =>
      frame { writer := true, budget := true, head := true, objects := true } s t ∧
      erasurePending s = false ∧
      (∃ owner, s.authority.holder = some owner ∧ r.principal = .worker owner) ∧
      ObjectWithdrawal.canAdmitReferences s.objects references ∧
      appendEffect limits s t grant expected lane payload bytes references cut ∧
      t.objects = registerReferences s.objects references .suffix expected
  | .lease (.acquire basis), _ =>
      ∃ hold, out = basis.outcome hold ∧ frame { holds := true } s t ∧
        r.principal = .worker hold.owner ∧ admitsHold s basis hold ∧ insertsHold s r hold t.holds
  | .lease (.release (.exact hold id)), .released =>
      frame { holds := true, leases := true } s t ∧ r.principal = .worker hold.owner ∧
      s.holds id = some hold ∧ t.holds = replace s.holds id none ∧
      t.leases = pruneLeases s.roster t.holds s.leases
  | .lease (.release (.read id)), .released =>
      frame { holds := true, leases := true } s t ∧ (∃ owner, r.principal = .worker owner) ∧
      (s.holds id = none ∧ t.holds = s.holds ∧ t.leases = s.leases ∨
        (∃ hold entry, s.holds id = some hold ∧ hold.origin = r.principal ∧
          hold.kind = .ordinary ∧ s.book (r.principal, id) = some entry ∧
          entry.original.outcome = .ok (.barrier hold)) ∧
        t.holds = replace s.holds id none ∧ t.leases = pruneLeases s.roster t.holds s.leases)
  | .lease (.renew (.writer grant)), .leased issuedAt leaseEnd =>
      frame { leases := true } s t ∧ s.history.active = true ∧ s.history.writer = grant ∧
      (∃ owner, r.principal = .worker owner ∧ s.authority.holder = some owner ∧
        s.roster owner.1 = some owner ∧ renewsLease s limits owner issuedAt leaseEnd t.leases)
  | .lease (.renew (.read hold id)), .readLeased issuedAt leaseEnd =>
      frame { leases := true } s t ∧ r.principal = .worker hold.owner ∧
      checkpointOpen s hold.checkpoint ∧
      DisposalLease.read_lease_end (s.roster hold.owner.1) (some hold.owner) hold.owner
        (s.holds id) hold
        (DisposalLease.interval_available (hold.start == hold.through) s.floor.nextLsn
          hold.start.nextLsn hold.through.nextLsn s.history.records.length)
        true s.time limits.leaseDuration limits.maxTime = some leaseEnd ∧
      renewsLease s limits hold.owner issuedAt leaseEnd t.leases
  | .reconfigure (.enroll worker expected), .enrolled owner =>
      frame { writer := true, roster := true, leases := true } s t ∧
      r.principal = .administrator ∧ s.roster worker = expected ∧ worker ≠ 0 ∧
      owner = (worker, s.lastSerial + 1) ∧ t.lastSerial = owner.2 ∧
      t.roster = replace s.roster worker (some owner) ∧
      writerUpdate s t (s.authority.holder.any fun incumbent => incumbent.1 == worker) ∧
      t.leases = pruneLeases t.roster s.holds s.leases
  | .reconfigure (.withdraw owner), .withdrawn =>
      frame { writer := true, roster := true, leases := true } s t ∧
      r.principal = .administrator ∧ s.roster owner.1 = some owner ∧
      t.lastSerial = s.lastSerial ∧ t.roster = replace s.roster owner.1 none ∧
      writerUpdate s t (s.authority.holder == some owner) ∧
      t.leases = pruneLeases t.roster s.holds s.leases
  | .reconfigure (.transfer expectedEpoch expected owner), .granted writer recovery =>
      frame { writer := true, holds := true } s t ∧
      (r.principal = .administrator ∨ r.principal = .worker owner) ∧
      s.roster owner.1 = some owner ∧ expectedEpoch = s.history.writer.epoch ∧
      expected = (if s.history.active then some s.history.writer else none) ∧
      erasurePending s = false ∧ recovery.kind = .recovery ∧
      recovery.owner = owner ∧ recovery.checkpoint = s.checkpoints.selected ∧
      recovery.start = s.checkpoints.selected.cut ∧ recovery.through = s.head ∧
      insertsHold s r recovery t.holds ∧
      successor s t writer { s.authority with holder := some owner, epoch := s.authority.epoch + 1 }
  | .reconfigure (.rotate grant checkpoint), .granted writer recovery =>
      frame { writer := true, holds := true, checkpoints := true, objects := true } s t ∧
      r.principal = .custodian ∧ s.history.active = true ∧ s.history.writer = grant ∧
      checkpoint.cut = s.head ∧ checkpoint ≠ s.checkpoints.selected ∧
      (∃ p, s.checkpoints.preparing = some p ∧ p.erasure = true ∧ p.source = grant ∧
        p.base = s.checkpoints.selected ∧ matchesPreparation p checkpoint) ∧
      recovery.kind = .recovery ∧ some recovery.owner = s.authority.holder ∧
      recovery.checkpoint = checkpoint ∧ recovery.start = checkpoint.cut ∧
      recovery.through = s.head ∧ insertsHold s r recovery t.holds ∧
      successor s t writer (ErasureCommit.rotate s.authority) ∧
      t.checkpoints = publishSelection s.checkpoints checkpoint true ∧
      dropReferences s.objects t.objects (fun _ _ => True)
  | .reconfigure (.vacate grant), .vacated =>
      frame { writer := true } s t ∧
      canVacate s.history (erasurePending s)
        (match r.principal with | .worker owner => some owner | _ => none) s.authority.holder grant ∧
      t.history = { s.history with active := false } ∧ t.authority = vacate s.authority
  | .reconfigure (.seal expected successor), .cohortSealed result =>
      frame { cohortSeal := true } s t ∧ r.principal = .administrator ∧ successor = result ∧
      expected = s.voterScope ∧ successor ≠ 0 ∧ successor ≠ expected ∧ t.successor = some successor
  | .checkpoint (.prepare pending references), .checkpointPrepared result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ pending = result ∧
      (s.checkpoints.preparing = some pending ∧ t.checkpoints = s.checkpoints ∧ t.objects = s.objects ∨
        s.checkpoints.preparing = none ∧ s.checkpoints.selected.cut.nextLsn < pending.cut.nextLsn ∧
        pending.revision = s.checkpoints.selected.revision + 1 ∧ pending.root ≠ 0 ∧
        retainedCut s pending.cut.nextLsn = some pending.cut ∧ checkpointOpen s pending.base ∧
        (pending.erasure = true → s.history.active = true ∧ pending.source = s.history.writer ∧
          pending.base = s.checkpoints.selected ∧ pending.cut = s.head) ∧
        ObjectWithdrawal.canAdmitReferences s.objects references ∧
        t.checkpoints = { s.checkpoints with preparing := some pending } ∧
        t.objects = registerReferences s.objects references .root pending.revision)
  | .checkpoint (.close checkpoint), .checkpointClosed result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ checkpoint = result ∧
      (∃ closed, s.checkpoints.oldRoots checkpoint.revision = some (checkpoint, closed)) ∧
      (∀ id hold, s.holds id = some hold → hold.checkpoint ≠ checkpoint) ∧
      (∀ p, s.checkpoints.preparing = some p → p.base ≠ checkpoint) ∧
      t.checkpoints = { s.checkpoints with
        oldRoots := replace s.checkpoints.oldRoots checkpoint.revision (some (checkpoint, true)) } ∧
      dropReferences s.objects t.objects (fun _ _ => True)
  | .checkpoint (.select checkpoint), .published result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ checkpoint = result ∧
      (checkpoint = s.checkpoints.selected ∧ t.checkpoints = s.checkpoints ∧ t.objects = s.objects ∨
       (∃ p, s.checkpoints.preparing = some p ∧ p.erasure = false ∧ matchesPreparation p checkpoint) ∧
        retainedCut s checkpoint.cut.nextLsn = some checkpoint.cut ∧
        t.checkpoints = publishSelection s.checkpoints checkpoint false ∧
        dropReferences s.objects t.objects (fun _ _ => True))
  | .collect (.root checkpoint disposition floor), .checkpointSettled result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ checkpoint = result ∧
      floor = s.checkpoints.erasureFloor ∧ disposition ≠ 0 ∧
      s.checkpoints.oldRoots checkpoint.revision = some (checkpoint, true) ∧
      (∀ id hold, s.holds id = some hold → hold.checkpoint ≠ checkpoint) ∧
      (∀ p, s.checkpoints.preparing = some p → p.base ≠ checkpoint) ∧
      t.checkpoints = { s.checkpoints with
        oldRoots := replace s.checkpoints.oldRoots checkpoint.revision none } ∧
      dropReferences s.objects t.objects (fun role id => role ≠ .root ∨ id ≠ checkpoint.revision)
  | .collect (.prefix selected through), .trimmed cut credit =>
      frame { writer := true, budget := true, floor := true, objects := true } s t ∧
      r.principal = .custodian ∧ selected = s.checkpoints.selected ∧ through = cut ∧
      s.floor.nextLsn ≤ cut.nextLsn ∧ cut.nextLsn ≤ selected.cut.nextLsn ∧
      retainedCut s cut.nextLsn = some cut ∧
      (∀ id hold, s.holds id = some hold → hold.start.nextLsn < hold.through.nextLsn →
        cut.nextLsn ≤ hold.start.nextLsn) ∧
      t.floor = cut ∧ t.window = s.window ∧ t.authority = s.authority ∧
      t.history = Kernel.Ordered.trimImage s.history (cut.nextLsn - s.floor.nextLsn) ∧
      credit = trimCredit s.history (cut.nextLsn - s.floor.nextLsn) ∧
      credit.ordinary ≤ s.budget.budget.ordinary ∧ credit.maintenance ≤ s.budget.budget.maintenance ∧
      t.budget = { s.budget with budget := OrderedBudgets.trimBudget s.budget.budget credit } ∧
      dropReferences s.objects t.objects (fun role id => role ≠ .suffix ∨ cut.nextLsn ≤ id)
  | .fund window, .windowFunded result =>
      frame { budget := true } s t ∧ r.principal = .custodian ∧ window = result ∧
      window.allocation ≠ 0 ∧ window.bytes ≠ 0 ∧ window.serial = s.window.serial + 1 ∧
      OrderedBudgets.admitsDebit s.budget.budget.ordinary window.bytes limits.ordinaryCapacity ∧
      t.budget = fundWindow s.budget.budget window.bytes ∧ t.window = window
  | .fence name version, .objectWithdrawn chosenName chosenVersion =>
      frame { objects := true } s t ∧ r.principal = .custodian ∧ name = chosenName ∧ version = chosenVersion ∧
      (s.objects.fence name = some version ∧ t.objects = s.objects ∨
        ObjectWithdrawal.canWithdraw s.objects name ∧ ¬ ObjectWithdrawal.fenced s.objects name ∧
        t.objects = commitWithdrawal s.objects name version)
  | .dispose owner basis, .workerDisposed result =>
      frame { holds := true, leases := true } s t ∧ owner = result ∧
      dispositionAuthorized s r limits owner basis ∧
      t.holds = removesOwner s.holds owner ∧ t.leases = pruneLeases s.roster t.holds s.leases
  | _, _ => False

def retainsThrough (s : State) (r : Request) (out : AppliedOutcome) (t : State) : Prop :=
  ∀ id hold, t.holds id = some hold →
    s.holds id = some hold ∨
      id = r.id ∧ hold.origin = r.principal ∧ hold.admittedAt = s.position ∧
        (out = .barrier hold ∨ out = .protectedHold hold ∨ ∃ grant, out = .granted grant hold)

def leaseRows (limits : Limits) (s t : State) : Prop :=
  ∀ owner endTime, t.leases owner = some endTime →
    leaseOwner t.roster t.holds owner ∧
      (s.leases owner = some endTime ∨ endTime = s.time + limits.leaseDuration)

/-- A command may change a concern only through its checked transition.
The cross-concern fields in effect pin the writer cut, budget, and receipt
to the same outcome. Projection witnesses are obligations on an implementer
of this relation. -/
structure Applied (limits : Limits) (s : State) (r : Request) (out : AppliedOutcome) (t : State) :
    Prop where
  commandEffect : effect limits s r out t
  history : ImageStep limits.history s.history t.history
  authority : ErasureCommit.Step s.authority t.authority
  budget : Related (OrderedBudgets.Step limits.ordinaryCapacity limits.reserve) s.budget t.budget
  objects : Related ObjectWithdrawal.Step s.objects t.objects
  holds : retainsThrough s r out t
  leases : leaseRows limits s t
  time : t.time = s.time
  position : t.position = s.position
  rotationIncumbent : s.authority.generation < t.authority.generation → 0 < s.authority.epoch

def earlyRefusal (s : State) (r : Request) : Option Refusal :=
  if r.placement ≠ s.placement then some .wrongPlacement
  else if r.id.nonce = 0 then some .invalid else none

def lateRefusal (limits : Limits) (s : State) (r : Request) : Option Refusal :=
  if r.id.expiresAt ≤ s.position then some .expired
  else if s.successor.isSome then some .cohortSealed
  else if limits.retryPositions < r.id.expiresAt - s.position then some .invalid
  else none

def fresh (limits : Limits) (s : State) (r : Request) : Prop :=
  earlyRefusal s r = none ∧ s.book r.key = none ∧ lateRefusal limits s r = none

def cachedReceipt (s : State) (r : Request) (retained : RetainedReceipt Nat Receipt) : Receipt :=
  (replay r.action.isRead retained.fingerprint r.fingerprint retained.original).getD
    (currentReceipt s.placement s.position r (.error .conflict))

/-- An admitted request may be refused by additional concrete checks.
Expiration and replay happen before dispatch. Release and disposal prune the
receipt of an expired hold when they remove that hold. -/
inductive RequestStep (limits : Limits) (r : Request) (s : State) : Receipt → State → Prop
  | early (refusal) (rejected : earlyRefusal s r = some refusal) :
      RequestStep limits r s (currentReceipt s.placement s.position r (.error refusal)) s
  | cached (retained) (placed : earlyRefusal s r = none) (found : s.book r.key = some retained) :
      RequestStep limits r s (cachedReceipt s r retained) s
  | late (refusal) (placed : earlyRefusal s r = none) (unused : s.book r.key = none)
      (rejected : lateRefusal limits s r = some refusal) :
      RequestStep limits r s (currentReceipt s.placement s.position r (.error refusal)) s
  | refused (refusal) (admitted : fresh limits s r) :
      RequestStep limits r s (currentReceipt s.placement s.position r (.error refusal))
        { s with book := recordReceipt s.placement s.position r (.error refusal) s.book }
  | applied {t out} (admitted : fresh limits s r) (effects : Applied limits s r out t) :
      RequestStep limits r s (currentReceipt s.placement s.position r (.ok out))
        { t with book := recordReceipt s.placement s.position r (.ok out) (pruneBook s.position t.holds s.book) }

open Reducer (ApplyError)

def applyError (limits : Limits) (s : State) (position time : Nat) : Option ApplyError :=
  if s.position + 1 ≠ position ∨ limits.maxTime < position then some .position
  else if decision_time s.time time = none ∨ limits.maxTime < time then some .time
  else none

def advance (limits : Limits) (s : State) (position time : Nat) (r : Request) : State :=
  { s with position, time, book := pruneBook position s.holds s.book,
           commandHistory := limits.extendCommandHistory s.commandHistory position time r.fingerprint }

inductive Step (limits : Limits) (position time : Nat) (request : Request) (before : State) :
    Except ApplyError Receipt → State → Prop
  | rejected (error) (invalid : applyError limits before position time = some error) :
      Step limits position time request before (.error error) before
  | chosen {receipt after} (valid : applyError limits before position time = none)
      (requestStep : RequestStep limits request (advance limits before position time request) receipt after) :
      Step limits position time request before (.ok receipt) after

def HoldReceipts (s : State) : Prop :=
  ∀ id hold, s.holds id = some hold → ∃ entry,
    s.book (hold.origin, id) = some entry ∧
      CompactImage.holdReceiptMatches hold.admittedAt (some entry.original.position) ∧
      (entry.original.outcome = .ok (.barrier hold) ∨
        entry.original.outcome = .ok (.protectedHold hold) ∨
        ∃ grant, entry.original.outcome = .ok (.granted grant hold))

def LeaseBounds (limits : Limits) (s : State) : Prop :=
  ∀ owner endTime, s.leases owner = some endTime →
    leaseOwner s.roster s.holds owner ∧
      limits.leaseDuration ≤ endTime ∧ endTime ≤ s.time + limits.leaseDuration

structure Inv (limits : Limits) (s : State) : Prop where
  image : WellFormed s.history
  kernel : Kernel.Valid limits.history (projectKernel s)
  budget : OrderedBudgets.fundedBudget s.budget.budget s.budget.window limits.ordinaryCapacity limits.reserve
  generation : CompactImage.generationInRange s.authority.epoch s.authority.generation
  references : ObjectWithdrawal.Safe s.objects
  holds : HoldReceipts s
  leases : LeaseBounds limits s

private theorem keep_held_receipt {holds : Holds} {book : Book} {position : Nat}
    {id : RequestId} {hold : Hold} (held : holds id = some hold) :
    pruneBook position holds book (hold.origin, id) = book (hold.origin, id) := by
  simp [pruneBook, ownsHold, held, retains_receipt]

private theorem record_other {placement position : Nat} {request : Request}
    {out : Except Refusal AppliedOutcome} {book : Book} {key : Key} (other : key ≠ request.key) :
    recordReceipt placement position request out book key = book key := by
  unfold recordReceipt
  split
  · simp [replace, other]
  · rfl

private theorem checked_time {limits : Limits} {s : State} {position time : Nat}
    (valid : applyError limits s position time = none) : s.time ≤ time := by
  by_cases ordered : s.time ≤ time
  · exact ordered
  · unfold applyError at valid
    split at valid
    · contradiction
    · simp [decision_time, DisposalLease.decision_time, ordered] at valid

theorem request_step_projects {limits r s receipt t}
    (step : RequestStep limits r s receipt t) :
    ImageStep limits.history s.history t.history ∧
      ErasureCommit.Step s.authority t.authority ∧
      Related (OrderedBudgets.Step limits.ordinaryCapacity limits.reserve) s.budget t.budget ∧
      Related ObjectWithdrawal.Step s.objects t.objects ∧ t.time = s.time := by
  cases step with
  | applied _ effects => exact ⟨effects.history, effects.authority, effects.budget, effects.objects, effects.time⟩
  | _ => exact ⟨.stutter _, .stutter _, Or.inl rfl, Or.inl rfl, rfl⟩

private theorem request_step_holds {limits r s receipt t}
    (inv : HoldReceipts s) (step : RequestStep limits r s receipt t) : HoldReceipts t := by
  cases step with
  | refused refusal admitted =>
    intro id hold held
    obtain ⟨entry, found, atPosition, positive⟩ := inv id hold held
    have distinct : (hold.origin, id) ≠ r.key := by
      intro equal
      rw [equal, admitted.2.1] at found
      contradiction
    refine ⟨entry, ?_, atPosition, positive⟩
    change recordReceipt s.placement s.position r (.error refusal) s.book (hold.origin, id) = some entry
    rw [record_other distinct, found]
  | @applied t out admitted effects =>
    intro id hold held
    rcases effects.holds id hold held with old | ⟨rfl, origin, position, issued⟩
    · obtain ⟨entry, found, atPosition, positive⟩ := inv id hold old
      have distinct : (hold.origin, id) ≠ r.key := by
        intro equal
        rw [equal, admitted.2.1] at found
        contradiction
      change t.holds id = some hold at held
      have keep := keep_held_receipt (book := s.book) (position := s.position) held
      refine ⟨entry, ?_, atPosition, positive⟩
      change recordReceipt s.placement s.position r (.ok out) (pruneBook s.position t.holds s.book)
        (hold.origin, id) = some entry
      rw [record_other distinct, keep, found]
    · have recorded : record_after_apply r.action.isRead (.ok out : Except Refusal AppliedOutcome) = true := by
        simp [record_after_apply]
      refine ⟨⟨r.fingerprint, currentReceipt s.placement s.position r (.ok out)⟩, ?_, ?_, ?_⟩
      · simp [recordReceipt, recorded, replace, origin, Request.key]
      · simp [CompactImage.holdReceiptMatches, currentReceipt, position]
      · simpa [currentReceipt] using issued
  | _ => exact inv

private theorem request_step_leases {limits r s receipt t}
    (inv : LeaseBounds limits s) (step : RequestStep limits r s receipt t) : LeaseBounds limits t := by
  cases step with
  | @applied t _ _ effects =>
    intro owner endTime found
    obtain ⟨retained, earlier | renewed⟩ := effects.leases owner endTime found
    · have prior := inv owner endTime earlier
      exact ⟨retained, prior.2.1, by simpa only [effects.time] using prior.2.2⟩
    · refine ⟨retained, by omega, ?_⟩
      change endTime ≤ t.time + limits.leaseDuration
      rw [effects.time, renewed]
      exact Nat.le_refl _
  | _ => exact inv

theorem step_projects {limits position time request s out t}
    (step : Step limits position time request s out t) :
    ImageStep limits.history s.history t.history ∧
      ErasureCommit.Step s.authority t.authority ∧
      Related (OrderedBudgets.Step limits.ordinaryCapacity limits.reserve) s.budget t.budget ∧
      Related ObjectWithdrawal.Step s.objects t.objects ∧ s.time ≤ t.time := by
  cases step with
  | rejected => exact ⟨.stutter _, .stutter _, Or.inl rfl, Or.inl rfl, Nat.le_refl _⟩
  | chosen valid req =>
    have ⟨hist, authority, budget, objects, endTime⟩ := request_step_projects req
    exact ⟨hist, authority, budget, objects,
      by rw [endTime]; exact checked_time valid⟩

theorem step_projects_kernel {limits position time request s out t}
    (wellFormed : WellFormed s.history) (step : Step limits position time request s out t) :
    Related (Kernel.Step limits.history) (projectKernel s) (projectKernel t) := by
  have projection := (Kernel.Ordered.image_step_refines_kernel wellFormed (step_projects step).1).2
  exact projection.elim (fun same => Or.inl same.symm) Or.inr

private theorem valid_generation_preserved {s t : ErasureCommit.Authority Owner}
    (inv : CompactImage.generationInRange s.epoch s.generation)
    (step : ErasureCommit.Step s t)
    (rotationIncumbent : s.generation < t.generation → 0 < s.epoch) :
    CompactImage.generationInRange t.epoch t.generation := by
  cases step with
  | rotate =>
    have lower : 1 ≤ s.epoch := rotationIncumbent (by simp [ErasureCommit.rotate])
    simp [CompactImage.generationInRange, ErasureCommit.rotate, Nat.max_eq_right lower] at *
    omega
  | grant =>
    simp [CompactImage.generationInRange] at *
    omega
  | vacate => exact inv
  | stutter => exact inv

private theorem step_generation {limits position time request s out t}
    (inv : Inv limits s) (step : Step limits position time request s out t) :
    CompactImage.generationInRange t.authority.epoch t.authority.generation := by
  cases step with
  | rejected => exact inv.generation
  | chosen _ requestStep =>
    cases requestStep with
    | applied _ effects =>
      exact valid_generation_preserved inv.generation effects.authority effects.rotationIncumbent
    | _ => exact inv.generation

theorem step_preserves_inv {limits position time request s out t}
    (inv : Inv limits s) (step : Step limits position time request s out t) :
    Inv limits t := by
  obtain ⟨history, _, budget, references, _⟩ := step_projects step
  refine ⟨(Kernel.Ordered.image_step_refines_kernel inv.image history).1, ?_, ?_,
    step_generation inv step, ?_, ?_, ?_⟩
  · rcases step_projects_kernel inv.image step with same | kernel
    · rw [← same]
      exact inv.kernel
    · exact Kernel.step_preserves_valid inv.kernel kernel
  · rcases budget with same | budget
    · rw [← same]
      exact inv.budget
    · exact OrderedBudgets.trace_preserves_funding inv.budget (.next (.empty _) budget)
  · rcases references with same | references
    · rw [← same]
      exact inv.references
    · exact ObjectWithdrawal.order_preserves_separation inv.references references
  · cases step with
    | rejected => exact inv.holds
    | chosen _ req =>
      apply request_step_holds _ req
      intro id hold held
      obtain ⟨entry, found, atPosition, positive⟩ := inv.holds id hold held
      change s.holds id = some hold at held
      refine ⟨entry, ?_, atPosition, positive⟩
      change pruneBook position s.holds s.book (hold.origin, id) = some entry
      rw [keep_held_receipt held, found]
  · cases step with
    | rejected => exact inv.leases
    | chosen valid req =>
      have observed := checked_time valid
      apply request_step_leases _ req
      intro owner endTime found
      obtain ⟨ownerKept, lower, upper⟩ := inv.leases owner endTime found
      exact ⟨ownerKept, lower, by change endTime ≤ time + limits.leaseDuration; omega⟩

inductive Trace (limits : Limits) : State → State → Prop
  | same (s : State) : Trace limits s s
  | next {s m t position time request out} (prior : Trace limits s m)
      (step : Step limits position time request m out t) : Trace limits s t

theorem trace_preserves_inv {limits s t} (inv : Inv limits s) (trace : Trace limits s t) :
    Inv limits t := by
  induction trace with
  | same => exact inv
  | next _ step earlier => exact step_preserves_inv earlier step

theorem trace_projects_history {limits s t} (trace : Trace limits s t) :
    Kernel.Ordered.ImageTrace limits.history s.history t.history := by
  induction trace with
  | same => exact .same _
  | next _ step earlier => exact .step earlier (step_projects step).1

theorem trace_projects_authority {limits s t} (trace : Trace limits s t) :
    ErasureCommit.Trace s.authority t.authority := by
  induction trace with
  | same => exact .refl _
  | next _ step earlier => exact .extend earlier (step_projects step).2.1

theorem trace_projects_budget {limits s t} (trace : Trace limits s t) :
    OrderedBudgets.Trace limits.ordinaryCapacity limits.reserve s.budget t.budget := by
  induction trace with
  | same => exact .empty _
  | next _ step earlier =>
    rcases (step_projects step).2.2.1 with same | next
    · exact same ▸ earlier
    · exact .next earlier next

theorem trace_projects_objects {limits s t} (trace : Trace limits s t) :
    ObjectWithdrawal.Trace s.objects t.objects := by
  induction trace with
  | same => exact .empty _
  | next _ step earlier =>
    rcases (step_projects step).2.2.2.1 with same | next
    · exact same ▸ earlier
    · exact .next earlier next

theorem trace_preserves_fence {limits s t name version} (trace : Trace limits s t)
    (fenced : s.objects.fence name = some version) : t.objects.fence name = some version :=
  ObjectWithdrawal.trace_preserves_fence (trace_projects_objects trace) fenced

theorem trace_preserves_history {limits s t} (inv : Inv limits s) (trace : Trace limits s t)
    {lsn : Nat} (committed : lsn < (projectKernel s).history.length) :
    (projectKernel t).history[lsn]? = (projectKernel s).history[lsn]? :=
  Kernel.Ordered.history_is_irrevocable inv.image (trace_projects_history trace) committed

theorem a_cached_barrier_refuses {s : State} {r : Request}
    (reading : r.action.isRead = true) (retained : RetainedReceipt Nat Receipt) :
    cachedReceipt s r retained = currentReceipt s.placement s.position r (.error .conflict) := by
  unfold cachedReceipt
  rw [reading, Protocol.Ordered.barriers_never_replay]
  rfl

theorem a_refused_barrier_leaves_no_receipt (placement position : Nat) (r : Request)
    (reading : r.action.isRead = true) (refusal : Refusal) (book : Book) :
    recordReceipt placement position r (.error refusal) book = book := by
  simp [recordReceipt, record_after_apply, reading]

end Logkeeper.DecisionKernel
