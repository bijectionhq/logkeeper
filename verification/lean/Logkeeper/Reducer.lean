import Logkeeper.OrderedWriter
import Logkeeper.OrderedBudgets
import Logkeeper.OrderedReceipt
import Logkeeper.LeaseReducer
import Logkeeper.ErasureCommit
import Logkeeper.ObjectWithdrawal
import Logkeeper.CompactImage

set_option warningAsError true

namespace Logkeeper.Reducer

open Kernel (Writer)
open Protocol (ChargeClass Credit)
open Protocol.Ordered (RetainedReceipt retains_receipt replay record_after_apply)
open Kernel.Ordered (Image ImageStep WellFormed)

structure Limits where
  history : Kernel.Limits
  ordinaryCapacity : Nat
  reserve : Nat
  retryPositions : Nat
  leaseDuration : Nat
  drift : Nat
  maxTime : Nat
  extendCommandHistory : Nat → Nat → Nat → Nat → Nat

/-- An enrollment retains both the worker identity and its issuance serial. -/
abbrev Owner := Nat × Nat

inductive Principal where
  | administrator | custodian | worker (owner : Owner) | routeReader
  deriving DecidableEq

structure RequestId where
  nonce : Nat
  expiresAt : Nat
  deriving DecidableEq

abbrev Key := Principal × RequestId

structure Cut where
  nextLsn : Nat
  digest : Nat
  deriving DecidableEq

structure Checkpoint where
  cut : Cut
  root : Nat
  revision : Nat
  manifest : Nat
  deriving DecidableEq

structure Record where
  identity : Nat
  cut : Cut
  debit : Protocol.Debit
  references : Option (List Nat)

structure Preparation where
  cut : Cut
  root : Nat
  revision : Nat
  source : Writer
  base : Checkpoint
  erasure : Bool
  deriving DecidableEq

inductive HoldKind where
  | ordinary | recovery | root (source : RequestId)
  deriving DecidableEq

structure Hold where
  owner : Owner
  admittedAt : Nat
  checkpoint : Checkpoint
  start : Cut
  through : Cut
  origin : Principal
  kind : HoldKind
  deriving DecidableEq

structure Window where
  allocation : Nat
  serial : Nat
  bytes : Nat
  deriving DecidableEq

inductive Command where
  | enroll (worker : Nat) (expected : Option Owner)
  | withdraw (owner : Owner)
  | grant (expectedEpoch : Nat) (expected : Option Writer) (candidate : Owner)
  | publishAndRotate (grant : Writer) (checkpoint : Checkpoint)
  | append (grant : Writer) (expected : Nat) (lane : ChargeClass)
      (payload : Nat) (bytes : Nat) (references : Option (List Nat))
  | barrier
  | prepareCheckpoint (preparation : Preparation) (references : Option (List Nat))
  | withdrawObject (name version : Nat)
  | closeCheckpoint (checkpoint : Checkpoint)
  | settleCheckpoint (checkpoint : Checkpoint) (disposition erasureFloor : Nat)
  | disposeWorker (owner : Owner) (disposition : Nat)
  | publish (checkpoint : Checkpoint)
  | fundWindow (window : Window)
  | protect (grant : Writer) (through : Cut)
  | protectRange (start through : Nat)
  | protectCheckpoint (root start through : Nat)
  | protectRoot (source : RequestId)
  | vacate (grant : Writer)
  | sealCohort (expected successor : Nat)
  | release (hold : Hold) (id : RequestId)
  | releaseRead (id : RequestId)
  | lease (grant : Writer)
  | leaseRead (hold : Hold) (id : RequestId)
  | disposeExpired (owner : Owner)
  | trim (selected : Checkpoint) (through : Cut)

def Command.isBarrier : Command → Bool
  | .barrier => true
  | _ => false

structure Request where
  placement : Nat
  principal : Principal
  id : RequestId
  command : Command
  fingerprint : Nat

def Request.key (r : Request) : Key := (r.principal, r.id)

inductive AppliedOutcome where
  | enrolled (owner : Owner)
  | withdrawn
  | granted (grant : Writer) (recovery : Hold)
  | appended (cut : Cut)
  | barrier (hold : Hold)
  | checkpointPrepared (preparation : Preparation)
  | objectWithdrawn (name version : Nat)
  | checkpointClosed (checkpoint : Checkpoint)
  | checkpointSettled (checkpoint : Checkpoint)
  | workerDisposed (owner : Owner)
  | published (checkpoint : Checkpoint)
  | windowFunded (window : Window)
  | protectedHold (hold : Hold)
  | vacated
  | cohortSealed (successor : Nat)
  | released
  | leased (issuedAt leaseEnd : Nat)
  | readLeased (issuedAt leaseEnd : Nat)
  | trimmed (through : Cut) (credit : Credit)

inductive Refusal where
  | wrongPlacement | invalid | conflict | expired | cohortSealed
  | unauthorized | stale | unavailable | capacity

structure Receipt where
  placement : Nat
  key : Key
  position : Nat
  outcome : Except Refusal AppliedOutcome

abbrev Book := Key → Option (RetainedReceipt Nat Receipt)
abbrev Holds := RequestId → Option Hold
abbrev Leases := Owner → Option Nat
abbrev Roster := Nat → Option Owner

structure Checkpoints where
  selected : Checkpoint
  preparing : Option Preparation
  oldRoots : Nat → Option (Checkpoint × Bool)
  erasureFloor : Nat

/-- History includes the archived prefix and last writer from the trace.
Object registrations keep the same identity when a preparation is published. -/
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

def replace [DecidableEq K] (entries : K → Option V) (key : K) (value : Option V) : K → Option V :=
  fun query => if query = key then value else entries query

def projectKernel (s : State) : Kernel.State Record := Kernel.Ordered.abstract_state s.history

def leaseOwner (roster : Roster) (holds : Holds) (owner : Owner) : Prop :=
  roster owner.1 = some owner ∨ ∃ id hold, holds id = some hold ∧ hold.owner = owner

noncomputable def pruneLeases (roster : Roster) (holds : Holds) (leases : Leases) : Leases := by
  classical
  exact fun owner => if leaseOwner roster holds owner then leases owner else none

def ownsHold (holds : Holds) (key : Key) : Bool :=
  match holds key.2 with
  | some hold => decide (hold.origin = key.1)
  | none => false

def pruneBook (position : Nat) (holds : Holds) (book : Book) : Book :=
  fun key => if retains_receipt position key.2.expiresAt (ownsHold holds key)
    then book key else none

def currentReceipt (placement position : Nat) (request : Request) (outcome : Except Refusal AppliedOutcome) :
    Receipt := ⟨placement, request.key, position, outcome⟩

def recordReceipt (placement position : Nat) (request : Request) (outcome : Except Refusal AppliedOutcome)
    (book : Book) : Book :=
  if record_after_apply request.command.isBarrier outcome then
    replace book request.key (some ⟨request.fingerprint, currentReceipt placement position request outcome⟩)
  else book

def decision_time (before incoming : Nat) : Option Nat :=
  DisposalLease.decision_time before incoming

def canVacate (history : Image Record) (erasurePending : Bool)
    (principal current : Option Owner) (presented : Writer) : Prop :=
  principal = current ∧ current.isSome ∧ history.active = true ∧
    history.writer = presented ∧ erasurePending = false

def erasurePending (s : State) : Bool := s.checkpoints.preparing.any (·.erasure)

def vacate (authority : ErasureCommit.Authority Owner) : ErasureCommit.Authority Owner :=
  ErasureCommit.vacate authority

def fundWindow (budget : OrderedBudgets.Budget) (window : Nat) : OrderedBudgets.State :=
  ⟨{ budget with spent := 0 }, window⟩

def commitAppend (history : Image Record) (grant : Writer) (record : Record) (next : Nat) :
    Image Record :=
  { history with records := history.records ++ [⟨grant.epoch, record⟩], head := next }

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

def registerReferences (s : ObjectWithdrawal.State Nat Nat) (names : Option (List Nat))
    (role : ObjectWithdrawal.Role) (owner : Nat) : ObjectWithdrawal.State Nat Nat :=
  match names with
  | none => { s with hasOpaqueReferences := True }
  | some names => { s with references := fun n r o =>
      (n ∈ names ∧ r = role ∧ o = owner) ∨ s.references n r o }

def dropReferences (s t : ObjectWithdrawal.State Nat Nat)
    (keep : ObjectWithdrawal.Role → Nat → Prop) : Prop :=
  ∃ unknown : Prop, (unknown → s.hasOpaqueReferences) ∧ t =
    { s with references := fun name role id => s.references name role id ∧ keep role id,
             hasOpaqueReferences := unknown }

def trimCredit (image : Image Record) (count : Nat) : Credit :=
  ((image.records.take count).map (·.bytes.debit)).foldl Protocol.Credit.addDebit ⟨0, 0⟩

theorem trim_credit_matches_protocol (image : Image Record) (count : Nat)
    (receiptFor : Record → Protocol.AppendReceipt) :
    Protocol.trimCredit
      (image.records.map fun row => .append ⟨receiptFor row.bytes, row.bytes.debit⟩) 0 count =
      trimCredit image count := by
  simp only [Protocol.trimCredit, Protocol.application, trimCredit, List.drop_zero, Nat.sub_zero,
    List.filterMap_map, Function.comp_def, List.filterMap_eq_map', ← List.map_take, List.foldl_map]

def commitWithdrawal (s : ObjectWithdrawal.State Nat Nat) (name version : Nat) :
    ObjectWithdrawal.State Nat Nat :=
  { s with fence := replace s.fence name (some version) }

theorem commit_withdrawal_projects (s : ObjectWithdrawal.State Nat Nat) (name version : Nat)
    (available : ObjectWithdrawal.canWithdraw s name) (fresh : ¬ ObjectWithdrawal.fenced s name) :
    ObjectWithdrawal.Step s (commitWithdrawal s name version) :=
  .withdraw s name version available fresh

def publishSelection (s : Checkpoints) (next : Checkpoint) (rotate : Bool) : Checkpoints :=
  { selected := next, preparing := none,
    oldRoots := fun revision =>
      if revision = s.selected.revision ∧ s.selected.manifest ≠ 0 then some (s.selected, rotate)
      else (s.oldRoots revision).map fun (root, closed) => (root, closed || rotate),
    erasureFloor := ErasureCommit.erasure_floor s.erasureFloor next.cut.nextLsn rotate }

def removesOwner (holds : Holds) (owner : Owner) : Holds :=
  fun id => (holds id).filter (·.owner != owner)

def insertsHold (s : State) (r : Request) (hold : Hold) (after : Holds) : Prop :=
  s.holds r.id = none ∧ hold.origin = r.principal ∧ hold.admittedAt = s.position ∧
    after = replace s.holds r.id (some hold)

def renewsLease (s : State) (limits : Limits) (owner : Owner) (issuedAt leaseEnd : Nat)
    (after : Leases) : Prop :=
  issuedAt = s.time ∧ leaseEnd = s.time + limits.leaseDuration ∧ leaseEnd ≤ limits.maxTime ∧
    after = replace s.leases owner (some (DisposalLease.retained_end (s.leases owner) leaseEnd))

def Related (rel : α → α → Prop) (a b : α) : Prop := a = b ∨ rel a b

structure Writes where
  writer : Bool := false
  budget : Bool := false
  head : Bool := false
  floor : Bool := false
  checkpoints : Bool := false
  roster : Bool := false
  holds : Bool := false
  leases : Bool := false
  objects : Bool := false
  cohortSeal : Bool := false

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

/-- Successful transitions pair a command with its outcome and frame the other
fields. Authentication and provider assertions enter as opaque identities. -/
def effect (limits : Limits) (s : State) (r : Request) (out : AppliedOutcome) (t : State) : Prop :=
  match r.command, out with
  | .enroll worker expected, .enrolled owner =>
      frame { writer := true, roster := true, leases := true } s t ∧
      r.principal = .administrator ∧ s.roster worker = expected ∧ worker ≠ 0 ∧
      owner = (worker, s.lastSerial + 1) ∧ t.lastSerial = owner.2 ∧
      t.roster = replace s.roster worker (some owner) ∧
      writerUpdate s t (s.authority.holder.any fun incumbent => incumbent.1 == worker) ∧
      t.leases = pruneLeases t.roster s.holds s.leases
  | .withdraw owner, .withdrawn =>
      frame { writer := true, roster := true, leases := true } s t ∧
      r.principal = .administrator ∧ s.roster owner.1 = some owner ∧
      t.lastSerial = s.lastSerial ∧ t.roster = replace s.roster owner.1 none ∧
      writerUpdate s t (s.authority.holder == some owner) ∧
      t.leases = pruneLeases t.roster s.holds s.leases
  | .grant expectedEpoch expected owner, .granted writer recovery =>
      frame { writer := true, holds := true } s t ∧
      (r.principal = .administrator ∨ r.principal = .worker owner) ∧
      s.roster owner.1 = some owner ∧ expectedEpoch = s.history.writer.epoch ∧
      expected = (if s.history.active then some s.history.writer else none) ∧
      erasurePending s = false ∧ recovery.kind = .recovery ∧
      recovery.owner = owner ∧ recovery.checkpoint = s.checkpoints.selected ∧
      recovery.start = s.checkpoints.selected.cut ∧ recovery.through = s.head ∧
      insertsHold s r recovery t.holds ∧
      successor s t writer { s.authority with holder := some owner, epoch := s.authority.epoch + 1 }
  | .publishAndRotate grant checkpoint, .granted writer recovery =>
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
  | .append grant expected lane payload bytes references, .appended cut =>
      frame { writer := true, budget := true, head := true, objects := true } s t ∧
      erasurePending s = false ∧
      (∃ owner, s.authority.holder = some owner ∧ r.principal = .worker owner) ∧
      ObjectWithdrawal.canAdmitReferences s.objects references ∧
      appendEffect limits s t grant expected lane payload bytes references cut ∧
      t.objects = registerReferences s.objects references .suffix expected
  | .barrier, .barrier hold =>
      frame { holds := true } s t ∧ r.principal = .worker hold.owner ∧
      s.roster hold.owner.1 = some hold.owner ∧ hold.kind = .ordinary ∧
      hold.checkpoint = s.checkpoints.selected ∧ hold.start = s.checkpoints.selected.cut ∧
      hold.through = s.head ∧ exactRange s hold.start hold.through ∧ insertsHold s r hold t.holds
  | .prepareCheckpoint pending references, .checkpointPrepared result =>
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
  | .withdrawObject name version, .objectWithdrawn chosenName chosenVersion =>
      frame { objects := true } s t ∧ r.principal = .custodian ∧ name = chosenName ∧ version = chosenVersion ∧
      (s.objects.fence name = some version ∧ t.objects = s.objects ∨
        ObjectWithdrawal.canWithdraw s.objects name ∧ ¬ ObjectWithdrawal.fenced s.objects name ∧
        t.objects = commitWithdrawal s.objects name version)
  | .closeCheckpoint checkpoint, .checkpointClosed result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ checkpoint = result ∧
      (∃ closed, s.checkpoints.oldRoots checkpoint.revision = some (checkpoint, closed)) ∧
      (∀ id hold, s.holds id = some hold → hold.checkpoint ≠ checkpoint) ∧
      (∀ p, s.checkpoints.preparing = some p → p.base ≠ checkpoint) ∧
      t.checkpoints = { s.checkpoints with
        oldRoots := replace s.checkpoints.oldRoots checkpoint.revision (some (checkpoint, true)) } ∧
      dropReferences s.objects t.objects (fun _ _ => True)
  | .settleCheckpoint checkpoint disposition floor, .checkpointSettled result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ checkpoint = result ∧
      floor = s.checkpoints.erasureFloor ∧ disposition ≠ 0 ∧
      s.checkpoints.oldRoots checkpoint.revision = some (checkpoint, true) ∧
      (∀ id hold, s.holds id = some hold → hold.checkpoint ≠ checkpoint) ∧
      (∀ p, s.checkpoints.preparing = some p → p.base ≠ checkpoint) ∧
      t.checkpoints = { s.checkpoints with
        oldRoots := replace s.checkpoints.oldRoots checkpoint.revision none } ∧
      dropReferences s.objects t.objects (fun role id => role ≠ .root ∨ id ≠ checkpoint.revision)
  | .disposeWorker owner disposition, .workerDisposed result =>
      frame { holds := true, leases := true } s t ∧ r.principal = .administrator ∧ owner = result ∧
      disposition ≠ 0 ∧ DisposalLease.withdrawn owner.2 s.lastSerial
        (decide (s.roster owner.1 = some owner)) = true ∧
      t.holds = removesOwner s.holds owner ∧ t.leases = pruneLeases s.roster t.holds s.leases
  | .publish checkpoint, .published result =>
      frame { checkpoints := true, objects := true } s t ∧ r.principal = .custodian ∧ checkpoint = result ∧
      (checkpoint = s.checkpoints.selected ∧ t.checkpoints = s.checkpoints ∧ t.objects = s.objects ∨
       (∃ p, s.checkpoints.preparing = some p ∧ p.erasure = false ∧ matchesPreparation p checkpoint) ∧
        retainedCut s checkpoint.cut.nextLsn = some checkpoint.cut ∧
        t.checkpoints = publishSelection s.checkpoints checkpoint false ∧
        dropReferences s.objects t.objects (fun _ _ => True))
  | .fundWindow window, .windowFunded result =>
      frame { budget := true } s t ∧ r.principal = .custodian ∧ window = result ∧
      window.allocation ≠ 0 ∧ window.bytes ≠ 0 ∧ window.serial = s.window.serial + 1 ∧
      OrderedBudgets.admitsDebit s.budget.budget.ordinary window.bytes limits.ordinaryCapacity ∧
      t.budget = fundWindow s.budget.budget window.bytes ∧ t.window = window
  | .protect writer through, .protectedHold hold =>
      frame { holds := true } s t ∧ s.history.active = true ∧ s.history.writer = writer ∧
      s.authority.holder = some hold.owner ∧ r.principal = .worker hold.owner ∧
      hold.kind = .ordinary ∧ hold.checkpoint = s.checkpoints.selected ∧
      hold.start = s.checkpoints.selected.cut ∧ hold.through = through ∧
      exactRange s hold.start hold.through ∧ insertsHold s r hold t.holds
  | .protectRange start through, .protectedHold hold =>
      frame { holds := true } s t ∧ r.principal = .worker hold.owner ∧
      s.roster hold.owner.1 = some hold.owner ∧ hold.kind = .ordinary ∧
      hold.checkpoint = s.checkpoints.selected ∧ hold.start.nextLsn = start ∧
      hold.through.nextLsn = through ∧ exactRange s hold.start hold.through ∧ insertsHold s r hold t.holds
  | .protectCheckpoint root start through, .protectedHold hold =>
      frame { holds := true } s t ∧ r.principal = .worker hold.owner ∧
      s.roster hold.owner.1 = some hold.owner ∧ hold.kind = .ordinary ∧ hold.checkpoint.root = root ∧
      hold.start = hold.checkpoint.cut ∧ hold.start.nextLsn = start ∧
      hold.through.nextLsn = through ∧ checkpointOpen s hold.checkpoint ∧
      (hold.start = hold.through ∨ exactRange s hold.start hold.through) ∧ insertsHold s r hold t.holds
  | .protectRoot source, .protectedHold hold =>
      frame { holds := true } s t ∧ r.principal = .worker hold.owner ∧ hold.kind = .root source ∧
      (∃ recovery, s.holds source = some recovery ∧ recovery.kind = .recovery ∧
        recovery.owner = hold.owner ∧ recovery.checkpoint = hold.checkpoint) ∧
      checkpointOpen s hold.checkpoint ∧
      (∀ id old, s.holds id = some old → old.kind ≠ .root source) ∧
      hold.start = hold.checkpoint.cut ∧ hold.through = hold.start ∧ insertsHold s r hold t.holds
  | .vacate grant, .vacated =>
      frame { writer := true } s t ∧
      canVacate s.history (erasurePending s)
        (match r.principal with | .worker owner => some owner | _ => none) s.authority.holder grant ∧
      t.history = { s.history with active := false } ∧ t.authority = vacate s.authority
  | .sealCohort expected successor, .cohortSealed result =>
      frame { cohortSeal := true } s t ∧ r.principal = .administrator ∧ successor = result ∧
      expected = s.voterScope ∧ successor ≠ 0 ∧ successor ≠ expected ∧ t.successor = some successor
  | .release hold id, .released =>
      frame { holds := true, leases := true } s t ∧ r.principal = .worker hold.owner ∧
      s.holds id = some hold ∧ t.holds = replace s.holds id none ∧
      t.leases = pruneLeases s.roster t.holds s.leases
  | .releaseRead id, .released =>
      frame { holds := true, leases := true } s t ∧ (∃ owner, r.principal = .worker owner) ∧
      (s.holds id = none ∧ t.holds = s.holds ∧ t.leases = s.leases ∨
        (∃ hold entry, s.holds id = some hold ∧ hold.origin = r.principal ∧
          hold.kind = .ordinary ∧ s.book (r.principal, id) = some entry ∧
          entry.original.outcome = .ok (.barrier hold)) ∧
        t.holds = replace s.holds id none ∧ t.leases = pruneLeases s.roster t.holds s.leases)
  | .lease grant, .leased issuedAt leaseEnd =>
      frame { leases := true } s t ∧ s.history.active = true ∧ s.history.writer = grant ∧
      (∃ owner, r.principal = .worker owner ∧ s.authority.holder = some owner ∧
        s.roster owner.1 = some owner ∧ renewsLease s limits owner issuedAt leaseEnd t.leases)
  | .leaseRead hold id, .readLeased issuedAt leaseEnd =>
      frame { leases := true } s t ∧ r.principal = .worker hold.owner ∧
      checkpointOpen s hold.checkpoint ∧
      DisposalLease.read_lease_end (s.roster hold.owner.1) (some hold.owner) hold.owner
        (s.holds id) hold
        (DisposalLease.interval_available (hold.start == hold.through) s.floor.nextLsn
          hold.start.nextLsn hold.through.nextLsn s.history.records.length)
        true s.time limits.leaseDuration limits.maxTime = some leaseEnd ∧
      renewsLease s limits hold.owner issuedAt leaseEnd t.leases
  | .disposeExpired owner, .workerDisposed result =>
      frame { holds := true, leases := true } s t ∧ owner = result ∧
      DisposalLease.may_dispose (decide (r.principal = .administrator ∨ r.principal = .custodian))
        owner.2 s.lastSerial (decide (s.roster owner.1 = some owner)) s.time
        (s.leases owner) limits.drift limits.maxTime = true ∧
      t.holds = removesOwner s.holds owner ∧ t.leases = pruneLeases s.roster t.holds s.leases
  | .trim selected through, .trimmed cut credit =>
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
  | _, _ => False

private theorem disposed_hold_absent (holds : Holds) (owner : Owner) (id : RequestId) (hold : Hold)
    (present : removesOwner holds owner id = some hold) : hold.owner ≠ owner := by
  cases found : holds id with
  | none => simp [removesOwner, found] at present
  | some old =>
    have kept : old = hold ∧ hold.owner ≠ owner := by
      simpa [removesOwner, found] using present
    exact kept.2

theorem expired_disposal_leaves_no_custody {limits : Limits} {s t : State} {r : Request}
    {owner : Owner} (command : r.command = .disposeExpired owner)
    (applied : effect limits s r (.workerDisposed owner) t) :
    t.leases owner = none ∧ ∀ id hold, t.holds id = some hold → hold.owner ≠ owner := by
  simp only [effect, command] at applied
  obtain ⟨_, _, due, holds, leases⟩ := applied
  have noHolds : ∀ id hold, t.holds id = some hold → hold.owner ≠ owner := by
    rw [holds]
    exact disposed_hold_absent s.holds owner
  have withdrawn := (DisposalLease.disposal_requires_withdrawal_and_drift due).1
  have absent : ¬ leaseOwner s.roster t.holds owner := by
    intro owns
    rcases owns with enrolled | ⟨id, hold, held, eq⟩
    · simp [DisposalLease.withdrawn, enrolled] at withdrawn
    · exact noHolds id hold held eq
  exact ⟨by simp [leases, pruneLeases, absent], noHolds⟩

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
  (replay r.command.isBarrier retained.fingerprint r.fingerprint retained.original).getD
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

inductive ApplyError where
  | position | time

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

def spec_step (limits : Limits) (before : State) (position time : Nat)
    (request : Request) (after : State) (out : Except ApplyError Receipt) : Prop :=
  Step limits position time request before out after

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

structure ReducerInv (limits : Limits) (s : State) : Prop where
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
    · have recorded : record_after_apply r.command.isBarrier (.ok out : Except Refusal AppliedOutcome) = true := by
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
    (inv : ReducerInv limits s) (step : Step limits position time request s out t) :
    CompactImage.generationInRange t.authority.epoch t.authority.generation := by
  cases step with
  | rejected => exact inv.generation
  | chosen _ requestStep =>
    cases requestStep with
    | applied _ effects =>
      exact valid_generation_preserved inv.generation effects.authority effects.rotationIncumbent
    | _ => exact inv.generation

theorem step_preserves_inv {limits position time request s out t}
    (inv : ReducerInv limits s) (step : Step limits position time request s out t) :
    ReducerInv limits t := by
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

theorem trace_preserves_inv {limits s t} (inv : ReducerInv limits s) (trace : Trace limits s t) :
    ReducerInv limits t := by
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

theorem trace_preserves_history {limits s t} (inv : ReducerInv limits s) (trace : Trace limits s t)
    {lsn : Nat} (committed : lsn < (projectKernel s).history.length) :
    (projectKernel t).history[lsn]? = (projectKernel s).history[lsn]? :=
  Kernel.Ordered.history_is_irrevocable inv.image (trace_projects_history trace) committed

theorem commit_append_advances_head (history : Image Record) (grant : Writer)
    (record : Record) :
    (commitAppend history grant record (history.head + 1)).head = history.head + 1 := by
  rfl

theorem funding_resets_spend (budget : OrderedBudgets.Budget) (window : Nat) :
    (fundWindow budget window).budget.spent = 0 := by
  rfl

theorem vacancy_clears_holder (authority : ErasureCommit.Authority Owner) :
    (vacate authority).holder = none := by
  rfl

theorem a_cached_barrier_refuses {s : State} {r : Request}
    (reading : r.command.isBarrier = true) (retained : RetainedReceipt Nat Receipt) :
    cachedReceipt s r retained = currentReceipt s.placement s.position r (.error .conflict) := by
  unfold cachedReceipt
  rw [reading, Protocol.Ordered.barriers_never_replay]
  rfl

theorem a_refused_barrier_leaves_no_receipt (placement position : Nat) (r : Request)
    (reading : r.command.isBarrier = true) (refusal : Refusal) (book : Book) :
    recordReceipt placement position r (.error refusal) book = book := by
  simp [recordReceipt, record_after_apply, reading]

private def witnessLimits : Limits :=
  ⟨⟨1024, 1024⟩, 1024, 128, 10, 7, 1, 1024, fun previous position time fingerprint =>
    previous + position + time + fingerprint⟩

private def witnessInitial : State :=
  let empty : Cut := ⟨0, 0⟩
  let initialRoot : Checkpoint := ⟨empty, 0, 1, 0⟩
  { placement := 1, position := 0, time := 0, commandHistory := 0,
    voterScope := 1, successor := none,
    history := ⟨⟨⟨1, 1⟩, 0, 0⟩, false, [], [], 0⟩, authority := ⟨none, 0, 1⟩,
    budget := ⟨⟨0, 0, 0⟩, 256⟩, window := ⟨1, 1, 256⟩, floor := empty, head := empty,
    checkpoints := ⟨initialRoot, none, fun _ => none, 0⟩,
    roster := fun _ => none, lastSerial := 0, holds := fun _ => none, leases := fun _ => none,
    objects := ⟨fun _ _ _ => False, fun _ => none, False, 0, 0⟩, book := fun _ => none }

theorem reachable_funded_successor :
    ∃ s t : State, ReducerInv witnessLimits s ∧ Trace witnessLimits s t ∧
      t.position = 1 ∧ t.window.serial = 2 ∧ t.budget.window = 512 := by
  let window : Window := ⟨2, 2, 512⟩
  let r : Request := ⟨1, .custodian, ⟨1, 4⟩, .fundWindow window, 7⟩
  let s := advance witnessLimits witnessInitial 1 3 r
  let t := { s with window, budget := fundWindow s.budget.budget window.bytes }
  let out : AppliedOutcome := .windowFunded window
  have freshRequest : fresh witnessLimits s r := ⟨rfl, rfl, rfl⟩
  have paid : OrderedBudgets.admitsDebit s.budget.budget.ordinary 512 witnessLimits.ordinaryCapacity := by
    change 0 + 512 ≤ 1024
    decide
  have funded : Applied witnessLimits s r out t := by
    refine ⟨?_, .stutter _, .stutter _, Or.inr (.fund _ 512 paid), Or.inl rfl,
      ?_, ?_, rfl, rfl, ?_⟩
    · exact ⟨by simp [frame, s, t], rfl, rfl, by decide, by decide, rfl, paid, rfl, rfl⟩
    · intro id hold present
      exact Or.inl present
    · intro _ _ present
      contradiction
    · intro increased
      exact False.elim ((Nat.lt_irrefl _) increased)
  have inv : ReducerInv witnessLimits witnessInitial := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by decide, by decide, ?_, by decide, by decide⟩
      intro _ _ unused
      contradiction
    · change 0 ≤ 256 ∧ 0 + (256 - 0) ≤ 1024 ∧ 0 ≤ 128
      decide
    · change 0 < 1 ∧ 1 ≤ max 1 0
      decide
    · intro _ fenced
      exact False.elim (fenced rfl)
    · intro _ _ present
      contradiction
    · intro _ _ present
      contradiction
  exact ⟨witnessInitial, _, inv, .next (.same _) (.chosen rfl (.applied freshRequest funded)),
    rfl, rfl, rfl⟩

#print axioms expired_disposal_leaves_no_custody
#print axioms trim_credit_matches_protocol
#print axioms commit_withdrawal_projects
#print axioms step_projects
#print axioms step_projects_kernel
#print axioms step_preserves_inv
#print axioms trace_preserves_inv
#print axioms trace_projects_authority
#print axioms trace_projects_budget
#print axioms trace_projects_objects
#print axioms trace_preserves_fence
#print axioms trace_preserves_history
#print axioms commit_append_advances_head
#print axioms funding_resets_spend
#print axioms vacancy_clears_holder
#print axioms a_cached_barrier_refuses
#print axioms a_refused_barrier_leaves_no_receipt
#print axioms reachable_funded_successor

end Logkeeper.Reducer
