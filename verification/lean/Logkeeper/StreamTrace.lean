import Logkeeper.StreamReplacement

/-! Replay of every keeper effect in the simulator corpus against Study 119's keeper step.

The simulator records each delivered request with the keeper's durable image before and
after it, and each WAL reopen. An image is the keeper view and, for an incomplete Sync, the
staged floor, start, tail and epoch runs. The replay abstracts a staged Sync to the history
it builds, as Study 119's `staging` does, and checks that the effect is the reference step
for the request: its keeper-side admission and its exact change. Writer-side premises
(`owns`, the seed and `advertised`) are the I/O automaton's obligations. -/

namespace Logkeeper.StreamTrace

set_option warningAsError true
set_option autoImplicit false

structure Run where
  epoch : Nat
  first : Nat
  last : Nat
  deriving BEq, Repr

/-- Epochs and promises are shifted by one; zero represents none. `owner` indexes identities. -/
structure View where
  promised : Nat
  owner : Nat
  synced : Nat
  floor : Nat
  tail : Nat
  head : Nat
  learner : Bool
  ensemble : List Nat
  runs : List Run
  deriving BEq, Repr

structure Staged where
  floor : Nat
  start : Nat
  tail : Nat
  runs : List Run
  deriving BEq, Repr

structure Image where
  present : Bool
  deleted : Bool
  view : View
  staged : Option Staged
  deriving BEq, Repr

/-- The history a staged Sync builds, as Study 119 stages it: floor, tail and the epoch
    runs of the positions it will retain. -/
structure Build where
  floor : Nat
  tail : Nat
  runs : List Run
  deriving BEq, Repr

private def check (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

/-- Runs restricted to `[origin, through]`. -/
def clip (runs : List Run) (origin through : Nat) : List Run :=
  runs.filterMap fun run =>
    let first := max run.first origin
    let last := min run.last through
    if first ≤ last then some ⟨run.epoch, first, last⟩ else none

/-- Join adjacent runs of one epoch, as the keeper's `push` does. -/
def merge : List Run → List Run → List Run
  | left, [] => left
  | [], right => right
  | left, run :: rest =>
      match left.getLast? with
      | some last =>
          if last.epoch == run.epoch && last.last + 1 == run.first then
            merge (left.dropLast ++ [⟨last.epoch, last.first, run.last⟩]) rest
          else merge (left ++ [run]) rest
      | none => merge [run] rest
termination_by _ right => right.length

/-- Runs cover exactly `[origin, tail]` in order, with no two adjacent runs of one epoch. -/
def covers (runs : List Run) (origin tail : Nat) : Bool :=
  let rec go (position : Nat) (previous : Option Nat) : List Run → Bool
    | [] => position == tail + 1
    | run :: rest => run.first == position && run.first ≤ run.last && run.last ≤ tail &&
        previous != some run.epoch && go (run.last + 1) (some run.epoch) rest
  go origin none runs

def Image.build (image : Image) : Option Build :=
  image.staged.map fun staged =>
    let below := clip image.view.runs image.view.floor (staged.start - 1)
    ⟨staged.floor, staged.tail,
      clip (merge below staged.runs) (max image.view.floor staged.floor) staged.tail⟩

def View.bounded (view : View) : Bool :=
  0 < view.floor && view.floor ≤ view.head + 1 && view.head ≤ view.tail &&
    covers view.runs view.floor view.tail

inductive Reply where
  | refused | wrongEnsemble (ensemble : List Nat)
  | created | sealed (view : View) | synced (tail : Nat) | appended (tail : Nat)
  | trimmed (floor : Nat) | checked (view : View)
  | records (floor head : Nat) (positions : List Nat)
  | deleted | replaced
  /-- A crash after the WAL sync lost the reply. The effect is durable. -/
  | lost
  /-- A transport error origin the keeper. -/
  | failed

structure Row where
  verb : String
  serial : Nat
  keeper : Nat
  caller : Nat
  before : Image
  after : Image
  fields : List Nat
  runs : List Run
  reply : Reply

/-- Which Study 119 step an effect refines. -/
inductive Projection where
  | stutter | create | seal | syncPart | sync | installFloor | append | publish | trim | delete
  | replace | promote | wrongEnsemble | lose
  deriving BEq, Repr

def Projection.name : Projection → String
  | .stutter => "stutter" | .create => "create" | .seal => "seal" | .syncPart => "staged sync"
  | .sync => "complete sync" | .installFloor => "floor installation" | .append => "append"
  | .publish => "publication" | .trim => "trim" | .delete => "delete"
  | .replace => "survivor install" | .promote => "learner install"
  | .wrongEnsemble => "WrongEnsemble" | .lose => "disk loss"

def Projection.all : List Projection :=
  [.stutter, .create, .seal, .syncPart, .sync, .installFloor, .append, .publish, .trim, .delete,
    .replace, .promote, .wrongEnsemble, .lose]

private def unchanged (row : Row) : Except String Projection := do
  check (row.after == row.before) "stutter changed the image"
  return .stutter

private def accepted : Reply → Bool
  | .refused | .wrongEnsemble _ | .failed => false
  | _ => true

private def promisedTo (row : Row) (epoch : Nat) : Bool :=
  row.before.view.promised == epoch + 1 && row.before.view.owner == row.caller

def defaultView (ensemble : List Nat) (keeper : Nat) : View :=
  ⟨0, 0, 0, 1, 0, 0, !ensemble.contains keeper, ensemble, []⟩

private def checkRecords (origin : Nat) (through : Nat) (positions : List Nat) : Bool :=
  positions.length == 0 || (positions == (List.range positions.length).map (· + origin) &&
    origin + positions.length - 1 ≤ through)

def sealEffect (row : Row) (epoch : Nat) (ensemble : List Nat) : Except String Projection := do
  let before := row.before.view
  check (ensemble == before.ensemble) "seal ensemble"
  check (before.promised < epoch + 1 || (before.promised == epoch + 1 && before.owner == row.caller))
    "seal fence"
  let fresh := before.promised != epoch + 1
  let expected := if fresh then
      { row.before with view := { before with promised := epoch + 1, owner := row.caller },
                        staged := none }
    else row.before
  check (row.after == expected) "seal effect"
  match row.reply with
  | .sealed view => check (view == expected.view) "seal reply reports the vote"
  | _ => pure ()
  return if fresh then .seal else .stutter

def syncEffect (row : Row) (epoch floor origin count head complete : Nat) : Except String Projection := do
  let before := row.before.view
  check (promisedTo row epoch) "sync promise"
  let synced := before.synced == epoch + 1
  if synced then
    -- A synced keeper accepts only floor installation or an identical complete retry.
    if complete == 0 then
      check (count == 0 && row.runs.isEmpty && floor == origin && 0 < floor && floor == head + 1)
        "synced sync form"
      if floor ≤ before.floor then return ← unchanged row
      check (before.floor ≤ head) "floor installation below floor"
      let tail := max before.tail head
      let view := { before with floor, tail, head := max before.head head,
                                runs := clip before.runs floor tail }
      check (row.after == { row.before with view }) "floor installation effect"
      return .installFloor
    else
      return ← unchanged row
  else
    let build := row.before.build.getD ⟨before.floor, before.tail, before.runs⟩
    let stagedFloor := (row.before.staged.map fun staged => max staged.floor floor).getD floor
    let start := max (max origin stagedFloor) (max before.floor (before.head + 1))
    check (0 < stagedFloor && stagedFloor ≤ origin && before.floor ≤ origin) "sync floor"
    check (origin ≤ build.tail + 1 || origin == stagedFloor) "sync gap"
    check (covers row.runs origin (origin + count - 1)) "sync epoch runs"
    let skip := min (start - origin) count
    let tail := start - 1 + (count - skip)
    check (before.head ≤ head && head ≤ tail && stagedFloor ≤ head + 1) "sync head"
    let below := if start ≤ build.tail + 1 then clip build.runs build.floor (start - 1) else []
    let image := merge below (clip row.runs start tail)
    if complete == 0 then
      let staged := row.after.build
      check (row.after.view == before) "staged sync changed the view"
      check (staged == some ⟨stagedFloor, tail, clip image (max before.floor stagedFloor) tail⟩)
        "staged sync effect"
      return .syncPart
    else
      let floor := max before.floor stagedFloor
      let view := { before with synced := epoch + 1, floor, tail, head, runs := clip image floor tail }
      check (row.after == { row.before with view, staged := none }) "complete sync effect"
      match row.reply with
      | .synced replied => check (replied == tail) "sync reply tail"
      | _ => pure ()
      return .sync

def appendEffect (row : Row) (epoch position count head : Nat) : Except String Projection := do
  let before := row.before.view
  check (promisedTo row epoch) "append promise"
  check (before.synced == epoch + 1 && !before.learner) "append requires a synced voter"
  check (before.floor ≤ position && position ≤ before.tail + 1) "append position"
  let projection ← if position == before.tail + 1 && 0 < count then do
      let tail := before.tail + count
      check (head ≤ tail) "append head beyond tail"
      let runs := merge before.runs [⟨epoch, position, tail⟩]
      let view := { before with tail, head := max before.head head, runs }
      check (row.after == { row.before with view }) "append effect"
      pure Projection.append
    else do
      check (head ≤ before.tail) "publication beyond tail"
      check (row.after == { row.before with view := { before with head := max before.head head } })
        "publication effect"
      pure (if before.head < head then Projection.publish else Projection.stutter)
  match row.reply with
  | .appended tail => check (tail == row.after.view.tail) "append reply tail"
  | _ => pure ()
  return projection

def trimEffect (row : Row) (epoch through : Nat) : Except String Projection := do
  let before := row.before.view
  check (promisedTo row epoch) "trim promise"
  check (before.synced == epoch + 1 && !before.learner) "trim requires a synced voter"
  check (through ≤ before.head) "trim beyond head"
  let floor := max before.floor (through + 1)
  let view := { before with floor, runs := clip before.runs floor before.tail }
  check (row.after == { row.before with view }) "trim effect"
  return if before.floor < floor then .trim else .stutter

def replaceEffect (row : Row) (epoch : Nat) (origin to : List Nat) : Except String Projection := do
  let before := row.before.view
  check (promisedTo row epoch && before.synced == epoch + 1) "replace requires a synced promise"
  let decision := StreamReplacement.replaceDecision (promisedTo row epoch)
    (before.synced == epoch + 1) (before.ensemble == to) (before.ensemble == origin)
    (!to.contains 0 && to.Nodup) (to.contains row.keeper)
    ((List.zip origin to).countP (fun pair => pair.1 != pair.2))
  if decision == .replaced then return ← unchanged row
  check (decision == .persist) "replace ensemble"
  let (ensemble, learner) := StreamReplacement.installEnsemble to
  check (row.after == { row.before with view := { before with ensemble, learner } })
    "replace effect"
  return if before.learner then .promote else .replace

def wrongEnsembleEffect (row : Row) (reported : List Nat) : Except String Projection := do
  let requested ← match row.verb, row.fields with
    | "seal", [_, a, b, c] | "replace", [_, a, b, c, _, _, _]
    | "delete", [a, b, c] => pure [a, b, c]
    | _, _ => throw "WrongEnsemble request"
  check (row.before.present && row.before.view.ensemble == reported &&
    requested != reported) "WrongEnsemble reports current ensemble"
  let _ ← unchanged row
  return .wrongEnsemble

def observe (row : Row) (verb : String) (fields : List Nat) : Except String Projection := do
  let before := row.before.view
  match verb, fields, row.reply with
  | "check", _, .checked view => check (view == before) "check reports the view"
  | "read", [origin, _], .records floor head positions =>
      check (floor == before.floor && head == before.head && before.floor ≤ origin &&
        checkRecords origin before.head positions) "read returns committed records"
  | "recover", [epoch, origin, _], .records floor _ positions =>
      check (promisedTo row epoch && floor == before.floor && before.floor ≤ origin &&
        checkRecords origin before.tail positions) "recover returns accepted records"
  | _, _, _ => pure ()
  unchanged row

def step (row : Row) : Except String Projection := do
  check (row.before.view.bounded && row.after.view.bounded) "keeper image bounds"
  if row.verb == "reopen" then
    check (row.after == row.before) "reopen restores the durable image"
    return .stutter
  if row.verb == "lose" then
    check (row.before.present && !row.after.present && !row.after.deleted &&
      row.after.staged.isNone) "disk loss clears the image"
    return .lose
  if let .wrongEnsemble ensemble := row.reply then
    return ← wrongEnsembleEffect row ensemble
  if !accepted row.reply then return ← unchanged row
  if row.verb == "delete" then
    check (row.after.present && row.after.deleted) "delete installs a tombstone"
    return if row.before.deleted then .stutter else .delete
  if row.verb == "create" then
    if row.before.present then return ← unchanged row
    let ensemble := row.fields
    check (row.after == ⟨true, false, defaultView ensemble row.keeper, none⟩) "create effect"
    return .create
  check (row.before.present && !row.before.deleted) "request on an absent or deleted stream"
  match row.verb, row.fields with
  | "seal", [epoch, a, b, c] => sealEffect row epoch [a, b, c]
  | "sync", [epoch, floor, origin, count, head, complete] =>
      syncEffect row epoch floor origin count head complete
  | "append", [epoch, position, count, head] => appendEffect row epoch position count head
  | "trim", [epoch, through] => trimEffect row epoch through
  | "replace", [epoch, a, b, c, d, e, f] => replaceEffect row epoch [a, b, c] [d, e, f]
  | "check", _ | "read", _ | "recover", _ => observe row row.verb row.fields
  | _, _ => throw "event fields"

/-- Replay the simulation's single replacement plan per seed. Local keeper effects
    above do not know which other keepers have installed their ensemble. -/
structure SweepProgress where
  lost : Option Nat := none
  installed : List (Nat × List Nat) := []

def SweepProgress.advance (sweep : SweepProgress) (row : Row) :
    Projection → Except String SweepProgress
  | .lose => do
      check sweep.lost.isNone "multiple disk losses in one simulation seed"
      return { sweep with lost := some row.keeper }
  | .replace => do
      let old := row.before.view.ensemble
      let next := row.after.view.ensemble
      check (old.contains row.keeper && sweep.lost.any (fun lost =>
        old.contains lost && !next.contains lost)) "survivor replaced the lost member"
      return { sweep with installed := (row.keeper, next) :: sweep.installed }
  | .promote => do
      let old := row.before.view.ensemble
      let next := row.after.view.ensemble
      let survivors := old.filter next.contains
      check (survivors.length == 2 && survivors.all (fun id =>
        sweep.installed.contains (id, next))) "learner installs after both survivors"
      return sweep
  | _ => pure sweep

/-! Parsing. Lists are prefixed by their length. -/

abbrev Parser := StateT (List Nat) (Except String)

private def next : Parser Nat := do
  match ← get with
  | value :: rest => set rest; return value
  | [] => throw "missing field"

private def flag : Parser Bool := do
  match ← next with
  | 0 => return false
  | 1 => return true
  | _ => throw "expected a flag"

private def many {α : Type} (item : Parser α) : Parser (List α) := do
  let count ← next
  (List.range count).mapM fun _ => item

private def run : Parser Run := do return ⟨← next, ← next, ← next⟩

private def view : Parser View := do
  let promised ← next
  let owner ← next
  let synced ← next
  let floor ← next
  let tail ← next
  let head ← next
  let learner ← flag
  let ensemble := [← next, ← next, ← next]
  return ⟨promised, owner, synced, floor, tail, head, learner, ensemble, ← many run⟩

private def image : Parser Image := do
  let present ← flag
  let deleted ← flag
  let view ← view
  let staged ← if ← flag then pure (some ⟨← next, ← next, ← next, ← many run⟩) else pure none
  return ⟨present, deleted, view, staged⟩

private def reply : Parser Reply := do
  match ← next with
  | 0 => return .refused
  | 1 => return .created
  | 2 => return .sealed (← view)
  | 3 => return .synced (← next)
  | 4 => return .appended (← next)
  | 5 => return .trimmed (← next)
  | 6 => return .checked (← view)
  | 7 => return .records (← next) (← next) (← many next)
  | 8 => return .deleted
  | 9 => return .replaced
  | 10 => return .lost
  | 11 => return .failed
  | 12 => return .wrongEnsemble [← next, ← next, ← next]
  | _ => throw "unknown reply"

private def request (verb : String) : Parser (List Nat × List Run) := do
  let fixed : Nat := match verb with
    | "create" | "delete" => 3 | "seal" => 4 | "sync" => 6 | "append" => 4 | "trim" => 2
    | "check" => 1 | "read" => 2 | "recover" => 3 | "replace" => 7 | _ => 0
  let fields ← (List.range fixed).mapM fun _ => next
  let runs ← if verb == "sync" then many run else pure []
  return (fields, runs)

def parse (line : String) : Except String Row := do
  let verb :: tokens := line.splitOn " " | throw "missing event"
  let numbers ← tokens.mapM fun token => match token.toNat? with
    | some number => .ok number
    | none => .error "expected an unsigned integer"
  let parser : Parser Row := do
    let serial ← next
    let keeper ← next
    let caller ← next
    let before ← image
    let after ← image
    let (fields, runs) ← if verb == "reopen" || verb == "lose" then pure ([], []) else request verb
    let reply ← if verb == "reopen" || verb == "lose" then pure Reply.lost else reply
    return ⟨verb, serial, keeper, caller, before, after, fields, runs, reply⟩
  let (row, rest) ← parser.run numbers
  check rest.isEmpty "trailing fields"
  return row

end Logkeeper.StreamTrace
