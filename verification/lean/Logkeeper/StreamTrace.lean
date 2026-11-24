import Logkeeper.StreamAsync

namespace Logkeeper.StreamTrace

set_option warningAsError true
set_option autoImplicit false

structure Image where
  synced : Nat  -- wire epochs are shifted by one, zero represents no sync
  floor : Nat
  tail : Nat
  head : Nat
  deriving BEq

structure Effect where
  epoch : Nat
  promised : Nat
  sameIdentity : Nat
  learner : Nat
  prior : Image
  next : Image

inductive Projection where
  | checked | inheritedPublication | incompleteSync

private def check (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def Image.bounded (image : Image) : Bool :=
  0 < image.floor && image.floor ≤ image.head + 1 && image.head ≤ image.tail

private def checkRuns (position tail : Nat) (previousEpoch : Option Nat) : List Nat → Except String Unit
  | [] => check (position == tail + 1) "epoch run coverage"
  | epoch :: first :: last :: rest => do
      check (first == position && first ≤ last && last ≤ tail && previousEpoch != some epoch)
        "epoch run coverage"
      checkRuns (last + 1) tail (some epoch) rest
  | _ => .error "epoch run fields"

private def hasRecord (epoch : Nat) : List Nat → Bool
  | run :: _ :: _ :: rest => run == epoch || hasRecord epoch rest
  | _ => false

def step (verb : String) (effect : Effect) (fields : List Nat) : Except String Projection := do
  let before := effect.prior
  let after := effect.next
  check (effect.promised == effect.epoch) "promise"
  check (effect.sameIdentity == 1) "authenticated identity"
  check (before.bounded && after.bounded) "keeper image bounds"
  check (after.synced == before.synced) "sync epoch changed"
  match verb, fields with
  | "publish", position :: head :: runs =>
      check (before.synced == effect.epoch + 1) "publication requires a complete sync"
      check (effect.learner == 0) "publication requires a voter"
      check (position == head + 1 && before.floor ≤ position) "publication position"
      check (head ≤ before.tail) "publication beyond tail"
      checkRuns before.floor before.tail none runs
      check (after == { before with head := max before.head head }) "publication effect"
      return if before.head < head && !hasRecord effect.epoch runs then
        .inheritedPublication else .checked
  | "sync-part", [start, floor, head, count] =>
      if before.synced == effect.epoch + 1 then
        check (floor == start && 0 < floor && head + 1 == floor && count == 0) "synced floor install"
        let expected := if floor ≤ before.floor then before else
          { before with floor, head := max before.head head, tail := max before.tail head }
        check (after == expected) "floor install effect"
        return .checked
      else
        let tail := start - 1 + count
        check (0 < floor && floor ≤ start && before.floor ≤ start) "incomplete sync floor"
        check (start ≤ before.tail + 1 || start == floor) "incomplete sync gap"
        check (before.head ≤ head && head ≤ tail && floor ≤ head + 1) "incomplete sync head"
        check (after == { before with floor := max before.floor floor, tail, head }) "incomplete sync effect"
        return if after.tail != before.tail then .incompleteSync else .checked
  | _, _ => .error "event fields"

def parse (line : String) : Except String (Nat × Nat × Projection) := do
  let verb :: fields := (line.splitOn " ") | throw "missing event"
  let numbers ← fields.mapM fun field => match field.toNat? with
    | some number => .ok number
    | none => .error "expected an unsigned integer"
  let serial :: keeper :: epoch :: promised :: owner :: learner ::
      syncedBefore :: floorBefore :: tailBefore :: headBefore ::
      syncedAfter :: floorAfter :: tailAfter :: headAfter :: rest := numbers |
    throw "missing effect fields"
  let effect : Effect := ⟨epoch, promised, owner, learner,
    ⟨syncedBefore, floorBefore, tailBefore, headBefore⟩,
    ⟨syncedAfter, floorAfter, tailAfter, headAfter⟩⟩
  return (serial, keeper, ← step verb effect rest)

end Logkeeper.StreamTrace
