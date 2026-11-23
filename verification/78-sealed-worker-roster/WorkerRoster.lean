import Std

set_option warningAsError true

namespace JointSource

inductive WorkerChange where
  | enroll (holder issuedThrough : Nat)
  | withdraw (holder enrollment : Nat)

structure Workers where
  issuedThrough : Nat
  members : List (Nat × Nat)
  deriving DecidableEq

def Workers.enrollment (workers : Workers) (holder : Nat) : Option Nat :=
  (workers.members.find? (fun member => member.1 == holder)).map Prod.snd

def Workers.change (workers : Workers) (capacity lastSerial : Nat) : WorkerChange → Option Workers
  | .enroll holder issuedThrough =>
      if issuedThrough = workers.issuedThrough ∧ workers.issuedThrough < lastSerial ∧
          workers.enrollment holder = none ∧ workers.members.length < capacity then
        some ⟨workers.issuedThrough + 1, (holder, workers.issuedThrough + 1) :: workers.members⟩
      else none
  | .withdraw holder enrollment =>
      if workers.enrollment holder = some enrollment then
        some {workers with members := workers.members.filter (fun member => member.1 != holder)}
      else none

end JointSource
