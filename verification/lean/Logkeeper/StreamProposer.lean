import Logkeeper.StreamRpc

/-! The interpreter returns at most one event for each issued call. Model one
slot here. Independent slots interleave without changing each other's state. -/

namespace Logkeeper.StreamProposer

set_option autoImplicit false
set_option warningAsError true

def MatchesTicket (issued received : Nat) : Prop := issued = received

instance (issued received : Nat) : Decidable (MatchesTicket issued received) :=
  inferInstanceAs (Decidable (issued = received))

def NextTicket (previous : Nat) : Option Nat :=
  if previous = 2^64 - 1 then none else some (previous + 1)

inductive Event where
  | send (ticket : Nat)
  | receive (ticket : Nat)
  | cancel (ticket : Nat)

inductive Schedule : Option Nat → List Event → Option Nat → Prop
  | empty (pending : Option Nat) : Schedule pending [] pending
  | send {pending : Option Nat} {events : List Event} (ticket : Nat) :
      Schedule pending events none →
      Schedule pending (events ++ [.send ticket]) (some ticket)
  | receive {pending : Option Nat} {events : List Event} (ticket : Nat) :
      Schedule pending events (some ticket) →
      Schedule pending (events ++ [.receive ticket]) none
  | cancel {pending : Option Nat} {events : List Event} (ticket : Nat) :
      Schedule pending events (some ticket) →
      Schedule pending (events ++ [.cancel ticket]) none

def receive (pending : Option Nat) (ticket : Nat) : Option Nat :=
  match pending with
  | none => none
  | some issued => if MatchesTicket issued ticket then none else pending

/-- A driver outcome consumes its own send. Stale outcomes stutter. -/
theorem schedule_receive {pending outstanding : Option Nat} {events : List Event}
    (schedule : Schedule pending events outstanding) (ticket : Nat) :
    if outstanding = some ticket then
      Schedule pending (events ++ [.receive ticket]) (receive outstanding ticket)
    else Schedule pending events (receive outstanding ticket) := by
  split
  next matched =>
    rw [matched] at schedule
    simpa [receive, matched, MatchesTicket] using schedule.receive ticket
  next stale =>
    cases outstanding with
    | none => exact schedule
    | some issued =>
        have ne : issued ≠ ticket := by simpa using stale
        simpa [receive, MatchesTicket, ne] using schedule

theorem duplicate_reply_stutters (ticket : Nat) :
    receive (receive (some ticket) ticket) ticket = none := by
  simp [receive, MatchesTicket]

theorem schedule_witness (ticket : Nat) :
    Schedule none [.send ticket, .receive ticket] none := by
  exact ((Schedule.empty none).send ticket).receive ticket

/-- Cancelling a wait leaves any eventual durable delivery in the transport
    history. Its outcome cannot consume the next operation's ticket. -/
theorem cancelled_reply_stutters (issued : Nat) :
    receive (some (issued + 1)) issued = some (issued + 1) := by
  simp [receive, MatchesTicket]

theorem cancelled_schedule_witness (ticket : Nat) :
    Schedule none [.send ticket, .cancel ticket, .send (ticket + 1), .receive (ticket + 1)] none := by
  exact ((((Schedule.empty none).send ticket).cancel ticket).send (ticket + 1)).receive (ticket + 1)

/-- The scheduler can interleave all three slots. Its projection to each
    slot retains only that slot's sends, cancellations, and outcomes. -/
def project (slot : Fin 3) (events : List (Fin 3 × Event)) : List Event :=
  events.filterMap fun (target, event) => if target = slot then some event else none

def DriverSchedule (pending : Fin 3 → Option Nat) (events : List (Fin 3 × Event))
    (outstanding : Fin 3 → Option Nat) : Prop :=
  ∀ slot, Schedule (pending slot) (project slot events) (outstanding slot)

theorem schedule_effect {pending outstanding : Fin 3 → Option Nat}
    {events : List (Fin 3 × Event)} (before : DriverSchedule pending events outstanding)
    (slot : Fin 3) (event : Event) (after : Option Nat)
    (localStep : Schedule (pending slot) (project slot events ++ [event]) after) :
    DriverSchedule pending (events ++ [(slot, event)])
      (fun other => if other = slot then after else outstanding other) := by
  intro other
  by_cases same : other = slot
  · subst other
    simpa [project, List.filterMap_append] using localStep
  · simpa [project, List.filterMap_append, same, Ne.symm same] using before other

#print axioms schedule_effect
#print axioms schedule_receive
#print axioms cancelled_reply_stutters
#print axioms cancelled_schedule_witness

end Logkeeper.StreamProposer
