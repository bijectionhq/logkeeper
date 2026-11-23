---------------------------- MODULE ConcurrentWithdrawal ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Policy, Layout
VARIABLES physical, witnesses, pending, lost, replaced

vars == <<physical, witnesses, pending, lost, replaced>>
Copies == {"A:1", "A:2", "B:1", "B:2", "C:1"}
Zones == {"A", "B", "C"}
Zone(copy) == CASE copy \in {"A:1", "A:2"} -> "A"
                [] copy \in {"B:1", "B:2"} -> "B"
                [] OTHER -> "C"
Domains(copies) == {Zone(key) : key \in copies}
Covered(copies) == \A zone \in Zones : Domains(copies) \ {zone} # {}

Init ==
  /\ physical = CASE Layout = "same-zone" -> {"A:1", "B:1", "B:2"}
                   [] Layout = "key-reuse" -> {"A:1", "B:1", "C:1"}
                   [] OTHER -> {"A:1", "B:1", "C:1"}
  /\ witnesses = physical
  /\ pending = {}
  /\ lost = "none"
  /\ replaced = FALSE

Authorize(copy) ==
  /\ copy \in witnesses
  /\ copy \in {"A:1", "C:1"}
  /\ copy \notin pending
  /\ Covered(witnesses \ {copy}) \/
       (Policy = "count-copies" /\ Cardinality(witnesses \ {copy}) >= 2)
  /\ pending' = pending \cup {copy}
  /\ witnesses' = IF Policy = "independent-check" THEN witnesses ELSE witnesses \ {copy}
  /\ UNCHANGED <<physical, lost, replaced>>

Replacement ==
  /\ Layout = "key-reuse"
  /\ ~replaced
  /\ "A:1" \in pending
  /\ lost # "A"
  /\ physical' = (physical \ {"A:1"}) \cup {"A:2"}
  /\ witnesses' = witnesses \cup {"A:2"}
  /\ replaced' = TRUE
  /\ UNCHANGED <<pending, lost>>

Effect(copy) ==
  /\ copy \in pending
  /\ IF Policy = "delete-by-address"
       THEN physical' = {resident \in physical : Zone(resident) # Zone(copy)}
       ELSE physical' = physical \ {copy}
  /\ pending' = pending \ {copy}
  /\ witnesses' = witnesses \ {copy}
  /\ UNCHANGED <<lost, replaced>>

Lose ==
  /\ lost = "none"
  /\ \E zone \in Zones : lost' = zone
  /\ UNCHANGED <<physical, witnesses, pending, replaced>>

Next == (\E copy \in Copies : Authorize(copy) \/ Effect(copy)) \/ Replacement \/ Lose
Spec == Init /\ [][Next]_vars
StillProtected == Covered(physical)
HasWitnesses == witnesses \subseteq physical
ActualSurvivor == Domains(physical) \ {lost} # {}
NeverCompletesWithdrawal == ~(physical = {"B:1", "C:1"} /\ pending = {})

======================================================================================
