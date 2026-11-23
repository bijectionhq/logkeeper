----------------------------- MODULE ReadyTurns -----------------------------
EXTENDS Naturals

CONSTANT Variant

Jobs == 1..3
Parked == 1
Target == 2
Recurring == 3

VARIABLES cursor, active, finished
vars == <<cursor, active, finished>>

Init ==
  /\ cursor = Target
  /\ active = 0
  /\ finished = FALSE

Ready == IF finished THEN {Recurring} ELSE {Target, Recurring}
Distance(j) == IF cursor < j THEN j - cursor ELSE 3 - cursor + j
AheadInGrowingOrder(j) == j = Recurring \/ (j = Target /\ cursor = Parked)

Selected(j) ==
  CASE Variant = "race" -> TRUE
    [] Variant = "growing-order" -> AheadInGrowingOrder(j)
    [] OTHER -> \A other \in Ready : Distance(j) <= Distance(other)

Dispatch(j) ==
  /\ active = 0
  /\ j \in Ready
  /\ Selected(j)
  /\ active' = j
  /\ cursor' = j
  /\ UNCHANGED finished

Publish ==
  /\ active # 0
  /\ finished' = (finished \/ active = Target)
  /\ active' = 0
  /\ UNCHANGED cursor

Next == (\E j \in Jobs : Dispatch(j)) \/ Publish

Fair ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Publish)
  /\ \A j \in Jobs : WF_vars(Dispatch(j))

ParkedNeverOccupies == active # Parked
ReadyTargetFinishes == <>finished

=============================================================================
