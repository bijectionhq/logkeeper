--------------------------- MODULE CapacityOwnership ---------------------------
EXTENDS Naturals

CONSTANTS Ownership, Schedule, Weakening
VARIABLES holds, ready, active, pinned

Pools == {"left", "right"}
Moves == {"out", "back"}
Demand(move, pool) ==
    IF (move = "out" /\ pool = "left") \/ (move = "back" /\ pool = "right")
    THEN 2 ELSE 1

BaseUsage == 1
Capacity == 4
PinCharge(pool) == IF pinned /\ pool = "left" THEN 1 ELSE 0
HeldUsage(pool) ==
    (IF pool \in holds["out"] THEN Demand("out", pool) ELSE 0) +
    (IF pool \in holds["back"] THEN Demand("back", pool) ELSE 0)
PhysicalUsage(pool) == BaseUsage + PinCharge(pool) + HeldUsage(pool)
AdmittedUsage(pool) ==
    BaseUsage + (IF Weakening = "ignore-pin" THEN 0 ELSE PinCharge(pool)) +
    HeldUsage(pool)
Fits(move, pool) == AdmittedUsage(pool) + Demand(move, pool) <= Capacity

CoordinatorUp == Schedule \in {"pin-releases", "pin-holds"}
SourceUp(move) == move = "back" \/
    Schedule \in {"pin-releases", "pin-holds", "coordinator-lost-first"}

Init ==
    /\ holds = [move \in Moves |->
        IF move = "out" /\ Schedule \in {"lost-before-certificate", "lost-after-certificate"}
        THEN Pools ELSE {}]
    /\ ready = IF Schedule = "lost-after-certificate" THEN {"out"} ELSE {}
    /\ active = {}
    /\ pinned = TRUE

Reserve(move) ==
    /\ Ownership = "vector"
    /\ CoordinatorUp
    /\ holds[move] = {}
    /\ \A pool \in Pools : Fits(move, pool)
    /\ holds' = [holds EXCEPT ![move] = Pools]
    /\ UNCHANGED <<ready, active, pinned>>

Prepare(move, pool) ==
    /\ Ownership = "local"
    /\ pool \notin holds[move]
    /\ pool = "left" \/ "left" \in holds[move]
    /\ Fits(move, pool)
    /\ holds' = [holds EXCEPT ![move] = @ \cup {pool}]
    /\ UNCHANGED <<ready, active, pinned>>

InstallCertificate(move) ==
    /\ move \notin ready
    /\ holds[move] = Pools
    /\ SourceUp(move)
    /\ ready' = ready \cup {move}
    /\ UNCHANGED <<holds, active, pinned>>

Activate(move) ==
    /\ move \notin active
    /\ IF Weakening = "use-holds"
       THEN holds[move] = Pools
       ELSE move \in ready
    /\ Weakening # "recontact" \/ (CoordinatorUp /\ SourceUp(move))
    /\ active' = active \cup {move}
    /\ UNCHANGED <<holds, ready, pinned>>

DisposeOriginalPin ==
    /\ Schedule = "pin-releases"
    /\ pinned
    /\ pinned' = FALSE
    /\ UNCHANGED <<holds, ready, active>>

Next ==
    \/ \E move \in Moves :
          Reserve(move) \/ InstallCertificate(move) \/ Activate(move) \/
          (\E pool \in Pools : Prepare(move, pool))
    \/ DisposeOriginalPin

Vars == <<holds, ready, active, pinned>>
Spec ==
    /\ Init
    /\ [][Next]_Vars
    /\ WF_Vars(DisposeOriginalPin)
    /\ \A move \in Moves :
        /\ WF_Vars(Reserve(move))
        /\ WF_Vars(InstallCertificate(move))
        /\ WF_Vars(Activate(move))
        /\ \A pool \in Pools : WF_Vars(Prepare(move, pool))

PointwiseCapacity == \A pool \in Pools : PhysicalUsage(pool) <= Capacity
ExactInstall ==
    /\ active \subseteq ready
    /\ \A move \in ready : holds[move] = Pools
CannotActivateOut == "out" \notin active
CannotActivateBothWhilePinned == pinned => active # Moves
BothEventuallyActive == <>(active = Moves)
SomeEventuallyActive == <>(active # {})
OutEventuallyActive == <>("out" \in active)
=============================================================================
