---------------------------- MODULE PoolEvacuation ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Limit, Scenario, Variant

Pools == 1..4
Zones == 1..3
Zone(p) == IF p = 4 THEN 2 ELSE p
Original == 1
Survivor == 2
Replacement == 3
CoLocated == 4

VARIABLES down, placement, booked, pending, landed, wrong, verified, ordinary,
          borrowed, released, drained

vars == <<down, placement, booked, pending, landed, wrong, verified, ordinary,
          borrowed, released, drained>>

Online(p) == Zone(p) # down
Used(p) == ordinary[p] + (IF p \in booked THEN 1 ELSE 0)
Eligible == {p \in placement \cap verified : Online(p)}
ExactServing == {p \in placement \cap (landed \ wrong) \cap booked : Online(p)}
DomainProtected(copies) == \A z \in Zones : \E p \in copies : Zone(p) # z
CanAdvertise ==
    IF Variant = "count_pools" THEN Cardinality(Eligible) >= 2
    ELSE DomainProtected(Eligible)

Init ==
    /\ down = IF Scenario = "repair" THEN 1 ELSE 0
    /\ placement = {Original, Survivor}
    /\ booked = placement
    /\ pending = {} /\ landed = placement /\ wrong = {} /\ verified = placement
    /\ ordinary = [p \in Pools |-> IF Scenario = "saturated" /\ p = Replacement THEN Limit ELSE 0]
    /\ borrowed = FALSE /\ released = {} /\ drained = FALSE

Fill(p) ==
    /\ Online(p) /\ Used(p) < Limit /\ Scenario = "general"
    /\ ordinary' = [ordinary EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<down, placement, booked, pending, landed, wrong, verified,
                   borrowed, released, drained>>

Fault(z) ==
    /\ down = 0 /\ z \in Zones
    /\ down' = z
    /\ booked' = IF Variant = "release_on_failure" THEN {p \in booked : Zone(p) # z} ELSE booked
    /\ UNCHANGED <<placement, pending, landed, wrong, verified, ordinary, borrowed, released, drained>>

Reserve(p) ==
    /\ Online(p) /\ p \notin booked \cup released
    /\ Scenario # "outage_witness" \/ ~Online(Original)
    /\ \/ Used(p) < Limit
       \/ Variant = "use_offline_credit" /\ ~Online(Original) /\ Original \in booked
    /\ booked' = booked \cup {p}
    /\ pending' = pending \cup {p}
    /\ UNCHANGED <<down, placement, landed, wrong, verified, ordinary, borrowed, released, drained>>

Land(p, exact) ==
    /\ Online(p) /\ p \in pending
    /\ Eligible # {}
    /\ pending' = pending \ {p}
    /\ landed' = landed \cup {p}
    /\ wrong' = IF exact THEN wrong ELSE wrong \cup {p}
    /\ UNCHANGED <<down, placement, booked, verified, ordinary, borrowed, released, drained>>

Verify(p) ==
    /\ Online(p) /\ p \in (landed \ verified) \cap booked
    /\ p \notin wrong \/ Variant = "unbound_receipt"
    /\ verified' = verified \cup {p}
    /\ UNCHANGED <<down, placement, booked, pending, landed, wrong, ordinary, borrowed, released, drained>>

Join(p) ==
    /\ Online(p) /\ p \in verified \ placement
    /\ placement' = placement \cup {p}
    /\ UNCHANGED <<down, booked, pending, landed, wrong, verified, ordinary, borrowed, released, drained>>

Evacuate ==
    /\ Original \in placement
    /\ \/ DomainProtected(Eligible \ {Original})
       \/ Variant = "weak_planned_cut" /\ (Eligible \ {Original}) # {}
    /\ Variant # "wait_for_old" \/ Online(Original)
    /\ placement' = placement \ {Original}
    /\ drained' = DomainProtected(Eligible \ {Original})
    /\ UNCHANGED <<down, booked, pending, landed, wrong, verified, ordinary, borrowed, released>>

Borrow ==
    /\ Original \in Eligible /\ ~borrowed
    /\ borrowed' = TRUE
    /\ UNCHANGED <<down, placement, booked, pending, landed, wrong, verified, ordinary, released, drained>>

Finish ==
    /\ borrowed /\ Online(Original)
    /\ borrowed' = FALSE
    /\ UNCHANGED <<down, placement, booked, pending, landed, wrong, verified, ordinary, released, drained>>

Dispose ==
    /\ Original \in booked \ placement /\ Online(Original) /\ ~borrowed
    /\ released' = released \cup {Original}
    /\ booked' = booked \ {Original}
    /\ landed' = landed \ {Original}
    /\ verified' = verified \ {Original}
    /\ UNCHANGED <<down, placement, pending, wrong, ordinary, borrowed, drained>>

Targets == IF Scenario = "repair" THEN {Replacement} ELSE {Replacement, CoLocated}
Next ==
    \/ \E p \in Pools : Fill(p)
    \/ \E z \in Zones : Fault(z)
    \/ \E p \in Targets : Reserve(p) \/ Land(p, TRUE) \/ Verify(p) \/ Join(p)
    \/ Scenario # "repair" /\ \E p \in Targets : Land(p, FALSE)
    \/ Evacuate \/ Borrow \/ Finish \/ Dispose

Spec == Init /\ [][Next]_vars
FairSpec ==
    Spec
    /\ WF_vars(Reserve(Replacement)) /\ WF_vars(Land(Replacement, TRUE))
    /\ WF_vars(Verify(Replacement)) /\ WF_vars(Join(Replacement))
    /\ WF_vars(Evacuate)

PointwiseBudget == \A p \in Pools : Used(p) <= Limit
UnsettledCharged == landed \cup pending \subseteq booked
ServingExact == Eligible = ExactServing
RecoverableAfterFault == ExactServing # {}
AdvertisesExactProtection == CanAdvertise => DomainProtected(ExactServing)
PreservesPlannedEnvelope == Original \notin placement => drained
OldBorrowCovered ==
    borrowed => Original \in (landed \ wrong) \cap booked /\ Original \notin released
Repaired == <> (Replacement \in Eligible /\ Original \notin placement)

NeverRepairWithOldBorrow ==
    ~(~Online(Original) /\ borrowed /\ Original \in booked \ placement
      /\ Replacement \in Eligible /\ CanAdvertise)
NeverDisposeAfterWithdrawal == released = {}
NeverServeCoLocatedDegraded ==
    ~(~Online(Original) /\ Eligible = {Survivor, CoLocated} /\ ~CanAdvertise)
NeverBookSaturatedReplacement == Replacement \notin booked
=============================================================================
