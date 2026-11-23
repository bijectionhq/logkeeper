------------------------------- MODULE ConcurrentLedger -------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Capacity, Variant, Scenario
VARIABLE s

Moves == 1..2
Zones == 1..2
Needs(move, zone) ==
    IF Scenario = "skew" THEN 2 ELSE IF move = zone THEN 2 ELSE 1
Obsolete(move, zone) == IF move = zone THEN 1 ELSE 0
Resident(move, zone) == Needs(move, zone) - Obsolete(move, zone)
AtCapacity(zone) == s.ordinary[zone] + s.charges[1][zone] + s.charges[2][zone]
CompleteVector(move) == \A zone \in Zones : s.charges[move][zone] = Needs(move, zone)

Init ==
    s = [ordinary |-> [zone \in Zones |-> IF Scenario = "skew" /\ zone = 1 THEN Capacity - 1 ELSE 0],
         charges |-> [move \in Moves |-> [zone \in Zones |-> 0]],
         phase |-> [move \in Moves |-> "idle"],
         disposed |-> [move \in Moves |-> {}], restarted |-> FALSE,
         restartedAtFullSeal |-> FALSE, wrongEffect |-> FALSE]

Fill(zone) ==
    /\ Scenario # "skew" /\ AtCapacity(zone) < Capacity
    /\ s' = [s EXCEPT !.ordinary[zone] = @ + 1]

Reserve(move) ==
    /\ s.phase[move] = "idle"
    /\ IF Variant = "total_only"
       THEN AtCapacity(1) + AtCapacity(2) + Needs(move, 1) + Needs(move, 2) <= 2 * Capacity
       ELSE \A zone \in Zones : AtCapacity(zone) + Needs(move, zone) <= Capacity
    /\ s' = [s EXCEPT !.phase[move] = "funded",
                     !.charges[move] = [zone \in Zones |-> Needs(move, zone)]]

Abort(move) ==
    /\ s.phase[move] = "funded" \/ (Variant = "timeout_revokes_sealed" /\ s.phase[move] = "sealed")
    /\ s' = [s EXCEPT !.phase[move] = IF @ = "sealed" THEN @ ELSE "aborted",
                     !.charges[move] = [zone \in Zones |-> 0]]

Seal(move) ==
    /\ s.phase[move] = "funded" /\ CompleteVector(move)
    /\ s' = [s EXCEPT !.phase[move] = "sealed"]

Promote(move) ==
    /\ s.phase[move] = "sealed" /\ CompleteVector(move)
    /\ Variant # "rebill_promotion" \/ \A zone \in Zones : AtCapacity(zone) + Resident(move, zone) <= Capacity
    /\ s' = [s EXCEPT !.phase[move] = "installed",
        !.charges[move] = IF Variant = "drop_retained_charge" THEN [zone \in Zones |-> Resident(move, zone)] ELSE @]

Dispose(move, zone) ==
    /\ s.phase[move] = "installed" /\ zone \notin s.disposed[move]
    /\ Scenario # "custodian_down"
    /\ s' = [s EXCEPT !.disposed[move] = @ \cup {zone}]

FullWithOrdinaryTraffic ==
    \A zone \in Zones : AtCapacity(zone) = Capacity /\ s.ordinary[zone] > 0

Release(move, zone, proofOwner) ==
    /\ s.phase[move] = "installed" /\ s.charges[move][zone] > Resident(move, zone)
    /\ zone \in s.disposed[proofOwner]
    /\ proofOwner = move \/ Variant = "release_by_route"
    /\ s' = [s EXCEPT !.charges[move][zone] = Resident(move, zone),
                     !.wrongEffect = @ \/ proofOwner # move]

Restart ==
    /\ ~s.restarted
    /\ s' = [s EXCEPT !.restarted = TRUE,
         !.restartedAtFullSeal = Scenario = "custodian_down" /\ FullWithOrdinaryTraffic /\
             (\A move \in Moves : s.phase[move] = "sealed"),
         !.charges = IF Variant = "forget_charges" THEN [move \in Moves |-> [zone \in Zones |-> 0]] ELSE @]

Next ==
    \/ Restart \/ \E zone \in Zones : Fill(zone)
    \/ \E move \in Moves : Reserve(move) \/ Abort(move) \/ Seal(move) \/ Promote(move)
    \/ \E move \in Moves, zone \in Zones : Dispose(move, zone)
    \/ \E move \in Moves, zone \in Zones, proofOwner \in Moves : Release(move, zone, proofOwner)

Spec == Init /\ [][Next]_s
Fair == Spec /\ \A move \in Moves : WF_s(Promote(move))

BoundsEachZone == \A zone \in Zones : AtCapacity(zone) <= Capacity
UnreleasedSealIsFullyFunded == \A move \in Moves : s.phase[move] \in {"funded", "sealed"} => CompleteVector(move)
RetainsExactCharges ==
    \A move \in Moves : s.phase[move] = "installed" =>
        \A zone \in Zones : s.charges[move][zone] >= Resident(move, zone) +
            (IF zone \in s.disposed[move] THEN 0 ELSE Obsolete(move, zone))
ReleaseStaysInScope == ~s.wrongEffect

SealsFinish == \A move \in Moves : (s.phase[move] = "sealed") ~> (s.phase[move] = "installed")
NeverInstallsBothAtCapacity ==
    ~((\A move \in Moves : s.phase[move] = "installed" /\ s.disposed[move] = {}) /\
      FullWithOrdinaryTraffic /\ s.restartedAtFullSeal)
NeverReleasesExactObsolete ==
    ~(s.phase[1] = "installed" /\ 1 \in s.disposed[1] /\ s.charges[1][1] = Resident(1, 1))
=============================================================================
