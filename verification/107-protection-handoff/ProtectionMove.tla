------------------------------ MODULE ProtectionMove ------------------------------
CONSTANTS Scenario, Policy
VARIABLES phase, sourceUp, control, copies, loss, neighborSpent, acked

vars == <<phase, sourceUp, control, copies, loss, neighborSpent, acked>>
Zones == {"A", "B", "C"}
Frozen == [data |-> 7, frontier |-> 4, lineage |-> 8, start |-> 2,
           confirmed |-> IF Scenario = "spent" THEN "A" ELSE "unknown"]
Substitute == [Frozen EXCEPT !.start = 0, !.confirmed = "unknown"]
Mounted == IF Scenario = "rival-control" THEN Substitute ELSE Frozen

Init ==
  /\ phase = "source"
  /\ sourceUp = TRUE
  /\ control = Frozen
  /\ copies = IF Scenario = "spent" THEN {"B"} ELSE {"A", "B"}
  /\ loss = IF Scenario = "spent" THEN "A" ELSE "none"
  /\ neighborSpent = FALSE
  /\ acked = FALSE

Covers(placements, scenarios) == \A failed \in scenarios : placements \ {failed} # {}
InheritedCases == IF Frozen.confirmed = "unknown" THEN Zones ELSE {Frozen.confirmed}
CurrentCases == IF control.confirmed = "unknown" THEN Zones ELSE {control.confirmed}

Seal ==
  /\ phase = "source"
  /\ phase' = "sealed"
  /\ UNCHANGED <<sourceUp, control, copies, loss, neighborSpent, acked>>

Disconnect ==
  /\ phase = "sealed"
  /\ sourceUp
  /\ sourceUp' = FALSE
  /\ UNCHANGED <<phase, control, copies, loss, neighborSpent, acked>>

Mount ==
  /\ phase = "sealed"
  /\ ~sourceUp
  /\ Mounted = Frozen \/ Policy = "match-data-only"
  /\ phase' = "mounted"
  /\ control' = Mounted
  /\ UNCHANGED <<sourceUp, copies, loss, neighborSpent, acked>>

Activate ==
  /\ phase = "mounted"
  /\ "B" \in copies
  /\ Scenario # "arriving-loss" \/ loss = "A"
  /\ Covers(copies, InheritedCases)
  /\ Policy # "healthy-gate" \/ Covers(copies, Zones)
  /\ Policy # "recontact-source" \/ sourceUp
  /\ phase' = "active"
  /\ control' = IF Policy = "reset-interval"
                   THEN [control EXCEPT !.start = 5, !.confirmed = "unknown"]
                   ELSE control
  /\ neighborSpent' = (Policy = "overwrite-neighbor" /\ control.confirmed # "unknown")
  /\ UNCHANGED <<sourceUp, copies, loss, acked>>

CompleteCopy ==
  /\ Scenario = "withdrawal"
  /\ phase = "active"
  /\ loss = "none"
  /\ "C" \notin copies
  /\ copies' = copies \cup {"C"}
  /\ UNCHANGED <<phase, sourceUp, control, loss, neighborSpent, acked>>

ReleaseA ==
  /\ Scenario = "withdrawal"
  /\ phase = "active"
  /\ "A" \in copies
  /\ Covers(copies \ {"A"}, CurrentCases) \/ Policy = "release-on-activation"
  /\ copies' = copies \ {"A"}
  /\ UNCHANGED <<phase, sourceUp, control, loss, neighborSpent, acked>>

LoseB ==
  /\ Scenario = "withdrawal"
  /\ phase = "active"
  /\ loss = "none"
  /\ loss' = "B"
  /\ UNCHANGED <<phase, sourceUp, control, copies, neighborSpent, acked>>

LoseA ==
  /\ Scenario = "arriving-loss"
  /\ phase \in {"sealed", "mounted"}
  /\ loss = "none"
  /\ loss' = "A"
  /\ UNCHANGED <<phase, sourceUp, control, copies, neighborSpent, acked>>

ApplyConfirmation ==
  /\ Scenario = "arriving-loss"
  /\ phase = "active"
  /\ control.start = Frozen.start
  /\ control.confirmed = "unknown"
  /\ loss = "A"
  /\ control' = [control EXCEPT !.confirmed = "A"]
  /\ UNCHANGED <<phase, sourceUp, copies, loss, neighborSpent, acked>>

AckBOnly ==
  /\ phase = "active"
  /\ ~acked
  /\ control.confirmed = "A"
  /\ acked' = TRUE
  /\ UNCHANGED <<phase, sourceUp, control, copies, loss, neighborSpent>>

Next == Seal \/ Disconnect \/ Mount \/ Activate \/ CompleteCopy \/ ReleaseA \/
        LoseB \/ LoseA \/ ApplyConfirmation \/ AckBOnly
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Seal) /\ WF_vars(Disconnect) /\ WF_vars(Mount) /\ WF_vars(Activate) /\
               WF_vars(LoseA) /\ WF_vars(ApplyConfirmation) /\ WF_vars(AckBOnly)
KeepsInterval == phase = "active" =>
  /\ control.start = Frozen.start
  /\ control.lineage = Frozen.lineage
  /\ IF Scenario = "arriving-loss" THEN control.confirmed \in {Frozen.confirmed, "A"}
       ELSE control.confirmed = Frozen.confirmed
LeavesNeighbor == ~neighborSpent
Survives == copies \ {loss} # {}
ServesExistingInterval == <>acked
NeverSafelyReleases == ~(copies = {"B", "C"} /\ loss = "B")
==================================================================================
