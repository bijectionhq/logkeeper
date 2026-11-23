--------------------------- MODULE DegradedEvidence -------------------------
EXTENDS Naturals

CONSTANTS World, Policy, OwnerApproved, InputsAvailable

Responding == {2, 3}
Missing == 1
PhysicallyUnavailable == IF World = "failed" THEN {Missing} ELSE {}
LocalEvidence == [responders |-> Responding, currentScope |-> 1, exactInputs |-> InputsAvailable]
Ready == LocalEvidence.responders = Responding /\ LocalEvidence.exactInputs

VARIABLES mode, diagnosis, served
vars == <<mode, diagnosis, served>>

Init ==
  /\ mode = "unselected"
  /\ diagnosis = 0
  /\ served = FALSE

Enter ==
  /\ mode = "unselected"
  /\ (Ready \/ Policy = "ignore-inputs")
  /\ CASE Policy = "infer-failure" ->
            /\ mode' = "degraded"
            /\ diagnosis' = Missing
        [] Policy \in {"ordered-exclusion", "ignore-inputs"} ->
            /\ OwnerApproved
            /\ mode' = "degraded"
            /\ diagnosis' = 0
        [] OTHER -> FALSE
  /\ UNCHANGED served

Admit ==
  /\ mode = "degraded"
  /\ ~served
  /\ served' = TRUE
  /\ UNCHANGED <<mode, diagnosis>>

Next == Enter \/ Admit
Fair == Init /\ [][Next]_vars /\ WF_vars(Enter) /\ WF_vars(Admit)

NoFalseDiagnosis == diagnosis = 0 \/ diagnosis \in PhysicallyUnavailable
AuthorizedMode == mode = "unselected" \/ OwnerApproved \/ diagnosis \in PhysicallyUnavailable
ServesWithExactInputs == served => Ready
EventuallyServes == <>served

=============================================================================
