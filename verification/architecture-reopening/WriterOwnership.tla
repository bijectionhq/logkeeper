---------------------------- MODULE WriterOwnership ----------------------------
CONSTANTS Ownership, WitnessUp, Weakening
VARIABLES phase, receipt, cut

\* The chosen append is protected at cut 1. A rival durably staged at 2 has no decision.
ChosenCut == 1
StagedCut == 2
DecisionReachable == Ownership = "group" \/ WitnessUp

Init ==
    /\ phase = "old"
    /\ receipt = 0
    /\ cut = 0

Grant ==
    /\ phase = "old"
    /\ DecisionReachable
    /\ phase' = "granted"
    /\ UNCHANGED <<receipt, cut>>

Apply ==
    /\ phase = "granted"
    /\ phase' = "caught-up"
    /\ receipt' = IF Weakening = "stage-is-choice" THEN StagedCut ELSE ChosenCut
    /\ cut' = receipt'

Barrier ==
    /\ phase = "caught-up"
    /\ DecisionReachable
    /\ phase' = "served"
    /\ UNCHANGED <<receipt, cut>>

Next == Grant \/ Apply \/ Barrier
Vars == <<phase, receipt, cut>>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Grant) /\ WF_Vars(Apply) /\ WF_Vars(Barrier)

ExactResult == phase \in {"caught-up", "served"} => /\ receipt = ChosenCut /\ cut = ChosenCut
Service == <>(phase = "served")
=============================================================================
