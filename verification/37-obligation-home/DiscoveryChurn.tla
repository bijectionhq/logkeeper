------------------------------ MODULE DiscoveryChurn -----------------------------
VARIABLES fresh, finished

variables == <<fresh, finished>>
Init == fresh = FALSE /\ finished = FALSE

Refresh == ~fresh /\ ~finished /\ fresh' = TRUE /\ UNCHANGED finished
Move == fresh /\ ~finished /\ fresh' = FALSE /\ UNCHANGED finished
Deliver == fresh /\ ~finished /\ finished' = TRUE /\ UNCHANGED fresh
Next == Refresh \/ Move \/ Deliver

Spec == Init /\ [][Next]_variables
WeakDelivery == Spec /\ WF_variables(Refresh) /\ WF_variables(Deliver)
FairDelivery == Spec /\ WF_variables(Refresh) /\ SF_variables(Deliver)
Complete == <> finished
=============================================================================
