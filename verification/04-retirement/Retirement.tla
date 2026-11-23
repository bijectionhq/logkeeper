----------------------------- MODULE Retirement ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Locations, Mutation
VARIABLE state

Init ==
    state = [
        closed |-> FALSE,
        complete |-> FALSE,
        inventory |-> {1},
        queued |-> {},
        resident |-> {1},
        fenced |-> {},
        acknowledged |-> {},
        online |-> Locations
    ]

Reserve(location) ==
    /\ ~state.closed
    /\ location \notin state.inventory \cup state.queued
    /\ state' = [state EXCEPT
        !.inventory = IF Mutation = "unrecorded_copy" THEN @ ELSE @ \cup {location},
        !.queued = @ \cup {location}]

Deliver(location) ==
    /\ location \in state.queued \cap state.online
    /\ location \notin state.fenced
    /\ state' = [state EXCEPT !.queued = @ \ {location}, !.resident = @ \cup {location}]

Retire ==
    /\ ~state.closed
    /\ state' = [state EXCEPT !.closed = TRUE]

Fence(location) ==
    /\ state.closed
    /\ location \in (state.inventory \cap state.online) \ state.fenced
    /\ state' = [state EXCEPT !.fenced = @ \cup {location}]

Erase(location) ==
    /\ state.closed
    /\ location \in (state.inventory \cap state.online) \ state.acknowledged
    /\ location \in state.fenced \/ Mutation = "absence_only"
    /\ state' = [state EXCEPT !.resident = @ \ {location},
        !.acknowledged = @ \cup {location}]

Complete ==
    /\ state.closed
    /\ ~state.complete
    /\ (state.acknowledged = state.inventory \/
        (Mutation = "only_majority" /\ Cardinality(state.acknowledged) >= 2))
    /\ state' = [state EXCEPT !.complete = TRUE]

ForgetFence(location) ==
    /\ Mutation = "forget_fence"
    /\ state.complete
    /\ location \in state.fenced
    /\ state' = [state EXCEPT !.fenced = @ \ {location}]

ToggleOnline(location) ==
    state' = [state EXCEPT !.online =
        IF location \in @ THEN @ \ {location} ELSE @ \cup {location}]

Next ==
    \/ Retire \/ Complete
    \/ \E location \in Locations :
        Reserve(location) \/ Deliver(location) \/ Fence(location) \/ Erase(location) \/
        ForgetFence(location) \/ ToggleOnline(location)

Spec == Init /\ [][Next]_state

FairSpec ==
    /\ Spec
    /\ WF_state(Complete)
    /\ \A location \in Locations : WF_state(Fence(location)) /\ WF_state(Erase(location))

CustodyKnown == state.resident \cup state.queued \subseteq state.inventory
ErasureStable == state.complete => (state.closed /\ state.resident = {})
AllAcknowledged == state.complete => state.acknowledged = state.inventory

ProgressWithAccess ==
    (<>[] (state.closed /\ state.inventory \subseteq state.online)) => <>state.complete

ProgressWithMajority ==
    (<>[] (state.closed /\ Cardinality(state.online) = Cardinality(Locations) - 1)) =>
        <>state.complete

NeverFinishesWithLatePacket ==
    ~(state.complete /\ state.queued # {} /\ state.queued \subseteq state.fenced)
=============================================================================
