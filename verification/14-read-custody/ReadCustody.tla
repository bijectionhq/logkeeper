------------------------------ MODULE ReadCustody -----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Design, Mutation, Reads
VARIABLE state

Extents == 1..3
PhysicalSite(extent) == IF extent = 3 THEN 2 ELSE 1

Init ==
    state = [
        owner |-> 1,
        source_index |-> 1,
        written |-> {1},
        present |-> {1},
        open |-> TRUE,
        replay_hold |-> TRUE,
        floor |-> 0,
        reads |-> [request \in Reads |-> [phase |-> "idle", extent |-> 0]],
        source_online |-> TRUE,
        timeout |-> FALSE,
        late_admission |-> FALSE,
        late_success |-> FALSE,
        finished_after_trim |-> FALSE
    ]

CurrentExtent == IF state.owner = 2 THEN 3 ELSE state.source_index
Reachable(extent) == PhysicalSite(extent) = 2 \/ state.source_online

Build(extent) ==
    /\ extent \in {2, 3} \ state.written
    /\ state.owner = 1
    /\ state.floor = 0
    /\ CurrentExtent \in state.present
    /\ state' = [state EXCEPT !.present = @ \cup {extent}, !.written = @ \cup {extent}]

PublishCompaction ==
    /\ state.owner = 1
    /\ state.source_index = 1
    /\ 2 \in state.present
    /\ state' = [state EXCEPT !.source_index = 2]

Move ==
    /\ state.owner = 1
    /\ 3 \in state.present
    /\ state' = [state EXCEPT !.owner = 2]

Locate(request) ==
    /\ state.open
    /\ state.floor = 0
    /\ state.reads[request].phase = "idle"
    /\ CurrentExtent \in state.present
    /\ Reachable(CurrentExtent)
    /\ state' = [state EXCEPT !.reads[request] =
        [phase |-> "located", extent |-> CurrentExtent]]

Borrow(request) ==
    /\ state.reads[request].phase = "located"
    /\ state.open \/ Mutation = "admit_after_close"
    /\ state.floor = 0
    /\ LET extent == state.reads[request].extent
       IN /\ Reachable(extent)
          /\ (extent = CurrentExtent /\ extent \in state.present) \/ Mutation = "stale_lookup"
          /\ state' = [state EXCEPT !.reads[request].phase = "reading",
               !.late_admission = @ \/ ~state.open]

Complete(request) ==
    /\ state.reads[request].phase = "reading" \/
        (Mutation = "late_reply" /\ state.reads[request].phase = "fenced")
    /\ Reachable(state.reads[request].extent)
    /\ state' = [state EXCEPT !.reads[request].phase = "completed",
         !.late_success = @ \/ state.reads[request].phase = "fenced",
         !.finished_after_trim = @ \/ state.floor = 1]

CloseAdmission ==
    /\ state.open
    /\ state' = [state EXCEPT !.open = FALSE]

ObserveTimeout ==
    /\ ~state.open
    /\ ~state.timeout
    /\ state' = [state EXCEPT !.timeout = TRUE]

ConfirmFence(request) ==
    /\ ~state.open
    /\ state.reads[request].phase = "reading"
    /\ Reachable(state.reads[request].extent)
    /\ state' = [state EXCEPT !.reads[request].phase = "fenced"]

NoBorrowers == \A request \in Reads : state.reads[request].phase # "reading"

ReleaseLogicalHold ==
    /\ ~state.open
    /\ state.replay_hold
    /\ Design = "exact" \/ NoBorrowers
    /\ state' = [state EXCEPT !.replay_hold = FALSE]

Trim ==
    /\ ~state.replay_hold
    /\ state.floor = 0
    /\ state' = [state EXCEPT !.floor = 1]

IsBorrowed(extent) == \E request \in Reads :
    state.reads[request].phase = "reading" /\ state.reads[request].extent = extent

Reclaim(extent) ==
    /\ extent \in state.present
    /\ extent # CurrentExtent \/ state.floor = 1
    /\ ~IsBorrowed(extent) \/ Mutation = "logical_only" \/
        (Mutation = "timeout_is_stop" /\ state.timeout)
    /\ state' = [state EXCEPT !.present = @ \ {extent}]

LoseSource ==
    /\ state.source_online
    /\ state' = [state EXCEPT !.source_online = FALSE]

Next ==
    \/ PublishCompaction \/ Move \/ CloseAdmission \/ ObserveTimeout \/ ReleaseLogicalHold \/ Trim \/ LoseSource
    \/ \E extent \in Extents : Build(extent) \/ Reclaim(extent)
    \/ \E request \in Reads : Locate(request) \/ Borrow(request) \/ Complete(request) \/ ConfirmFence(request)

Spec == Init /\ [][Next]_state

FairSpec ==
    /\ Spec
    /\ \A request \in Reads : WF_state(ConfirmFence(request))

LiveBorrowHasBytes ==
    \A extent \in Extents : IsBorrowed(extent) => extent \in state.present

NoAdmissionAfterClose == ~state.late_admission
FencedReadCannotSucceed == ~state.late_success

DrainWithSource ==
    (<>[] state.source_online) => (~state.open ~> NoBorrowers)

DrainEvenIfSourceLost == ~state.open ~> NoBorrowers

NeverTrimsAndCompletesBorrow ==
    ~state.finished_after_trim

NeverServesOldAndNewSite ==
    ~(state.owner = 2 /\ IsBorrowed(3) /\
      \E extent \in {1, 2} : IsBorrowed(extent))
=============================================================================
