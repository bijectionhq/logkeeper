------------------------------- MODULE Permits -------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Mutation, MaxPermit
VARIABLE state

Ids == 1..MaxPermit
Lsn == 0..1
NoTicket == [phase |-> "unused", first |-> 0]
Requests == [id : Ids, first : Lsn]

Init ==
    state = [
        owner |-> "source",
        high_water |-> 0,
        tickets |-> [id \in Ids |-> NoTicket],
        envelopes |-> {},
        prepared_at_seal |-> {},
        acknowledged_closed |-> {},
        released_first_record |-> {},
        closed_pending |-> {},
        refused_first |-> 2,
        promised_holds |-> {},
        floor |-> 0,
        admitted_after_move |-> FALSE
    ]

CanDecide == state.owner # "sealed"

Prepare(first) ==
    /\ CanDecide
    /\ state.high_water < MaxPermit
    /\ LET id == state.high_water + 1
       IN state' = [state EXCEPT !.high_water = id,
                     !.tickets[id] = [phase |-> "prepared", first |-> first],
                     !.envelopes = @ \cup {[id |-> id, first |-> first]}]

Admit(request) ==
    /\ CanDecide
    /\ request \in state.envelopes
    /\ state.floor <= request.first
    /\ (state.tickets[request.id] = [phase |-> "prepared", first |-> request.first] \/
        Mutation = "trust_old_envelope")
    /\ state' = [state EXCEPT
        !.tickets[request.id] = [phase |-> "holding", first |-> request.first],
        !.promised_holds = @ \cup {request},
        !.admitted_after_move = @ \/ (state.owner = "target" /\ request \in state.prepared_at_seal)]

Close(id) ==
    /\ CanDecide
    /\ id <= state.high_water
    /\ id \notin state.acknowledged_closed
    /\ state' = [state EXCEPT !.acknowledged_closed = @ \cup {id},
        !.closed_pending = IF state.owner = "source" /\ state.tickets[id].phase = "prepared"
                           THEN @ \cup {id} ELSE @,
        !.released_first_record = IF state.tickets[id] = [phase |-> "holding", first |-> 0]
                                 THEN @ \cup {id} ELSE @,
        !.promised_holds = {request \in @ : request.id # id},
        !.tickets = [entry \in Ids |->
            IF entry = id \/ (Mutation = "close_range" /\ @[entry].first = @[id].first)
            THEN NoTicket ELSE @[entry]]]

RejectClosed(request) ==
    /\ state.owner = "target"
    /\ request \in state.envelopes
    /\ request.id \in state.closed_pending
    /\ request.id <= state.high_water
    /\ state.tickets[request.id] = NoTicket
    /\ state.refused_first = 2
    /\ state' = [state EXCEPT !.refused_first = request.first]

Trim ==
    /\ CanDecide
    /\ state.floor = 0
    /\ \A id \in Ids :
         (state.tickets[id].phase = "holding" /\
          (Mutation # "check_latest_only" \/ id = state.high_water)) => state.tickets[id].first >= 1
    /\ state' = [state EXCEPT !.floor = 1]

Seal ==
    /\ state.owner = "source"
    /\ state' = [state EXCEPT !.owner = "sealed",
        !.prepared_at_seal = {request \in state.envelopes : state.tickets[request.id].phase = "prepared"}]

Install ==
    /\ state.owner = "sealed"
    /\ state' = [state EXCEPT !.owner = "target",
        !.high_water = IF Mutation = "forget_issued" THEN 0 ELSE @,
        !.tickets = IF Mutation = "forget_pending"
                    THEN [id \in Ids |-> IF @[id].phase = "prepared" THEN NoTicket ELSE @[id]]
                    ELSE @]

Next ==
    \/ Seal \/ Install \/ Trim
    \/ \E first \in Lsn : Prepare(first)
    \/ \E request \in Requests : Admit(request) \/ RejectClosed(request)
    \/ \E id \in Ids : Close(id)

Spec == Init /\ [][Next]_state

ClosedStaysClosed ==
    \A id \in state.acknowledged_closed : state.tickets[id] = NoTicket

PromisesPreserved ==
    \A request \in state.promised_holds :
        state.tickets[request.id] = [phase |-> "holding", first |-> request.first]

EveryHoldCovered ==
    \A request \in state.promised_holds : state.floor <= request.first

ReservationsTransfer ==
    \A request \in state.envelopes :
        request.id \notin state.acknowledged_closed /\ request \notin state.promised_holds =>
        state.tickets[request.id] = [phase |-> "prepared", first |-> request.first]

NeverClosesOneAndContinuesAnotherAfterMove ==
    ~(state.owner = "target" /\ state.admitted_after_move /\ 1 \in state.released_first_record /\
      state.tickets[2].phase = "holding" /\ state.floor = 1)
NeverRefusesOnePendingAndKeepsAnother ==
    ~(state.refused_first \in Lsn /\
      \E id \in Ids : state.tickets[id] = [phase |-> "holding", first |-> state.refused_first])

=============================================================================
