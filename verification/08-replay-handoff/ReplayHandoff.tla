--------------------------- MODULE ReplayHandoff ----------------------------
EXTENDS Naturals
CONSTANT Mutation
VARIABLE state

Init ==
    state = [
        route |-> "source",
        source_floor |-> 0,
        target_floor |-> 0,
        source_hold |-> FALSE,
        target_hold |-> FALSE,
        object_resident |-> TRUE,
        object_pin |-> FALSE,
        client |-> "idle",
        inflight |-> FALSE,
        continued |-> FALSE,
        stale_rejected |-> FALSE
    ]

Floor == IF state.route = "target" THEN state.target_floor ELSE state.source_floor
HasHold == IF state.route = "target" THEN state.target_hold ELSE state.source_hold
ReachableWriter == state.route # "sealed"

PinCheckpoint ==
    /\ state.client = "idle"
    /\ state.object_resident
    /\ state' = [state EXCEPT !.client = "opening",
        !.object_pin = Mutation # "unprotected_objects"]

RegisterReplay ==
    /\ state.client = "opening"
    /\ ReachableWriter
    /\ ~HasHold
    /\ Floor = 0
    /\ IF state.route = "target"
       THEN state' = [state EXCEPT !.target_hold = TRUE]
       ELSE state' = [state EXCEPT !.source_hold = TRUE]

RejectOutdated ==
    /\ state.client = "opening"
    /\ ReachableWriter
    /\ Floor > 0
    /\ state' = [state EXCEPT !.stale_rejected = TRUE, !.client = "draining"]

Expose ==
    /\ state.client = "opening"
    /\ HasHold
    /\ state.object_pin \/ Mutation = "unprotected_objects"
    /\ state' = [state EXCEPT !.client = "active"]

BeginRead ==
    /\ state.client = "active"
    /\ ~state.inflight
    /\ state' = [state EXCEPT !.inflight = TRUE,
        !.continued = @ \/ state.route = "target"]

EndRead ==
    /\ state.inflight
    /\ state' = [state EXCEPT !.inflight = FALSE]

CloseOrExpire ==
    /\ state.client \in {"opening", "active"}
    /\ state' = [state EXCEPT !.client = "draining"]

MayRelease ==
    state.client = "draining" /\ (~state.inflight \/ Mutation = "expire_before_drain")

ReleaseObject ==
    /\ MayRelease
    /\ state.object_pin
    /\ state' = [state EXCEPT !.object_pin = FALSE]

ReleaseTail ==
    /\ MayRelease
    /\ ReachableWriter
    /\ HasHold
    /\ IF state.route = "target"
       THEN state' = [state EXCEPT !.target_hold = FALSE]
       ELSE state' = [state EXCEPT !.source_hold = FALSE]

Finish ==
    /\ state.client = "draining"
    /\ ~state.inflight
    /\ ~state.object_pin
    /\ ~HasHold
    /\ state' = [state EXCEPT !.client = "finished"]

Trim ==
    /\ ReachableWriter
    /\ ~HasHold
    /\ Floor = 0
    /\ IF state.route = "target"
       THEN state' = [state EXCEPT !.target_floor = 1]
       ELSE state' = [state EXCEPT !.source_floor = 1]

ReapCheckpoint ==
    /\ state.object_resident
    /\ ~state.object_pin
    /\ state' = [state EXCEPT !.object_resident = FALSE]

Seal ==
    /\ state.route = "source"
    /\ state' = [state EXCEPT !.route = "sealed"]

Activate ==
    /\ state.route = "sealed"
    /\ state' = [state EXCEPT !.route = "target", !.target_floor = state.source_floor,
        !.target_hold = state.source_hold /\ Mutation # "forget_replay_hold"]

Next ==
    \/ PinCheckpoint \/ RegisterReplay \/ RejectOutdated \/ Expose \/ BeginRead \/ EndRead
    \/ CloseOrExpire \/ ReleaseObject \/ ReleaseTail \/ Finish
    \/ Trim \/ ReapCheckpoint \/ Seal \/ Activate

Spec == Init /\ [][Next]_state

NoPartialSnapshot ==
    state.client = "active" => state.object_pin /\ HasHold

OpenRangeAvailable ==
    (state.client = "active" \/ state.inflight) =>
        state.object_resident /\ Floor = 0

FinishedReleasesBoth == state.client = "finished" => ~state.object_pin /\ ~HasHold

NeverContinuesAndCloses ==
    ~(state.route = "target" /\ state.source_hold /\ state.continued /\
      state.client = "finished" /\ state.target_floor = 1 /\ ~state.object_resident)

NeverRejectsAndReleases ==
    ~(state.stale_rejected /\ state.client = "finished" /\ ~state.object_resident)
=============================================================================
