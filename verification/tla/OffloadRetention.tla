--------------------------- MODULE OffloadRetention ---------------------------
EXTENDS Naturals

CONSTANTS A, B, GateStoreRead, RecheckFloor

Voters == {A, B}
Records == [i \in 1..3 |-> IF i = 1 THEN "first" ELSE IF i = 2 THEN "second" ELSE "third"]

VARIABLES leader, moved, uploaded, offloaded, trimmed, applied, local, storeUp, read

vars == <<leader, moved, uploaded, offloaded, trimmed, applied, local, storeUp, read>>
authority == <<leader, moved>>
storage == <<uploaded, offloaded, trimmed, applied, local, storeUp>>

Init ==
    /\ leader = A /\ moved = FALSE
    /\ uploaded = 0 /\ offloaded = 0 /\ trimmed = 1
    /\ applied = [p \in Voters |-> 1] /\ local = applied
    /\ storeUp \in BOOLEAN
    /\ read = [step |-> "idle", at |-> 1, keeper |-> A, invokedFloor |-> 1,
                barrierFloor |-> 0, plannedApplied |-> 1, answer |-> "none"]

Migrate ==
    /\ ~moved /\ leader' = B /\ moved' = TRUE
    /\ UNCHANGED <<storage, read>>

RestoreStore ==
    /\ ~storeUp /\ storeUp' = TRUE
    /\ UNCHANGED <<authority, uploaded, offloaded, trimmed, applied, local, read>>

Upload ==
    /\ storeUp /\ uploaded < 2 /\ uploaded' = uploaded + 1
    /\ UNCHANGED <<authority, offloaded, trimmed, applied, local, storeUp, read>>

Publish ==
    /\ offloaded < uploaded /\ offloaded' = uploaded
    /\ UNCHANGED <<authority, uploaded, trimmed, applied, local, storeUp, read>>

Retain(p) ==
    /\ local[p] < offloaded + 1
    /\ local' = [local EXCEPT ![p] = offloaded + 1]
    /\ UNCHANGED <<authority, uploaded, offloaded, trimmed, applied, storeUp, read>>

CommitTrim ==
    /\ trimmed < 3 /\ trimmed' = trimmed + 1
    /\ UNCHANGED <<authority, uploaded, offloaded, applied, local, storeUp, read>>

ApplyTrim(p) ==
    /\ applied[p] < trimmed /\ applied' = [applied EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<authority, uploaded, offloaded, trimmed, local, storeUp, read>>

RemoteAt(p, at) == applied[p] <= at /\ at < local[p]

Invoke ==
    /\ read.step = "idle"
    /\ \E p \in Voters, at \in 1..2:
        /\ RemoteAt(p, at)
        /\ read' = [read EXCEPT !.step = "routed", !.keeper = p, !.at = at,
                                  !.invokedFloor = trimmed]
    /\ UNCHANGED <<authority, storage>>

(* Capture the committed trim cut for this read and await its application.
   A follower or unsuccessful barrier returns Unavailable for client retry. *)
Barrier ==
    /\ read.step = "routed"
    /\ read' = IF ~GateStoreRead
               THEN [read EXCEPT !.step = "passed"]
               ELSE IF read.keeper = leader
                    THEN [read EXCEPT !.step = "waiting", !.barrierFloor = trimmed]
                    ELSE [read EXCEPT !.step = "done", !.answer = "unavailable"]
    /\ UNCHANGED <<authority, storage>>

CompleteBarrier ==
    /\ read.step = "waiting"
    /\ read' = IF read.keeper # leader
               THEN [read EXCEPT !.step = "done", !.answer = "unavailable"]
               ELSE IF applied[read.keeper] >= read.barrierFloor
                    THEN [read EXCEPT !.step = "passed"]
                    ELSE read
    /\ UNCHANGED <<authority, storage>>

(* Reading a descriptor is the last synchronized floor observation.
   Trims that overlap object I/O can linearize after that observation. *)
Plan ==
    /\ read.step = "passed"
    /\ read' = IF ~RecheckFloor \/ RemoteAt(read.keeper, read.at)
               THEN [read EXCEPT !.step = "fetch", !.plannedApplied = applied[read.keeper]]
               ELSE [read EXCEPT !.step = "done", !.answer = "trimmed"]
    /\ UNCHANGED <<authority, storage>>

Fetch ==
    /\ read.step = "fetch"
    /\ read' = [read EXCEPT !.step = "done",
             !.answer = IF storeUp /\ read.at <= uploaded THEN Records[read.at] ELSE "unavailable"]
    /\ UNCHANGED <<authority, storage>>

Next ==
    \/ Migrate \/ RestoreStore \/ Upload \/ Publish \/ CommitTrim
    \/ Invoke \/ Barrier \/ CompleteBarrier \/ Plan \/ Fetch
    \/ \E p \in Voters: Retain(p) \/ ApplyTrim(p)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Barrier) /\ WF_vars(CompleteBarrier) /\ WF_vars(Plan) /\ WF_vars(Fetch)
    /\ \A p \in Voters: WF_vars(ApplyTrim(p))

IsObjectAnswer == read.answer \in {Records[i] : i \in DOMAIN Records}
RetentionCovered == \A p \in Voters: local[p] - 1 <= offloaded /\ offloaded <= uploaded
RemoteReadHadBarrier == IsObjectAnswer => read.barrierFloor >= read.invokedFloor
NoPostTrimRemoteRead == IsObjectAnswer => read.at >= read.invokedFloor
RemoteRechecksFloor == IsObjectAnswer => read.at >= read.plannedApplied
RemoteReturnsExactBytes == IsObjectAnswer => read.answer = Records[read.at]
RemoteRequestSettles == (read.step # "idle") ~> (read.step = "done")

=============================================================================
