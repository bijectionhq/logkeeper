---------------------------- MODULE LatePrepare -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant
Keys == {1, 2}

VARIABLES source, aborted, row, held, charged, io, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor
vars == <<source, aborted, row, held, charged, io, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Init ==
    /\ source = [k \in Keys |-> "unissued"]
    /\ io = [k \in Keys |-> "none"]
    /\ aborted = {} /\ row = {} /\ held = {} /\ charged = {}
    /\ retained = {} /\ fenced = {} /\ floor = 0 /\ ack = {}
    /\ owner = 0 /\ late = {} /\ startedClosed = {} /\ takeoverFloor = 0

Closed(k) == k <= floor \/ k \in fenced

Plan(k) ==
    /\ source[k] = "unissued"
    /\ k = 1 \/ (source[1] = "aborted" /\ 1 \notin row)
    /\ source' = [source EXCEPT ![k] = "pending"] /\ row' = row \cup {k}
    /\ UNCHANGED <<aborted, held, charged, io, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Prepare(k) ==
    /\ source[k] \in {"pending", "aborted"}
    /\ k \notin held \cup charged /\ Cardinality(charged) < 1
    /\ (~Closed(k) \/ (Variant = "ignore_floor" /\ k \notin fenced))
    /\ held' = held \cup {k} /\ charged' = charged \cup {k}
    /\ io' = [io EXCEPT ![k] = "open"]
    /\ late' = IF k \in aborted THEN late \cup {k} ELSE late
    /\ UNCHANGED <<source, aborted, row, retained, fenced, floor, ack, owner, startedClosed, takeoverFloor>>

Abort(k) ==
    /\ source[k] = "pending"
    /\ source' = [source EXCEPT ![k] = "aborted"] /\ aborted' = aborted \cup {k}
    /\ UNCHANGED <<row, held, charged, io, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Seal(k) ==
    /\ k \in held
    /\ source[k] = "pending" \/ (Variant = "seal_aborted" /\ source[k] = "aborted")
    /\ source' = [source EXCEPT ![k] = "sealed"]
    /\ UNCHANGED <<aborted, row, held, charged, io, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Fence(k) ==
    /\ source[k] = "aborted" /\ k \in row /\ ~Closed(k)
    /\ held' = held \ {k} /\ fenced' = fenced \cup {k}
    /\ UNCHANGED <<source, aborted, row, charged, io, retained, floor, ack, owner, late, startedClosed, takeoverFloor>>

Start(k) ==
    /\ (k \in held \/ (Variant = "start_after_fence" /\ Closed(k))) /\ io[k] = "open"
    /\ io' = [io EXCEPT ![k] = "pending"]
    /\ startedClosed' = IF Closed(k) THEN startedClosed \cup {k} ELSE startedClosed
    /\ UNCHANGED <<source, aborted, row, held, charged, retained, fenced, floor, ack, owner, late, takeoverFloor>>

Write(k) ==
    /\ io[k] = "pending"
    /\ io' = [io EXCEPT ![k] = "present"]
    /\ UNCHANGED <<source, aborted, row, held, charged, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Dispose(k) ==
    /\ Closed(k) /\ k \in charged /\ io[k] # "absent"
    /\ io' = [io EXCEPT ![k] = "absent"]
    /\ UNCHANGED <<source, aborted, row, held, charged, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Refund(k) ==
    /\ k \in charged /\ k \notin held
    /\ io[k] = "absent" \/ Variant = "refund_after_fence"
    /\ charged' = charged \ {k} /\ retained' = retained \ {k}
    /\ UNCHANGED <<source, aborted, row, held, io, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Adopt(k) ==
    /\ Closed(k) /\ k \in charged \ retained
    /\ retained' = retained \cup {k}
    /\ UNCHANGED <<source, aborted, row, held, charged, io, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

Acknowledge(k) ==
    /\ k \in aborted \ ack /\ k \in row
    /\ Closed(k) \/ Variant = "ack_before_fence"
    /\ k \notin charged \/ k \in retained
    /\ ack' = ack \cup {k}
    /\ UNCHANGED <<source, aborted, row, held, charged, io, retained, fenced, floor, owner, late, startedClosed, takeoverFloor>>

CompactSource(k) ==
    /\ k \in row \cap ack
    /\ row' = row \ {k}
    /\ UNCHANGED <<source, aborted, held, charged, io, retained, fenced, floor, ack, owner, late, startedClosed, takeoverFloor>>

AdvanceFloor(k) ==
    /\ k = floor + 1 /\ k \in ack
    /\ floor' = k /\ fenced' = fenced \ {k}
    /\ UNCHANGED <<source, aborted, row, held, charged, io, retained, ack, owner, late, startedClosed, takeoverFloor>>

Takeover ==
    /\ owner = 0 /\ owner' = 1 /\ takeoverFloor' = floor
    /\ fenced' = IF Variant = "forget_fence" THEN {} ELSE fenced
    /\ UNCHANGED <<source, aborted, row, held, charged, io, retained, floor, ack, late, startedClosed>>

Next ==
    \/ Takeover
    \/ \E k \in Keys :
         Plan(k) \/ Prepare(k) \/ Abort(k) \/ Seal(k) \/ Fence(k) \/ Start(k)
         \/ Write(k) \/ Dispose(k) \/ Refund(k) \/ Adopt(k) \/ Acknowledge(k)
         \/ CompactSource(k) \/ AdvanceFloor(k)

Spec == Init /\ [][Next]_vars

CapacityAndPhysicalWork ==
    Cardinality(charged) <= 1 /\ held \cup retained \subseteq charged
    /\ \A k \in Keys : io[k] \in {"open", "pending", "present"} => k \in charged

AckMeansClosed == \A k \in ack : Closed(k) /\ k \notin held
ClosedRefusesLiveGrant == \A k \in Keys : Closed(k) => k \notin held
NoNewTicketsAfterFence == startedClosed = {}
AbortIsFinal == \A k \in aborted : source[k] = "aborted"
CompactedWaitsForCustody ==
    \A k \in aborted \ row : Closed(k) /\ (k \in retained \/ io[k] \in {"none", "absent"})

NeverLateSettleAndReuse ==
    ~(1 \in late /\ owner = 1 /\ takeoverFloor >= 1 /\ 1 \notin row \cup charged /\ source[2] = "sealed")
NeverCompactWithPendingWork ==
    ~(1 \in late /\ 1 \notin row /\ 1 \in retained /\ io[1] = "pending")
=============================================================================
