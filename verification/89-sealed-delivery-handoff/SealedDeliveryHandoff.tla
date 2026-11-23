------------------------- MODULE SealedDeliveryHandoff -------------------------
EXTENDS Naturals

CONSTANT Variant, Scenario

VARIABLES at, live, saved, active, retained, stopped, reply, rejected, wrongClear, reused

vars == <<at, live, saved, active, retained, stopped, reply, rejected, wrongClear, reused>>
NoBook == [cut |-> 0, floor |-> 0, borrow |-> "none", read |-> FALSE, dataEnd |-> 7]
Cut == [cut |-> 4, floor |-> 2, borrow |-> "original", read |-> FALSE, dataEnd |-> 7]
Old == [Cut EXCEPT !.cut = 2, !.floor = 1, !.borrow = "none", !.read = TRUE]

Init ==
  /\ at = "prepared"
  /\ live = TRUE
  /\ saved = NoBook
  /\ active = NoBook
  /\ retained = TRUE
  /\ stopped = FALSE
  /\ reply = FALSE
  /\ rejected = FALSE
  /\ wrongClear = FALSE
  /\ reused = FALSE

Seal ==
  /\ at = "prepared"
  /\ at' = "sealed"
  /\ saved' = IF Scenario = "stale" THEN Old
              ELSE IF Scenario = "split" THEN [Cut EXCEPT !.floor = Old.floor]
              ELSE Cut
  /\ retained' = (Scenario # "missing-extent")
  /\ UNCHANGED <<live, active, stopped, reply, rejected, wrongClear, reused>>

LoseSource ==
  /\ at = "sealed"
  /\ live
  /\ live' = FALSE
  /\ UNCHANGED <<at, saved, active, retained, stopped, reply, rejected, wrongClear, reused>>

Exact ==
  /\ IF Variant = "stale-data-frontier" THEN saved.dataEnd = Cut.dataEnd ELSE saved.cut = Cut.cut
  /\ IF Variant \in {"stale-data-frontier", "split-control"} THEN TRUE ELSE saved = Cut
  /\ retained \/ Variant = "forget-independent-extent"

Mount ==
  /\ at = "sealed"
  /\ ~live
  /\ IF Exact THEN (at' = "mounted" /\ rejected' = FALSE) ELSE (at' = "refused" /\ rejected' = TRUE)
  /\ UNCHANGED <<live, saved, active, retained, stopped, reply, wrongClear, reused>>

Activate ==
  /\ at = "mounted"
  /\ (Variant # "recontact" \/ live)
  /\ at' = "active"
  /\ active' = IF Variant = "reset-delivery-floor" THEN [saved EXCEPT !.floor = 0]
               ELSE IF Variant = "reparent-borrow" THEN [saved EXCEPT !.borrow = "target"]
               ELSE saved
  /\ UNCHANGED <<live, saved, retained, stopped, reply, rejected, wrongClear, reused>>

Complete ==
  /\ at = "active"
  /\ Scenario = "complete"
  /\ at' = "completed"
  /\ reply' = (active.borrow = "original" /\ retained /\ ~stopped)
  /\ UNCHANGED <<live, saved, active, retained, stopped, rejected, wrongClear, reused>>

Stop ==
  /\ at = "active"
  /\ Scenario = "settle"
  /\ at' = "stopped"
  /\ stopped' = TRUE
  /\ UNCHANGED <<live, saved, active, retained, reply, rejected, wrongClear, reused>>

Settle ==
  /\ at = "stopped"
  /\ at' = "settled"
  /\ active' = IF active.borrow = "original" THEN [active EXCEPT !.borrow = "none"] ELSE active
  /\ UNCHANGED <<live, saved, retained, stopped, reply, rejected, wrongClear, reused>>

RetrySerial ==
  /\ at = "settled"
  /\ at' = "retried"
  /\ reused' = (active.floor + 1 = 1)
  /\ UNCHANGED <<live, saved, active, retained, stopped, reply, rejected, wrongClear>>

OldAuthorityClear ==
  /\ at = "sealed"
  /\ Scenario = "settle"
  /\ Variant = "sealed-source-clears"
  /\ ~wrongClear
  /\ wrongClear' = TRUE
  /\ UNCHANGED <<at, live, saved, active, retained, stopped, reply, rejected, reused>>

Installed == at \in {"active", "completed", "stopped", "settled", "retried"}
ExactControl == Installed => active.cut = Cut.cut /\ active.read = Cut.read /\ active.floor = Cut.floor
KeepsCustody == Installed => retained
OriginalCustodian == at \in {"active", "completed", "stopped"} => active.borrow = Cut.borrow
OnlySuccessorClears == ~wrongClear
NoReuse == ~reused
Finishes == <>(Scenario = "complete" => reply)
StopsAndClears == <> (at = "retried" /\ stopped /\ active.borrow = "none" /\ ~reused)
RejectsInvalidCut == <> (at = "refused" /\ rejected)

Next == Seal \/ LoseSource \/ Mount \/ Activate \/ Complete \/ Stop \/ Settle \/ RetrySerial \/ OldAuthorityClear
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
