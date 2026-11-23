--------------------------- MODULE PhysicalNamespace ---------------------------
EXTENDS Naturals

CONSTANT Variant
VARIABLE s

Versions == 1..2
Init ==
    s = [issued |-> 1, current |-> 1, admitted |-> {}, terminal |-> {},
         closed |-> FALSE, present |-> FALSE, absentProof |-> FALSE, stopped |-> {},
         rotated |-> FALSE, wrongScope |-> FALSE, staleRefused |-> FALSE,
         restarted |-> FALSE, restartedVacant |-> FALSE]

Admit ==
    /\ s.current # 0 /\ ~s.closed /\ s.current \notin s.admitted
    /\ s' = [s EXCEPT !.admitted = @ \cup {s.current}]

Deliver(version) ==
    /\ version \in s.admitted
    /\ LET allow == s.current # 0 /\ ~s.closed /\ s.current \in s.admitted /\ s.current \notin s.terminal
                    /\ (version = s.current \/ Variant = "route_only")
       IN IF allow THEN s' = [s EXCEPT !.terminal = @ \cup {s.current}, !.present = TRUE,
                                       !.wrongScope = @ \/ version # s.current]
          ELSE s' = [s EXCEPT !.staleRefused = @ \/ (s.current = 2 /\ version = 1 /\ 2 \in s.admitted)]

Fence ==
    /\ s.current # 0 /\ ~s.closed
    /\ s' = [s EXCEPT !.closed = TRUE]

Erase ==
    /\ s.current # 0 /\ s.closed /\ ~s.absentProof
    /\ s' = [s EXCEPT !.present = FALSE, !.absentProof = TRUE]

Reclaim ==
    /\ s.current # 0 /\ (s.absentProof \/ Variant = "reclaim_before_absence")
    /\ s' = [s EXCEPT !.current = 0, !.stopped = @ \cup {s.current}]

Reopen ==
    /\ s.current = 0 /\ s.issued < 2
    /\ s' = [s EXCEPT !.issued = @ + 1, !.current = s.issued + 1, !.closed = FALSE,
                      !.present = FALSE, !.absentProof = FALSE, !.rotated = TRUE]

Restart ==
    /\ ~s.restarted
    /\ s' = [s EXCEPT !.restarted = TRUE,
                      !.restartedVacant = s.current = 0,
                      !.issued = IF Variant = "forget_namespace_issuance" /\ s.current = 0 THEN 0 ELSE @]

Next == Admit \/ Fence \/ Erase \/ Reclaim \/ Reopen \/ Restart \/ \E version \in Versions : Deliver(version)
Spec == Init /\ [][Next]_s
NeverReusesClosedScope == s.current \notin s.stopped
WritesOnlyInOwnScope == ~s.wrongScope
OnlyReclaimsAbsent == s.current = 0 => s.absentProof /\ ~s.present
NeverReusesAddressAndRefusesOldTicket == ~(s.rotated /\ s.restartedVacant /\ s.staleRefused)
=============================================================================
