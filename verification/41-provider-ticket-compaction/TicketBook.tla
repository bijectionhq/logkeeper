-------------------------------- MODULE TicketBook --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Tickets, Width, Policy, Variant
VARIABLE s

Ids == 1..Tickets
Issued == 1..s.issued

Init ==
    s = [issued |-> 0, open |-> TRUE, live |-> {}, completed |-> {}, markers |-> {},
         waiting |-> {}, certified |-> {}, present |-> FALSE, erased |-> FALSE,
         restarted |-> FALSE, completedAtRestart |-> {}, repeatedEffect |-> FALSE,
         duplicateRefused |-> {}, recoveredProof |-> {}]

Issue ==
    /\ s.open /\ s.issued < Tickets /\ Cardinality(s.live) < Width
    /\ s' = [s EXCEPT !.issued = @ + 1,
                      !.live = IF Variant = "split_issue" THEN @ ELSE @ \cup {s.issued + 1},
                      !.waiting = IF Variant = "split_issue" THEN @ \cup {s.issued + 1} ELSE @]

LateRegister(id) ==
    /\ id \in s.waiting /\ Cardinality(s.live) < Width
    /\ s' = [s EXCEPT !.waiting = @ \ {id}, !.live = @ \cup {id}]

PermitsEffect(id) ==
    IF Policy = "active" /\ Variant # "missing_is_live" THEN id \in s.live ELSE id \notin s.markers

Deliver(id) ==
    /\ id \in Issued
    /\ IF PermitsEffect(id)
       THEN s' = [s EXCEPT !.live = @ \ {id}, !.completed = @ \cup {id},
                           !.markers = IF Policy = "markers" THEN @ \cup {id} ELSE @,
                           !.repeatedEffect = @ \/ id \in s.completed,
                           !.present = TRUE]
       ELSE s' = [s EXCEPT !.duplicateRefused = IF s.erased /\ s.restarted THEN @ \cup {id} ELSE @]

Certify(id) ==
    /\ id \in Issued \/ Variant = "certify_unissued"
    /\ id \notin s.live /\ id \notin s.certified
    /\ s' = [s EXCEPT !.certified = @ \cup {id},
                      !.recoveredProof = IF id \in s.completedAtRestart THEN @ \cup {id} ELSE @]

ForgetMarkers ==
    /\ Variant = "forget_markers" /\ s.markers # {}
    /\ s' = [s EXCEPT !.markers = {}]

Seal ==
    /\ s.open
    /\ s' = [s EXCEPT !.open = FALSE]

Erase ==
    /\ ~s.open /\ s.live = {} /\ ~s.erased
    /\ s' = [s EXCEPT !.present = FALSE, !.erased = TRUE]

Restart ==
    /\ ~s.restarted
    /\ s' = [s EXCEPT !.restarted = TRUE,
                      !.completedAtRestart = s.completed,
                      !.issued = IF Variant = "restart_drops_issuance" /\ s.live = {} THEN 0 ELSE @]

Next ==
    \/ Issue \/ Seal \/ Erase \/ Restart \/ ForgetMarkers
    \/ \E id \in Ids : LateRegister(id) \/ Deliver(id) \/ Certify(id)

Spec == Init /\ [][Next]_s

AllIssuedAccounted == Issued = s.live \cup s.completed
NoReopen == s.certified \cap s.live = {}
NeverReuseIssued == s.completed \cap s.live = {}
OneEffectPerTicket == ~s.repeatedEffect
StableErase == s.erased => ~s.present
BoundedLive == Cardinality(s.live) <= Width
BoundedTerminalRows == Cardinality(s.markers) <= Width
NeverConfirmsAfterCompactionAndRestart == s.recoveredProof = {}
NeverRejectsDelayedCompletedAfterErase == s.duplicateRefused = {}
NeverIssuesBeyondWidthWithAnOldLive ==
    ~(s.issued > Width /\ 1 \in s.live /\ s.completed # {})
=============================================================================
