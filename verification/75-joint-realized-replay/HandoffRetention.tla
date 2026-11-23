------------------------- MODULE HandoffRetention --------------------------
EXTENDS Naturals

CONSTANT Variant
VARIABLES phase, realized, settled
vars == <<phase, realized, settled>>

Init == phase = "active" /\ realized = FALSE /\ settled = FALSE

Seal ==
    /\ phase = "active"
    /\ phase' = "handoff" /\ realized' = TRUE
    /\ UNCHANGED settled

ReceiveCompleteAcknowledgments ==
    /\ phase = "handoff" /\ ~settled
    /\ settled' = TRUE
    /\ UNCHANGED <<phase, realized>>

Compact ==
    /\ settled /\ realized /\ (phase = "installed" \/ Variant = "ack_only")
    /\ realized' = FALSE
    /\ UNCHANGED <<phase, settled>>

Activate ==
    /\ phase = "handoff" /\ realized
    /\ phase' = "installed"
    /\ UNCHANGED <<realized, settled>>

Next == Seal \/ ReceiveCompleteAcknowledgments \/ Compact \/ Activate \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

HandoffStillHasItsVector == phase = "handoff" => realized
NeverActivateAndCompactAfterEarlyAcknowledgments == ~(phase = "installed" /\ settled /\ ~realized)
=============================================================================
