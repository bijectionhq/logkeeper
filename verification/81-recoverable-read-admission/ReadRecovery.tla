---------------------------- MODULE ReadRecovery ------------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

Protected == Scenario \in {"admitted-live", "admitted-retired", "reuse", "two-slots"}
SlotCount == IF Scenario = "two-slots" THEN 2 ELSE 1
AtRetirement == Scenario \in {"admitted-retired", "unadmitted-retired"}

Init ==
    state = [oldMarker |-> FALSE, charged |-> FALSE, row |-> 0, hold |-> 0,
             lost |-> FALSE, compacted |-> FALSE, retired |-> FALSE, stopped |-> FALSE,
             freshTried |-> FALSE, issued |-> 0, served |-> FALSE, credit |-> SlotCount, reused |-> FALSE, replayedClosed |-> FALSE,
             duplicate |-> FALSE]

Mark ==
    /\ ~state.oldMarker
    /\ state' = [state EXCEPT !.oldMarker = TRUE]

Admit ==
    /\ Protected
    /\ state.oldMarker /\ ~state.charged /\ ~state.lost
    /\ state.credit > 0
    /\ state' = [state EXCEPT !.charged = TRUE, !.row = IF Variant = "volatile-outcome" THEN 0 ELSE 1,
                 !.hold = IF Variant = "omit-basis" THEN 0 ELSE 1, !.credit = @ - 1]

Duplicate ==
    /\ Scenario = "two-slots" /\ Variant = "admit-duplicate"
    /\ state.charged /\ state.credit > 0 /\ ~state.duplicate
    /\ state' = [state EXCEPT !.duplicate = TRUE, !.credit = @ - 1]

Retire ==
    /\ AtRetirement
    /\ state.oldMarker /\ ~state.retired
    /\ Protected => state.charged
    /\ state' = [state EXCEPT !.retired = TRUE]

Lose ==
    /\ state.oldMarker /\ ~state.lost
    /\ Protected => state.charged
    /\ AtRetirement => state.retired
    /\ state' = [state EXCEPT !.lost = TRUE]

Compact ==
    /\ state.lost /\ ~state.compacted
    /\ state' = [state EXCEPT !.compacted = TRUE]

Stop ==
    /\ Scenario = "reuse" /\ state.compacted /\ ~state.stopped /\ state.charged
    /\ state' = [state EXCEPT !.stopped = TRUE, !.charged = FALSE, !.row = 0, !.hold = 0, !.credit = 1]

Reuse ==
    /\ Scenario = "reuse" /\ state.stopped /\ ~state.reused
    /\ state.credit = 1
    /\ state' = [state EXCEPT !.reused = TRUE, !.row = 2, !.hold = 2, !.charged = TRUE, !.credit = 0]

RecoverOriginal ==
    /\ state.compacted /\ state.issued = 0 /\ ~state.stopped
    /\ state.row = 1 \/ (Variant = "pin-only-invents" /\ state.hold = 1)
    /\ state.hold = 1 \/ Variant = "omit-basis"
    /\ Variant \notin {"needs-old-suffix", "needs-lost-handle"}
    /\ state' = [state EXCEPT !.issued = IF Variant = "pin-only-invents" THEN 2 ELSE 1]

OldHandleAfterReuse ==
    /\ state.reused /\ ~state.replayedClosed
    /\ Variant = "slot-only"
    /\ state' = [state EXCEPT !.replayedClosed = TRUE]

FreshRetry ==
    /\ state.compacted /\ ~state.freshTried /\ ~Protected
    /\ ~state.retired \/ Variant = "retry-through-retirement"
    /\ state' = [state EXCEPT !.freshTried = TRUE, !.issued = 2, !.hold = 2,
                !.row = 2, !.charged = TRUE, !.credit = 0]

Deliver ==
    /\ state.compacted /\ state.issued # 0 /\ ~state.served /\ ~state.stopped
    /\ state' = [state EXCEPT !.served = TRUE]

Next == Mark \/ Admit \/ Duplicate \/ Retire \/ Lose \/ Compact \/ Stop \/ Reuse \/
        RecoverOriginal \/ OldHandleAfterReuse \/ FreshRetry \/ Deliver \/ UNCHANGED state
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(Mark) /\ WF_state(Admit) /\ WF_state(Retire) /\ WF_state(Lose) /\
        WF_state(Compact) /\ WF_state(RecoverOriginal) /\ WF_state(FreshRetry) /\ WF_state(Deliver)

ReturnedOriginal == state.served /\ Protected /\ ~state.stopped => state.issued = 1
ExactHold == state.served /\ ~state.stopped => state.issued = state.hold
TerminalBound == state.retired => ~state.freshTried
SettledClosed == ~state.replayedClosed
NoDuplicateCharge == ~state.duplicate
PointwiseCharge == state.credit + (IF state.charged THEN 1 ELSE 0) +
                  (IF state.duplicate THEN 1 ELSE 0) = SlotCount
DegradedCompletes == <>state.served
=============================================================================
