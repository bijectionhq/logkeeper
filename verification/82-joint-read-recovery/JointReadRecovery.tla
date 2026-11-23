------------------------------ MODULE JointReadRecovery --------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

Images == {1, 2}
NextImage == IF Scenario = "close-before-seal" THEN 2 ELSE 1

Init ==
    state = [current |-> 1, closed |-> FALSE, sealed |-> FALSE, oldRoute |-> TRUE,
             readRows |-> 0, holds |-> 0, covered |-> FALSE, active |-> FALSE, answered |-> 0, targetClosed |-> FALSE, answeredAfterClose |-> FALSE]

CloseBeforeSeal ==
    /\ Scenario = "close-before-seal" /\ ~state.sealed /\ ~state.closed
    /\ state' = [state EXCEPT !.closed = TRUE, !.current = 2]

Seal ==
    /\ ~state.sealed /\ state.current = NextImage
    /\ state' = [state EXCEPT !.sealed = TRUE]

LoseOldRoute ==
    /\ state.sealed /\ state.oldRoute
    /\ state' = [state EXCEPT !.oldRoute = FALSE]

CloseAtOldSource ==
    /\ Scenario = "close-after-seal"
    /\ Variant = "old-source-closes"
    /\ state.sealed /\ state.oldRoute /\ ~state.closed
    /\ state' = [state EXCEPT !.closed = TRUE]

Mount(rows, holds, covered) ==
    /\ state.sealed
    /\ state.readRows = 0
    /\ CASE Variant = "data-cut-only" -> rows = holds
          [] Variant = "split-control" -> rows = state.current
          [] OTHER -> rows = state.current /\ holds = state.current
    /\ covered \/ Variant = "skip-dependencies"
    /\ covered = (Scenario # "missing-basis")
    /\ state' = [state EXCEPT !.readRows = rows, !.holds = holds, !.covered = covered]

Activate ==
    /\ state.sealed /\ ~state.oldRoute
    /\ state.readRows # 0 /\ ~state.active
    /\ Variant # "recontact"
    /\ state' = [state EXCEPT !.active = TRUE]

CloseAtTarget ==
    /\ Scenario = "target-close" /\ state.active /\ ~state.closed
    /\ state' = [state EXCEPT !.closed = TRUE, !.targetClosed = TRUE]

Answer ==
    /\ state.active /\ state.answered = 0
    /\ ~state.targetClosed \/ Variant = "reuse-cached-read"
    /\ state' = [state EXCEPT !.answered = state.readRows,
                 !.answeredAfterClose = (state.closed /\ state.readRows = 1)]

ExactMount == Mount(NextImage, NextImage, TRUE)
Next == CloseBeforeSeal \/ Seal \/ LoseOldRoute \/ CloseAtOldSource \/
        (\E rows, holds \in Images, covered \in BOOLEAN : Mount(rows, holds, covered)) \/
        Activate \/ CloseAtTarget \/ Answer \/ UNCHANGED state
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(CloseBeforeSeal) /\ WF_state(Seal) /\ WF_state(LoseOldRoute) /\
        WF_state(ExactMount) /\ WF_state(Activate) /\ WF_state(Answer)

BindsChosenControl == state.readRows # 0 => state.readRows = state.current /\ state.holds = state.current
AdmittedBasisCovered == state.active => state.covered
ClosedDoesNotReopen == ~state.answeredAfterClose
CompletesFromExactMount == <>(state.answered = NextImage)
==================================================================================
