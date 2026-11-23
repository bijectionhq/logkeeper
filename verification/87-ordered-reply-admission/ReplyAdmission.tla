---------------------------- MODULE ReplyAdmission ----------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

Open == 1
Closed == 0
Reused == 2
FirstCall == 1
LaterCall == 2
Request == IF Scenario = "slot-reused" THEN LaterCall ELSE FirstCall
PresentedSerial == 1

Init ==
    state = [ordered |-> 1, applied |-> 1, row |-> Open, observed |-> 0,
             paid |-> (Scenario = "retired"), preparedAt |-> 0, attempted |-> FALSE,
             positioned |-> FALSE, reframed |-> FALSE,
             elected |-> TRUE, sealed |-> FALSE, retired |-> FALSE,
             authorized |-> FALSE, completed |-> FALSE, badRow |-> FALSE, noPay |-> FALSE,
             wrongPosition |-> FALSE, oldScope |-> FALSE, oldFloor |-> FALSE]

Close ==
    /\ Scenario \in {"overlap", "unseen-close", "slot-reused"}
    /\ state.row = Open
    /\ (Scenario # "overlap" \/ state.observed = 1)
    /\ state' = [state EXCEPT !.ordered = @ + 1, !.row = Closed]

Reuse ==
    /\ Scenario = "slot-reused" /\ state.row = Closed
    /\ state' = [state EXCEPT !.ordered = @ + 1, !.row = Reused]

Probe ==
    /\ state.observed = 0
    /\ (Scenario # "unseen-close" \/ state.row = Closed)
    /\ state' = [state EXCEPT !.observed = state.ordered]

Retire ==
    /\ Scenario = "retired" /\ ~state.retired
    /\ state' = [state EXCEPT !.retired = TRUE, !.ordered = @ + 1, !.applied = @ + 1]

Seal ==
    /\ Scenario = "sealed" /\ ~state.sealed
    /\ state' = [state EXCEPT !.sealed = TRUE, !.ordered = @ + 1, !.applied = @ + 1]

Prepare ==
    /\ state.observed # 0 /\ state.preparedAt = 0
    /\ Scenario # "retired" \/ state.retired
    /\ Scenario # "sealed" \/ state.sealed
    /\ Scenario # "slot-reused" \/ state.row = Reused
    /\ state' = [state EXCEPT !.paid = @ \/ Scenario \notin {"unpaid", "retired"},
                 !.preparedAt = state.ordered + 1]

Overtaken ==
    /\ Scenario \in {"stale-position", "reframe"} /\ state.preparedAt # 0 /\ ~state.positioned
    /\ state' = [state EXCEPT !.ordered = @ + 1, !.applied = @ + 1, !.positioned = TRUE]

Reframe ==
    /\ Scenario = "reframe" /\ state.positioned /\ ~state.reframed
    /\ state' = [state EXCEPT !.preparedAt = state.ordered + 1, !.reframed = TRUE]

Choose ==
    /\ state.preparedAt # 0 /\ ~state.attempted
    /\ Scenario # "overlap" \/ state.row = Closed
    /\ Scenario # "stale-position" \/ state.positioned
    /\ Scenario # "reframe" \/ state.reframed
    /\ LET exactRow == state.row = Request /\ state.row = PresentedSerial
           eligible == CASE Variant = "probe-authorizes" -> state.observed = 1
                          [] Variant = "data-floor" -> state.applied = 1
                          [] Variant = "omit-serial" -> state.row = Request
                          [] OTHER -> exactRow
           live == ~state.sealed \/ Variant = "allow-sealed"
           pin == state.paid \/ Variant = "ignore-payment"
           scope == state.preparedAt = state.ordered + 1 \/ Variant = "ignore-position"
           accept == eligible /\ live /\ pin /\ scope
       IN state' = [state EXCEPT !.attempted = TRUE, !.authorized = accept,
                      !.badRow = accept /\ ~exactRow, !.noPay = accept /\ ~state.paid,
                      !.wrongPosition = accept /\ state.preparedAt # state.ordered + 1,
                      !.oldScope = accept /\ state.sealed,
                      !.oldFloor = accept /\ state.observed > state.applied /\ state.row = Closed]

Lose ==
    /\ Scenario = "protected" /\ state.authorized /\ state.elected
    /\ state' = [state EXCEPT !.elected = FALSE]

Complete ==
    /\ state.authorized /\ ~state.completed
    /\ Scenario # "protected" \/ ~state.elected
    /\ state' = [state EXCEPT !.completed = TRUE]

Next == Close \/ Reuse \/ Probe \/ Retire \/ Seal \/ Prepare \/ Overtaken \/ Reframe \/ Choose \/ Lose \/ Complete
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(Probe) /\ WF_state(Prepare) /\ WF_state(Choose) /\
        WF_state(Lose) /\ WF_state(Complete) /\ WF_state(Retire) /\ WF_state(Overtaken) /\ WF_state(Reframe)
ExactLiveRow == ~state.badRow
PaidBeforeChoice == ~state.noPay
ExactPosition == ~state.wrongPosition
OnlyInstalledOwner == ~state.oldScope
CoversOrderedClose == ~state.oldFloor
Finishes == <>state.completed
=============================================================================
