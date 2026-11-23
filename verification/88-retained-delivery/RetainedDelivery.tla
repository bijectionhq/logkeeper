--------------------------- MODULE RetainedDelivery ---------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

None == 0
Original == 1
Other == 2
SlotBudget == 1

Init ==
    state = [book |-> None, issued |-> 0, liveRead |-> TRUE, chosen |-> FALSE,
             originalBorrow |-> TRUE, settled |-> FALSE, oldBase |-> None, newBase |-> None,
             switched |-> FALSE, frame |-> FALSE, crashed |-> FALSE, replied |-> FALSE,
             badRelease |-> FALSE, reopened |-> FALSE, overflow |-> FALSE, sourceClosed |-> FALSE]

Choose ==
    /\ ~state.chosen
    /\ state' = [state EXCEPT !.book = Original, !.issued = 1, !.chosen = TRUE, !.frame = TRUE]

CloseRead ==
    /\ state.chosen /\ state.liveRead
    /\ state' = [state EXCEPT !.liveRead = FALSE,
                 !.book = IF Variant = "couple-read-slot" THEN None ELSE @]

Checkpoint ==
    /\ state.chosen /\ ~state.liveRead /\ state.newBase = None /\ ~state.switched
    /\ state.book # None \/ Variant = "couple-read-slot"
    /\ state' = [state EXCEPT !.newBase = state.book, !.sourceClosed = TRUE]

Switch ==
    /\ state.sourceClosed /\ ~state.switched
    /\ state' = [state EXCEPT !.oldBase = state.newBase, !.switched = TRUE]

Collect ==
    /\ state.chosen /\ state.frame /\ state.sourceClosed
    /\ (state.switched \/ Variant = "visible-only")
    /\ (state.newBase = Original \/ Variant = "couple-read-slot")
    /\ Variant # "pin-raw-frame"
    /\ state' = [state EXCEPT !.frame = FALSE]

Crash ==
    /\ Scenario = "recovery" /\ ~state.crashed /\ state.sourceClosed /\ ~state.frame
    /\ state' = [state EXCEPT !.crashed = TRUE, !.book = state.oldBase]

Finish ==
    /\ Scenario = "recovery" /\ state.crashed /\ state.book = Original
    /\ state.originalBorrow /\ ~state.replied
    /\ state' = [state EXCEPT !.replied = TRUE]

Settle(identity) ==
    /\ Scenario \in {"reuse", "wrong-settlement"}
    /\ state.book = Original /\ ~state.settled
    /\ identity = Original \/ Variant = "ignore-settlement-identity"
    /\ state' = [state EXCEPT !.settled = TRUE, !.book = None,
                 !.originalBorrow = (identity # Original), !.badRelease = (identity # Original)]

Submit(serial) ==
    /\ Scenario = "reuse" /\ state.settled /\ state.book = None
    /\ serial = state.issued + 1 \/ Variant = "ignore-issued"
    /\ state' = [state EXCEPT !.book = serial, !.issued = serial, !.reopened = (serial = Original)]

Compete ==
    /\ Scenario = "capacity" /\ state.book = Original /\ ~state.overflow
    /\ Variant = "ignore-capacity"
    /\ state' = [state EXCEPT !.book = Other, !.overflow = TRUE]

Next == Choose \/ CloseRead \/ Checkpoint \/ Switch \/ Collect \/ Crash \/ Finish \/
        (\E identity \in {Original, Other} : Settle(identity)) \/
        (\E serial \in {Original, Other} : Submit(serial)) \/ Compete
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(Choose) /\ WF_state(CloseRead) /\ WF_state(Checkpoint) /\
        WF_state(Switch) /\ WF_state(Collect) /\ WF_state(Crash) /\ WF_state(Finish)

Recoverable == state.crashed /\ state.originalBorrow => state.book = Original
ExactSettlement == ~state.badRelease
NoReuse == ~state.reopened
Fits == ~state.overflow /\ SlotBudget = 1
Finishes == <>(state.replied /\ ~state.frame)
=============================================================================
