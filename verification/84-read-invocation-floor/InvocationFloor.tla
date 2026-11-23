--------------------------- MODULE InvocationFloor ---------------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

Limit == 2
Read(writer, nonce) == <<writer, nonce>>
First == Read(1, 1)
Later == Read(1, 2)
Successor == Read(2, 1)
Empty == Read(0, 0)

Init ==
    state = [phase |-> "start", grant |-> 1, floor |-> 0, live |-> Empty, cut |-> 0,
             used |-> {}, skipped |-> {}, duplicate |-> FALSE, overtaken |-> FALSE,
             foreign |-> FALSE, reissued |-> FALSE, outOfRange |-> FALSE]

Fresh(call) ==
    /\ call[1] = state.grant \/ Variant = "no-grant"
    /\ CASE Variant = "live-rows-only" -> TRUE
          [] Variant = "high-water" -> call[2] > state.floor
          [] Variant = "wrap" -> call[2] = IF state.floor = Limit THEN 1 ELSE state.floor + 1
          [] OTHER -> call[2] = state.floor + 1 /\ call[2] <= Limit

Admit(call, phase) ==
    /\ state.live = Empty
    /\ Fresh(call)
    /\ state' = [state EXCEPT !.phase = phase, !.floor = call[2], !.live = call,
                 !.used = @ \cup {call}, !.duplicate = @ \/ call \in state.used,
                 !.overtaken = @ \/ (call = Later /\ First \notin (state.used \cup state.skipped)),
                 !.foreign = @ \/ call[1] # state.grant, !.outOfRange = @ \/ call[2] > Limit]

OpenFirst ==
    /\ Scenario # "gap" /\ state.phase = "start"
    /\ Admit(First, "opened")

CloseFirst ==
    /\ state.phase = "opened" /\ Scenario \in {"compact", "exhaust"}
    /\ state' = [state EXCEPT !.phase = "closed", !.live = Empty, !.cut = @ + 1]

Reopen ==
    /\ Scenario = "compact" /\ state.phase = "closed"
    /\ state' = [state EXCEPT !.phase = "reopened",
                 !.floor = IF Variant = "rollback-floor" THEN 0 ELSE state.floor]

RetrySpent ==
    /\ Scenario = "compact" /\ state.phase = "reopened"
    /\ Admit(First, "done")

AbandonFirst ==
    /\ Scenario = "gap" /\ state.phase = "start"
    /\ Variant # "no-abandon"
    /\ state' = [state EXCEPT !.phase = "abandoned", !.floor = 1, !.skipped = @ \cup {First}]

OpenLater ==
    /\ (Scenario = "gap" /\ state.phase \in {"start", "abandoned"}) \/
       (Scenario = "exhaust" /\ state.phase = "closed")
    /\ Admit(Later, "later")

CloseLater ==
    /\ Scenario = "exhaust" /\ state.phase = "later"
    /\ state' = [state EXCEPT !.phase = "exhausted", !.live = Empty]

AfterLimit ==
    /\ Scenario = "exhaust" /\ state.phase = "exhausted"
    /\ \E nonce \in {1, 3} : Admit(Read(1, nonce), "done")

Fence ==
    /\ Scenario = "fence" /\ state.phase = "opened"
    /\ state' = [state EXCEPT !.phase = "fenced", !.grant = 2, !.floor = 0]

Reissue ==
    /\ Scenario = "fence" /\ state.phase = "fenced" /\ state.live = First
    /\ state' = [state EXCEPT !.phase = "retried", !.reissued = TRUE]

CloseCarried ==
    /\ Scenario = "fence" /\ state.phase = "retried"
    /\ state' = [state EXCEPT !.phase = "released", !.live = Empty]

OpenAfterFence ==
    /\ Scenario = "fence" /\ state.phase = "released"
    /\ Admit(Successor, "done") \/ Admit(First, "done")

Next == OpenFirst \/ CloseFirst \/ Reopen \/ RetrySpent \/ AbandonFirst \/ OpenLater \/
        CloseLater \/ AfterLimit \/ Fence \/ Reissue \/ CloseCarried \/ OpenAfterFence
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(AbandonFirst) /\ WF_state(OpenLater) /\ WF_state(OpenFirst) /\
        WF_state(Fence) /\ WF_state(Reissue) /\ WF_state(CloseCarried) /\ WF_state(OpenAfterFence)

ExactlyOnce == ~state.duplicate
NoImplicitSkip == ~state.overtaken
CurrentGrant == ~state.foreign
WithinLimit == ~state.outOfRange
GapProgress == <>(state.live = Later)
FenceProgress == <>(state.reissued /\ state.live = Successor)
=============================================================================
