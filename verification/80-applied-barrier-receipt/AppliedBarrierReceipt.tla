-------------------------- MODULE AppliedBarrierReceipt -----------------------
EXTENDS Naturals

CONSTANTS Variant, Scenario
VARIABLE state

NoReceipt == [scope |-> "none", invocation |-> 0, position |-> 0, cut |-> 0]
Exact == [scope |-> "installed", invocation |-> 2, position |-> 5, cut |-> 1]
Foreign == [Exact EXCEPT !.scope = "other"]
WrongCut == [Exact EXCEPT !.cut = 2]
WrongPosition == [Exact EXCEPT !.position = 6]
Packet(body, signer) == [body |-> body, signer |-> signer]
None == Packet(NoReceipt, "none")
Success == Packet(Exact, "local")
Packets == {Success, Packet(WrongCut, "local"), Packet(WrongPosition, "local"), Packet(Exact, "foreign")}

Init ==
    state = [chosen |-> FALSE, applied |-> FALSE, success |-> FALSE, retired |-> (Scenario = "retired"),
             head |-> 1, advanced |-> FALSE, issued |-> NoReceipt, sourceLost |-> FALSE,
             materialized |-> FALSE, served |-> None]

Choose ==
    /\ Scenario # "foreign"
    /\ ~state.chosen
    /\ state' = [state EXCEPT !.chosen = TRUE]

Apply ==
    /\ state.chosen /\ ~state.applied
    /\ state' = [state EXCEPT !.applied = TRUE, !.success = ~state.retired]

Advance ==
    /\ state.success /\ ~state.advanced
    /\ Scenario = "live"
    /\ state' = [state EXCEPT !.advanced = TRUE, !.head = 2]

Emit ==
    /\ state.issued = NoReceipt
    /\ state.chosen
    /\ state.applied \/ Variant = "sign-before-apply"
    /\ state.success \/ Variant \in {"sign-before-apply", "sign-refusal"}
    /\ Variant # "sign-head" \/ state.advanced
    /\ state' = [state EXCEPT !.issued = IF Variant = "sign-head" THEN [Exact EXCEPT !.cut = state.head] ELSE Exact]

RetireAfterIssue ==
    /\ Scenario = "overlap" /\ state.issued # NoReceipt /\ ~state.retired
    /\ state' = [state EXCEPT !.retired = TRUE]

LoseSource ==
    /\ state.issued # NoReceipt \/ Scenario = "foreign"
    /\ Scenario # "overlap" \/ state.retired
    /\ ~state.sourceLost
    /\ state' = [state EXCEPT !.sourceLost = TRUE]

Materialize ==
    /\ state.issued # NoReceipt \/ Scenario = "foreign"
    /\ ~state.materialized
    /\ state' = [state EXCEPT !.materialized = TRUE]

Verifies(packet) ==
    CASE packet.signer = "local" ->
        \/ packet.body = state.issued
        \/ Variant = "omit-cut" /\ state.issued = Exact /\ packet.body = WrongCut
        \/ Variant = "omit-position" /\ state.issued = Exact /\ packet.body = WrongPosition
      [] OTHER -> Variant = "omit-scope" /\ packet.body = [Foreign EXCEPT !.scope = "installed"]

Deliver(packet) ==
    /\ state.served = None
    /\ state.sourceLost
    /\ state.materialized /\ packet.body.cut <= state.head
    /\ Variant # "need-live-signer"
    /\ packet.body.scope = Exact.scope /\ packet.body.invocation = Exact.invocation
    /\ Verifies(packet)
    /\ state' = [state EXCEPT !.served = packet]

Next == Choose \/ Apply \/ Advance \/ Emit \/ RetireAfterIssue \/ LoseSource \/ Materialize \/
        (\E packet \in Packets : Deliver(packet)) \/ UNCHANGED state
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(Choose) /\ WF_state(Apply) /\ WF_state(Emit) /\ WF_state(RetireAfterIssue) /\
        WF_state(LoseSource) /\ WF_state(Materialize) /\ WF_state(Deliver(Success))

OnlyAppliedSuccessIssues == state.issued # NoReceipt => state.applied /\ state.success
IssuedOriginalResult == state.issued # NoReceipt => state.issued = Exact
DeliveryIsExact == state.served # None => state.served = Success /\ state.served.body = state.issued
RetiredNeverServes == Scenario = "retired" => state.served = None
CompletesAfterSourceLoss == <>(state.served = Success)
=============================================================================
