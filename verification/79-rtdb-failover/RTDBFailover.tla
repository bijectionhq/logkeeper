---------------------------- MODULE RTDBFailover ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Variant, Coverage
VARIABLE state

Zones == {"a", "b", "c"}
OriginalVoters == {"a", "b"}
RivalZone == "c"
Original == "chosen-payload"
Rival == "rival-payload"
MustUseSurvivors == state.failed # ""
HasQuorum == Cardinality(Zones \ {state.failed}) >= 2
CoversChosen == Coverage = "exact" /\ OriginalVoters \ {state.failed} # {}
FreshNonce == 2
OriginalWindow == 7

Init ==
    state = [chosen |-> FALSE, failed |-> "", recovered |-> "",
             writer |-> "old", cut |-> 0, applied |-> 0, receipt |-> "",
             rivalReply |-> "", oldWriterApplied |-> FALSE, staleAttempted |-> FALSE,
             previousMarker |-> FALSE, invocation |-> 0, freshMarker |-> FALSE,
             servedNonce |-> 0, appended |-> FALSE, cursor |-> 0, window |-> OriginalWindow]

Choose ==
    /\ ~state.chosen
    /\ state.failed = ""
    /\ Cardinality(OriginalVoters) >= 2
    /\ state' = [state EXCEPT !.chosen = TRUE, !.cursor = 1]

Lose(zone) ==
    /\ state.chosen
    /\ state.failed = ""
    /\ state' = [state EXCEPT !.failed = zone]

Recover ==
    /\ MustUseSurvivors
    /\ HasQuorum
    /\ CoversChosen \/ Variant = "skip-coverage"
    /\ state.recovered = ""
    /\ state' = [state EXCEPT !.recovered =
         IF Variant = "prefer-stage" /\ RivalZone # state.failed THEN Rival ELSE Original]

Grant ==
    /\ state.recovered # ""
    /\ state.writer = "old"
    /\ Variant # "need-directory"
    /\ state' = [state EXCEPT !.writer = "new", !.cut = 1]

Retry ==
    /\ state.writer = "new"
    /\ state.receipt = ""
    /\ state' = [state EXCEPT !.receipt = state.recovered,
             !.rivalReply = IF Variant = "trust-position" \/ state.recovered = Rival
                            THEN "committed" ELSE "conflict"]

DelayedWriter ==
    /\ state.writer = "new"
    /\ ~state.staleAttempted
    /\ state' = [state EXCEPT !.staleAttempted = TRUE,
             !.oldWriterApplied = (Variant = "accept-old-epoch")]

CatchUp ==
    /\ state.writer = "new"
    /\ state.applied = 0
    /\ state' = [state EXCEPT !.applied = state.cut]

PriorMarker ==
    /\ state.writer = "new"
    /\ ~state.previousMarker
    /\ state' = [state EXCEPT !.previousMarker = TRUE]

Invoke ==
    /\ state.previousMarker
    /\ state.invocation = 0
    /\ state' = [state EXCEPT !.invocation = IF Variant = "reuse-nonce" THEN 1 ELSE FreshNonce]

Mark ==
    /\ state.invocation # 0
    /\ ~state.freshMarker
    /\ state' = [state EXCEPT !.freshMarker = TRUE]

Serve(nonce) ==
    /\ state.invocation # 0
    /\ state.servedNonce = 0
    /\ state.applied = state.cut \/ Variant = "serve-before-apply"
    /\ nonce = state.invocation \/ Variant = "ignore-nonce"
    /\ IF nonce = FreshNonce THEN state.freshMarker ELSE state.previousMarker
    /\ state' = [state EXCEPT !.servedNonce = nonce]

Append ==
    /\ state.servedNonce # 0
    /\ ~state.appended
    /\ state.cursor = 1
    /\ Variant # "need-allocator"
    /\ state' = [state EXCEPT !.appended = TRUE, !.cursor = 2,
             !.window = IF Variant = "replace-window" THEN OriginalWindow + 1 ELSE OriginalWindow]

Next ==
    Choose \/ (\E zone \in Zones : Lose(zone)) \/ Recover \/ Grant \/ Retry \/ DelayedWriter \/
    CatchUp \/ PriorMarker \/ Invoke \/ Mark \/ Serve(1) \/ Serve(FreshNonce) \/ Append \/ UNCHANGED state

Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(Choose) /\ WF_state(\E zone \in Zones : Lose(zone)) /\
        WF_state(Recover) /\ WF_state(Grant) /\ WF_state(Retry) /\ WF_state(DelayedWriter) /\
        WF_state(CatchUp) /\ WF_state(PriorMarker) /\ WF_state(Invoke) /\ WF_state(Mark) /\
        WF_state(Serve(FreshNonce)) /\ WF_state(Append)

RecoverExact == state.recovered = "" \/ (state.recovered = Original /\ CoversChosen)
ReconcileExact == state.receipt = "" \/ (state.receipt = Original /\ state.rivalReply = "conflict")
OldEpochFenced == ~state.oldWriterApplied
InvocationFresh == state.servedNonce = 0 \/ (state.servedNonce = FreshNonce /\ state.freshMarker)
ReadIsApplied == state.servedNonce # 0 => state.applied = state.cut
UsesOriginalWindow == state.appended => state.window = OriginalWindow /\ state.cursor = 2
NoServiceWithoutCoverage == Coverage = "missing" => state.writer = "old" /\ ~state.appended
Completes == <>(state.appended /\ state.receipt = Original /\ state.staleAttempted)
=============================================================================
