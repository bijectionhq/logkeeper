------------------------- MODULE RankedNamedRecovery --------------------------
EXTENDS Naturals, Sequences

CONSTANTS Variant, Scenario
VARIABLE state

ActiveSuccessor == 2
ReportedSuccessor == IF Scenario = "foreign" THEN 3 ELSE ActiveSuccessor
HigherReport == [ballot |-> 2, history |-> <<"admit", "close", "abandon">>]
LongerReport == [ballot |-> 1, history |-> <<"admit", "other", "other", "other">>]
LearnedHistory == <<"admit">>
OldChoice == <<"admit", "close">>
ExactHistory == HigherReport.history
Cutoff ==
    CASE Variant = "learned" -> LearnedHistory
      [] Variant = "length" -> LongerReport.history
      [] OTHER -> ExactHistory

Image(position, prefix, live, floor) == [position |-> position, prefix |-> prefix, live |-> live, floor |-> floor]
Earlier == Image(1, <<"admit">>, TRUE, 1)
Latest == Image(2, OldChoice, FALSE, 1)
Rival == Image(2, SubSeq(LongerReport.history, 1, 2), TRUE, 1)
Images == {Earlier, Latest, Rival}
MediaFor(cut) ==
    CASE Scenario = "missing" -> OldChoice
      [] cut = LongerReport.history -> LongerReport.history
      [] OTHER -> ExactHistory
PrefixOf(prefix, frames) == Len(prefix) <= Len(frames) /\ prefix = SubSeq(frames, 1, Len(prefix))

Replay(body, tail) ==
    [live |-> body.live /\ "close" \notin {tail[i] : i \in DOMAIN tail},
     floor |-> IF "abandon" \in {tail[i] : i \in DOMAIN tail} THEN 2 ELSE body.floor]

Init ==
    state = [phase |-> "start", cut |-> <<>>, bytes |-> <<>>, checkpoint |-> Earlier,
             live |-> FALSE, floor |-> 0, stored |-> {}, current |-> ActiveSuccessor, served |-> FALSE,
             spentBeforeInstall |-> FALSE, staleAtServe |-> FALSE, scopeAtServe |-> FALSE,
             advanced |-> FALSE, lateAtServe |-> FALSE, targetQuorum |-> TRUE, servedOffline |-> FALSE]

Capture ==
    /\ state.phase = "start"
    /\ Variant # "every-replica"
    /\ state' = [state EXCEPT !.phase = "fenced", !.cut = Cutoff, !.bytes = MediaFor(Cutoff)]

Stage(body) ==
    /\ state.phase = "fenced"
    /\ Variant # "install-before-stage" \/ state.stored = {"B", "C"}
    /\ (ReportedSuccessor = ActiveSuccessor \/ Variant = "skip-scope")
    /\ body.position <= Len(state.cut)
    /\ (PrefixOf(body.prefix, state.cut) \/ Variant = "same-position")
    /\ LET tail == SubSeq(state.cut, body.position + 1, Len(state.cut))
           last == IF Len(state.bytes) < Len(state.cut) THEN Len(state.bytes) ELSE Len(state.cut)
           actual == SubSeq(state.bytes, body.position + 1, last)
           prepared == Replay(body, tail)
       IN /\ (tail = actual \/ Variant = "ignore-missing")
          /\ state' = [state EXCEPT !.phase = "staged", !.checkpoint = body,
                       !.live = prepared.live, !.floor = prepared.floor]

Install(replica) ==
    /\ state.phase = "staged"
    /\ replica \notin state.stored
    /\ state' = [state EXCEPT !.stored = @ \cup {replica}]

Supersede ==
    /\ Scenario = "superseded" /\ state.phase = "staged" /\ state.current = ActiveSuccessor
    /\ state' = [state EXCEPT !.current = ActiveSuccessor + 1]

AdvanceTarget ==
    /\ Scenario = "advanced" /\ state.phase = "staged" /\ state.stored = {"B", "C"}
    /\ ~state.advanced
    /\ state' = [state EXCEPT !.advanced = TRUE]

LoseTargetQuorum ==
    /\ Scenario = "target-unreachable" /\ state.phase = "staged" /\ state.stored = {"B", "C"}
    /\ state.targetQuorum
    /\ state' = [state EXCEPT !.targetQuorum = FALSE]

Publish ==
    /\ state.phase = "staged"
    /\ (state.stored = {"B", "C"} \/ Variant = "winner-serves")
    /\ (state.current = ActiveSuccessor \/ Variant = "stale-serve")
    /\ (~state.advanced \/ Variant = "ignore-current-cut")
    /\ (state.targetQuorum \/ Variant = "ignore-target-quorum")
    /\ state' = [state EXCEPT !.phase = "served", !.served = TRUE,
                 !.spentBeforeInstall = (state.stored # {"B", "C"}),
                 !.staleAtServe = (state.current # ActiveSuccessor),
                 !.scopeAtServe = (ReportedSuccessor = ActiveSuccessor),
                 !.lateAtServe = state.advanced, !.servedOffline = ~state.targetQuorum]

Next == Capture \/ (\E body \in Images : Stage(body)) \/
        (\E replica \in {"B", "C"} : Install(replica)) \/ Supersede \/ AdvanceTarget \/ LoseTargetQuorum \/ Publish
Spec == Init /\ [][Next]_state
Fair == Spec /\ WF_state(Capture) /\ WF_state(\E body \in Images : Stage(body)) /\
        WF_state(Install("B")) /\ WF_state(Install("C")) /\ WF_state(Publish)

ExactChoice == state.served => state.cut = ExactHistory
CompleteMedia == state.served => Len(state.bytes) >= Len(state.cut)
NeverReopens == state.served => (~state.live /\ state.floor = 2)
InstalledFirst == ~state.spentBeforeInstall
BindsSuccessor == state.served => (state.scopeAtServe /\ ~state.staleAtServe)
AtCurrentCut == ~state.lateAtServe
ReachableInstall == ~state.servedOffline
Progress == <>state.served
=============================================================================
