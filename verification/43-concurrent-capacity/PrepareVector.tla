------------------------------- MODULE PrepareVector -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Policy, Variant, Scenario
VARIABLE s

Intents == 1..2
Zones == 1..2

Init ==
    s = [held |-> [intent \in Intents |-> {}],
         phase |-> [intent \in Intents |-> "preparing"],
         abortProof |-> {}, restarted |-> FALSE, everSealed |-> {}, oldReceiptDelivered |-> FALSE,
         restartWithHold |-> FALSE, fenced |-> [intent \in Intents |-> {}]]

Open(zone) == \A intent \in Intents : zone \notin s.held[intent]
Complete(intent) == s.held[intent] = Zones

Acquire(intent, zone) ==
    /\ s.phase[intent] = "preparing" /\ Open(zone)
    /\ Policy # "ordered" \/ \A earlier \in Zones : earlier < zone => earlier \in s.held[intent]
    /\ s' = [s EXCEPT !.held[intent] = @ \cup {zone}]

AcquireAtomic(intent) ==
    /\ Policy = "atomic" /\ s.phase[intent] = "preparing" /\ \A zone \in Zones : Open(zone)
    /\ s' = [s EXCEPT !.held[intent] = Zones]

DecideSeal(intent) ==
    /\ s.phase[intent] = "preparing"
    /\ Complete(intent) \/ (Variant = "seal_partial" /\ s.held[intent] # {})
    /\ Scenario # "abort_after_restart" \/ intent # 1
    /\ s' = [s EXCEPT !.phase[intent] = "sealed", !.everSealed = @ \cup {intent}]

Install(intent) ==
    /\ s.phase[intent] = "sealed" /\ Complete(intent)
    /\ s' = [s EXCEPT !.phase[intent] = "installed", !.held[intent] = {}]

DecideAbort(intent) ==
    /\ Scenario = "abort_after_restart" /\ intent = 1 /\ s.restarted
    /\ s.phase[intent] = "preparing"
    /\ s' = [s EXCEPT !.phase[intent] = "aborted", !.abortProof = @ \cup {intent}]

Return(intent, zone) ==
    /\ zone \notin s.fenced[intent]
    /\ intent \in s.abortProof \/ (Variant = "timeout_reclaims" /\ s.phase[intent] = "sealed")
    /\ s' = [s EXCEPT !.held[intent] = @ \ {zone}, !.fenced[intent] = @ \cup {zone}]

DelayedOldPrepare(intent, zone) ==
    /\ intent \in s.abortProof /\ Open(zone)
    /\ ~s.oldReceiptDelivered \/ zone \notin s.fenced[intent]
    /\ s' = [s EXCEPT !.oldReceiptDelivered = @ \/ zone \in s.fenced[intent],
        !.held[intent] = IF zone \notin s.fenced[intent] \/ Variant = "reopen_abort" THEN @ \cup {zone} ELSE @]

Restart ==
    /\ ~s.restarted
    /\ s' = [s EXCEPT !.restarted = TRUE, !.restartWithHold = (s.held[1] # {} /\ ~Complete(1))]

AcquireSome(intent) ==
    IF Policy = "atomic" THEN AcquireAtomic(intent)
    ELSE \E zone \in Zones : Acquire(intent, zone)
ReturnSome(intent) == \E zone \in Zones : Return(intent, zone)

Next ==
    \/ Restart
    \/ \E intent \in Intents :
        AcquireSome(intent) \/ DecideSeal(intent) \/ Install(intent) \/ DecideAbort(intent) \/ ReturnSome(intent)
    \/ \E intent \in Intents, zone \in Zones : DelayedOldPrepare(intent, zone)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Restart) /\ \A intent \in Intents :
    WF_s(AcquireSome(intent)) /\ WF_s(DecideSeal(intent)) /\ WF_s(Install(intent))
    /\ WF_s(DecideAbort(intent)) /\ WF_s(ReturnSome(intent))

Exclusive == s.held[1] \cap s.held[2] = {}
SealsOwnAll == \A intent \in Intents : s.phase[intent] = "sealed" => Complete(intent)
TerminalDecisionIsExact == s.everSealed \cap s.abortProof = {}
AbortedCannotReacquire == \A intent \in Intents : s.held[intent] \cap s.fenced[intent] = {}

BothFinish == <> (\A intent \in Intents : s.phase[intent] = "installed")
AbortedRestoresRoom ==
    <> (s.phase[1] = "aborted" /\ s.fenced[1] = Zones /\ s.held[1] = {} /\ s.phase[2] = "installed")
NeverRecoversAContendedPartialAbort ==
    ~(s.restartWithHold /\ s.phase[1] = "aborted" /\ s.held[1] = {} /\
      s.phase[2] = "installed" /\ s.oldReceiptDelivered)
=============================================================================
