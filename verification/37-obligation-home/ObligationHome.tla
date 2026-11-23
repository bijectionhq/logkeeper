------------------------------ MODULE ObligationHome ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Sites, Policy, Variant, Scenario
VARIABLE s

Owners == 1..Sites
Keys == {"result", "copy"}
Binding(key) == IF key = "result" THEN 11 ELSE 21
DirectoryUp == Scenario # "locator_down"
AllPredecessorsStopped == s.stopped = 1..(Sites - 1)
Unresolved == {key \in Keys : s.book[key] # 0}

Init ==
    s = [owner |-> 1, locator |-> 1, cached |-> 1, stopped |-> {}, phase |-> "open",
         book |-> [key \in Keys |-> Binding(key)],
         image |-> [key \in Keys |-> 0], charged |-> Keys,
         counterpartsUp |-> Scenario \notin {"debt_endpoints_down", "reconnect_after_shutdown"},
         recorded |-> FALSE, fenced |-> FALSE, discharged |-> {},
         missing |-> {}, changedAfterShutdown |-> {}]

Seal ==
    /\ s.phase = "open" /\ s.owner < Sites
    /\ Policy # "stable" \/ s.locator = s.owner
    /\ s' = [s EXCEPT !.phase = "sealed"]

Stage ==
    /\ s.phase = "sealed"
    /\ s' = [s EXCEPT !.phase = "staged",
         !.image = [key \in Keys |->
             CASE Variant = "omit_result" /\ key = "result" -> 0
               [] Variant = "omit_plan" /\ key = "copy" -> 0
               [] Variant = "rebind_plan" /\ key = "copy" /\ s.book[key] # 0 -> 22
               [] Variant = "stale_image" -> Binding(key)
               [] OTHER -> s.book[key]]]

Install ==
    /\ s.phase = "staged"
    /\ s' = [s EXCEPT !.owner = @ + 1, !.phase = "open", !.book = s.image,
                      !.charged = IF Variant = "forget_charge" THEN {} ELSE {key \in Keys : s.image[key] # 0}]

Publish(candidate) ==
    /\ Policy = "stable" /\ DirectoryUp
    /\ candidate <= s.owner \/ (Variant = "publish_before_install" /\ s.phase # "open" /\ candidate = s.owner + 1)
    /\ candidate > s.locator \/ (Variant = "regress_locator" /\ candidate < s.locator)
    /\ s' = [s EXCEPT !.locator = candidate]

Stop(site) ==
    /\ site < s.owner /\ site \notin s.stopped
    /\ CASE Policy = "stable" -> s.locator > site \/ Variant = "stop_before_publish"
         [] Policy = "hold_forwarders" -> Unresolved = {}
         [] OTHER -> TRUE
    /\ s' = [s EXCEPT !.stopped = @ \cup {site}]

FindsCurrent ==
    IF Policy = "stable"
    THEN s.cached = s.owner /\ s.cached \notin s.stopped
    ELSE s.stopped = {}

Refresh ==
    /\ Policy = "stable" /\ DirectoryUp /\ s.cached # s.locator
    /\ s' = [s EXCEPT !.cached = s.locator]

ReportMissing(key) ==
    /\ Policy = "stable" /\ key \notin s.missing
    /\ (FindsCurrent /\ key \notin Unresolved) \/ (Variant = "stale_is_missing" /\ ~FindsCurrent)
    /\ s' = [s EXCEPT !.missing = @ \cup {key}]

Record ==
    /\ s.counterpartsUp /\ FindsCurrent /\ s.book["result"] = Binding("result") /\ ~s.recorded
    /\ s' = [s EXCEPT !.recorded = TRUE]

Fence ==
    /\ s.counterpartsUp /\ FindsCurrent /\ s.book["copy"] = Binding("copy") /\ ~s.fenced
    /\ s' = [s EXCEPT !.fenced = TRUE]

Reconnect ==
    /\ Scenario = "reconnect_after_shutdown" /\ ~s.counterpartsUp /\ AllPredecessorsStopped
    /\ s' = [s EXCEPT !.counterpartsUp = TRUE]

Discharge(key) ==
    /\ (s.phase = "open" \/ Variant = "post_seal_discharge") /\ FindsCurrent /\ key \in Unresolved
    /\ Variant = "assume_settled" \/ (IF key = "result" THEN s.recorded ELSE s.fenced)
    /\ s' = [s EXCEPT !.book[key] = 0, !.charged = @ \ {key}, !.discharged = @ \cup {key},
                      !.changedAfterShutdown =
                          IF AllPredecessorsStopped
                          THEN @ \cup {key} ELSE @]

PublishSome == \E candidate \in Owners : Publish(candidate)
StopSome == \E site \in Owners : Stop(site)
Next ==
    \/ Seal \/ Stage \/ Install \/ PublishSome \/ StopSome \/ Refresh \/ Record \/ Fence \/ Reconnect
    \/ \E key \in Keys : Discharge(key) \/ ReportMissing(key)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Stage) /\ WF_s(Install) /\ WF_s(PublishSome) /\ WF_s(StopSome)
             /\ WF_s(Refresh) /\ WF_s(Record) /\ WF_s(Fence) /\ WF_s(Reconnect)
             /\ \A key \in Keys : WF_s(Discharge(key))

ExactUnresolvedBook ==
    \A key \in Keys : s.book[key] = IF key \in s.discharged THEN 0 ELSE Binding(key)
ChargeMatchesOutstanding == s.charged = Keys \ s.discharged
OnlyExactSettlement ==
    ("result" \in s.discharged => s.recorded) /\ ("copy" \in s.discharged => s.fenced)
PublishedIsInstalled == s.locator <= s.owner
CurrentOwnerSurvives == s.owner \notin s.stopped
LocatorSurvivesShutdown == \A site \in s.stopped : site < s.locator
NoFalseTerminalAbsence == s.missing \subseteq s.discharged

InstallsSealedCut ==
    \A site \in Owners : (s.owner = site /\ s.phase # "open") ~> (s.owner > site)
CanShutDownPredecessors ==
    \A site \in Owners : (site < s.owner) ~> (site \in s.stopped)
EventuallyDischarges == <> (s.discharged = Keys)
ReconcilesAfterShutdown == AllPredecessorsStopped ~> (s.discharged = Keys)

NeverSettlesAfterAllPredecessorsStop == s.changedAfterShutdown # Keys
NeverLeavesBothDebtsAtLastOwner ==
    ~(s.owner = Sites /\ s.locator = Sites /\ AllPredecessorsStopped /\ s.charged = Keys)
=============================================================================
