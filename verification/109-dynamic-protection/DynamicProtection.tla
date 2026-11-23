------------------------------ MODULE DynamicProtection ------------------------------
EXTENDS FiniteSets

CONSTANTS Scenario, Policy
VARIABLES phase, canceled, offered, held, observed, fenced, pending, bytes,
          older, controlOnline, readyUnder, spent

vars == <<phase, canceled, offered, held, observed, fenced, pending, bytes,
          older, controlOnline, readyUnder, spent>>
Zones == {"A", "B", "C"}
Planned == CASE Scenario = "renewal" -> {"B"}
             [] Scenario \in {"cancel", "after-publication", "offline-publication", "renewal-covered"} -> {"B", "C"}
             [] OTHER -> {"A", "B"}
RenewalScenario == Scenario \in {"renewal", "renewal-covered"}
CurrentCases == IF spent THEN {"A"} ELSE Zones
Covers(copies, failures) == \A lost \in failures : copies \ {lost} # {}
OldPlan == {"B", "C"}

Init ==
  /\ phase = "idle"
  /\ canceled = FALSE
  /\ offered = {}
  /\ held = {}
  /\ observed = {}
  /\ fenced = {}
  /\ pending = {}
  /\ bytes = Zones
  /\ older = TRUE
  /\ controlOnline = TRUE
  /\ readyUnder = {}
  /\ spent = RenewalScenario

Prepare ==
  /\ phase = "idle"
  /\ phase' = "preparing"
  /\ UNCHANGED <<canceled, offered, held, observed, fenced, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

Send(copy) ==
  /\ phase = "preparing"
  /\ copy \in Planned \ offered
  /\ offered' = offered \cup {copy}
  /\ UNCHANGED <<phase, canceled, held, observed, fenced, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

Acquire(copy) ==
  /\ controlOnline
  /\ copy \in offered \ held
  /\ copy \notin fenced \/ Policy = "ignore-cancel-fence"
  /\ copy \in bytes
  /\ copy \notin pending \/ Policy = "pin-withdrawing"
  /\ held' = held \cup {copy}
  /\ UNCHANGED <<phase, canceled, offered, observed, fenced, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

Reply(copy) ==
  /\ Scenario # "cancel"
  /\ copy \in held \ observed
  /\ observed' = observed \cup {copy}
  /\ UNCHANGED <<phase, canceled, offered, held, fenced, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

Qualify ==
  /\ phase = "preparing"
  /\ Planned \subseteq observed
  /\ Covers(Planned, CurrentCases)
  /\ readyUnder = {}
  /\ readyUnder' = CurrentCases
  /\ UNCHANGED <<phase, canceled, offered, held, observed, fenced, pending, bytes,
                 older, controlOnline, spent>>

Publish ==
  /\ (phase = "preparing" \/ (phase = "canceled" /\ Policy = "publish-after-cancel"))
  /\ (readyUnder # {} \/ (Policy = "check-bytes" /\ Planned \subseteq bytes))
  /\ (Covers(Planned, CurrentCases) \/ Policy = "old-qualification")
  /\ Scenario # "offline-publication" \/ ~controlOnline
  /\ ~RenewalScenario \/ ~spent
  /\ Policy # "contact-custodian" \/ controlOnline
  /\ Policy # "same-envelope-only" \/ readyUnder = CurrentCases
  /\ phase' = "published"
  /\ UNCHANGED <<canceled, offered, held, observed, fenced, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

Cancel ==
  /\ Scenario \in {"cancel", "after-publication"}
  /\ ~canceled
  /\ Scenario # "cancel" \/ held # {}
  /\ phase = "preparing" \/ (phase = "published" /\ Policy = "infer-abort")
  /\ phase' = IF phase = "published" THEN phase ELSE "canceled"
  /\ canceled' = TRUE
  /\ UNCHANGED <<offered, held, observed, fenced, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

CloseAtCustodian(copy) ==
  /\ controlOnline
  /\ canceled
  /\ copy \in Planned \ fenced
  /\ Policy # "need-acquire-reply" \/ copy \in observed
  /\ fenced' = fenced \cup {copy}
  /\ held' = held \ {copy}
  /\ UNCHANGED <<phase, canceled, offered, observed, pending, bytes,
                 older, controlOnline, readyUnder, spent>>

MarkOldUnselectable ==
  /\ Scenario = "protect-old-selector"
  /\ phase = "published"
  /\ older
  /\ older' = FALSE
  /\ UNCHANGED <<phase, canceled, offered, held, observed, fenced, pending, bytes,
                 controlOnline, readyUnder, spent>>

Withdraw(copy) ==
  /\ Scenario \in {"race", "protect-old-selector"}
  /\ copy \in bytes \ pending
  /\ copy \notin held
  /\ ~older \/ copy \notin OldPlan \/ (Policy = "visible-only" /\ phase = "published")
  /\ pending' = pending \cup {copy}
  /\ UNCHANGED <<phase, canceled, offered, held, observed, fenced, bytes,
                 older, controlOnline, readyUnder, spent>>

Effect(copy) ==
  /\ copy \in pending \cap bytes
  /\ bytes' = bytes \ {copy}
  /\ UNCHANGED <<phase, canceled, offered, held, observed, fenced, pending,
                 older, controlOnline, readyUnder, spent>>

Renew ==
  /\ RenewalScenario
  /\ spent
  /\ readyUnder # {}
  /\ Covers(OldPlan, Zones)
  /\ spent' = FALSE
  /\ UNCHANGED <<phase, canceled, offered, held, observed, fenced, pending, bytes,
                 older, controlOnline, readyUnder>>

Disconnect ==
  /\ Scenario = "offline-publication"
  /\ readyUnder # {}
  /\ controlOnline
  /\ controlOnline' = FALSE
  /\ UNCHANGED <<phase, canceled, offered, held, observed, fenced, pending, bytes,
                 older, readyUnder, spent>>

PlanActions ==
  \E copy \in Zones : Send(copy) \/ Acquire(copy) \/ Reply(copy) \/ CloseAtCustodian(copy)
                         \/ Withdraw(copy) \/ Effect(copy)
Next == Prepare \/ PlanActions \/ Qualify \/ Publish \/ Cancel \/ MarkOldUnselectable \/ Renew \/ Disconnect
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Prepare) /\ WF_vars(Qualify) /\ WF_vars(Publish) /\
              WF_vars(Disconnect) /\ WF_vars(Cancel) /\ WF_vars(Renew) /\
              (\A copy \in Zones : WF_vars(Send(copy)) /\ WF_vars(Acquire(copy)) /\
                WF_vars(Reply(copy)) /\ WF_vars(CloseAtCustodian(copy)))

HoldsNeverCountPending == held \cap pending = {}
PublishedHasExactProtection == phase = "published" =>
  /\ Planned \subseteq held \cap bytes
  /\ Covers(Planned, CurrentCases)
NoPublishAfterCancel == canceled => phase # "published"
KeepsOldSelector == older => OldPlan \subseteq bytes
ClosedStaysClosed == held \cap fenced = {}
EventuallyPublishes == <>(phase = "published")
EventuallyClosesCanceled == <>(canceled /\ fenced = Planned /\ held = {})
NeverPublishesWithBothSelectors == ~(phase = "published" /\ older)
NeverRetiresOldAfterSwitch == ~("C" \notin bytes /\ phase = "published" /\ ~older)
======================================================================================
