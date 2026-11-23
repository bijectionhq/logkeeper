-------------------------- MODULE GrantReadPolicy ---------------------------
EXTENDS Naturals

CONSTANTS Scenario, Variant

OldWidth == IF Scenario = "trim" THEN 2 ELSE 1
NewWidth == 2
WidthOf(grant) == IF grant = 1 \/ Scenario = "failover-without-offer" THEN OldWidth ELSE NewWidth
SuccessorChosen == Scenario \in {"old-selector", "successor", "failover-without-offer"}
OfferMatches == Scenario # "foreign-offer"
OfferReachable == Scenario \notin {"no-offer", "failover-without-offer"}
Nonces == {1, 2}

VARIABLES grant, width, marks, seen, restored, changed, duplicated, oldDelivery
vars == <<grant, width, marks, seen, restored, changed, duplicated, oldDelivery>>

Init ==
  /\ grant = IF Scenario = "old-selector" THEN 2 ELSE 1
  /\ width = WidthOf(grant)
  /\ marks = {}
  /\ seen = {}
  /\ restored = FALSE
  /\ changed = FALSE
  /\ duplicated = FALSE
  /\ oldDelivery = TRUE

Restore ==
  /\ Scenario \in {"alias", "old-selector"}
  /\ ~restored
  /\ Variant # "latest-policy-opens-old" \/ WidthOf(grant) = OldWidth
  /\ width' = IF Variant = "trust-packed-size" THEN 2 ELSE WidthOf(grant)
  /\ restored' = TRUE
  /\ UNCHANGED <<grant, marks, seen, changed, duplicated, oldDelivery>>

AdvanceGrant ==
  /\ grant = 1
  /\ Scenario \in {"successor", "foreign-offer", "failover-without-offer"}
  /\ IF Scenario = "failover-without-offer" THEN Variant # "replacement-requires-offer"
     ELSE OfferReachable /\ (OfferMatches \/ Variant = "trust-other-grant")
  /\ grant' = 2
  /\ width' = IF Scenario = "failover-without-offer" THEN width
               ELSE IF OfferMatches THEN NewWidth ELSE 1
  /\ marks' = {}
  /\ oldDelivery' = (oldDelivery /\ Variant # "forget-old-delivery")
  /\ UNCHANGED <<seen, restored, changed, duplicated>>

InPlaceShrink ==
  /\ Scenario = "trim"
  /\ Variant = "shrink-live-window"
  /\ ~changed
  /\ <<1, 2>> \in seen
  /\ changed' = TRUE
  /\ width' = 1
  /\ marks' = marks \ {2}
  /\ UNCHANGED <<grant, seen, restored, duplicated, oldDelivery>>

CanStart ==
  CASE Scenario \in {"alias", "old-selector"} -> restored
    [] Scenario = "successor" -> grant = 2
    [] OTHER -> TRUE

Arrived(nonce) ==
  IF Scenario = "trim" THEN nonce = 2 \/ changed
  ELSE IF Scenario = "foreign-offer" THEN FALSE ELSE TRUE

Open(nonce) ==
  /\ CanStart
  /\ Arrived(nonce)
  /\ nonce \notin marks
  /\ nonce <= width \/ 1 \in marks
  /\ OfferReachable \/ Variant # "policy-needed-on-every-call"
  /\ marks' = marks \cup {nonce}
  /\ seen' = seen \cup {<<grant, nonce>>}
  /\ duplicated' = (duplicated \/ <<grant, nonce>> \in seen)
  /\ UNCHANGED <<grant, width, restored, changed, oldDelivery>>

Next ==
  Restore \/ AdvanceGrant \/ InPlaceShrink \/ (\E nonce \in Nonces : Open(nonce))

Spec == Init /\ [][Next]_vars
Fair ==
  /\ Spec
  /\ WF_vars(Restore) /\ WF_vars(AdvanceGrant)
  /\ \A nonce \in Nonces : WF_vars(Open(nonce))

ExactWidth == width = WidthOf(grant)
NoDuplicate == ~duplicated
CurrentGrantAuthorized == (grant = 2) => SuccessorChosen
OldUsePersists == oldDelivery
Progress ==
  <>(CASE Scenario = "trim" -> <<1, 2>> \in seen
      [] Scenario = "foreign-offer" -> grant = 1
      [] Scenario = "alias" -> restored /\ <<1, 1>> \in seen
      [] Scenario = "old-selector" -> restored /\ <<2, 2>> \in seen
      [] Scenario = "successor" -> grant = 2 /\ <<2, 2>> \in seen
      [] Scenario = "failover-without-offer" -> grant = 2 /\ <<2, 1>> \in seen
      [] OTHER -> <<1, 1>> \in seen)

=============================================================================
