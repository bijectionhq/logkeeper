---------------------- MODULE OrderedPolicyVerifiers ------------------------
EXTENDS Naturals

CONSTANTS Scenario, Variant, Selector

PolicyServiceReachable == FALSE
OldHistory == Scenario = "historical"
CurrentOffer == Scenario = "new-offer"
RivalOffer == Scenario = "rival-offer"

VARIABLES version, verifier, newBase, reopened, restoredWidth, attempted, accepted,
          oldDescriptor, discardedUncovered
vars == <<version, verifier, newBase, reopened, restoredWidth, attempted, accepted, oldDescriptor, discardedUncovered>>

Init ==
  /\ version = 1
  /\ verifier = 1
  /\ newBase = 0
  /\ reopened = FALSE
  /\ restoredWidth = 0
  /\ attempted = FALSE
  /\ accepted = FALSE
  /\ oldDescriptor = TRUE
  /\ discardedUncovered = FALSE

Rotate ==
  /\ version = 1
  /\ PolicyServiceReachable \/ Variant # "rotate-needs-old-signer"
  /\ version' = 2
  /\ verifier' = 2
  /\ UNCHANGED <<newBase, reopened, restoredWidth, attempted, accepted, oldDescriptor, discardedUncovered>>

Publish ==
  /\ version = 2
  /\ newBase = 0
  /\ newBase' = 1
  /\ UNCHANGED <<version, verifier, reopened, restoredWidth, attempted, accepted, oldDescriptor, discardedUncovered>>

Persist ==
  /\ newBase = 1
  /\ Selector = "new" \/ reopened
  /\ newBase' = 2
  /\ UNCHANGED <<version, verifier, reopened, restoredWidth, attempted, accepted, oldDescriptor, discardedUncovered>>

HistoricalKey ==
  IF Variant \in {"use-live-verifier", "skip-unverifiable"} THEN verifier
  ELSE IF oldDescriptor THEN 1 ELSE 0

Restore ==
  /\ OldHistory
  /\ ~reopened
  /\ \/ Selector = "new" /\ newBase = 2
     \/ Selector = "old" /\ newBase = 1 /\ (HistoricalKey = 1 \/ Variant = "skip-unverifiable")
  /\ PolicyServiceReachable \/ Variant # "history-needs-policy-service"
  /\ reopened' = TRUE
  /\ restoredWidth' = IF Variant = "skip-unverifiable" /\ HistoricalKey # 1 THEN 1 ELSE 2
  /\ UNCHANGED <<version, verifier, newBase, attempted, accepted, oldDescriptor, discardedUncovered>>

Collect ==
  /\ oldDescriptor
  /\ newBase = 2 \/ (newBase = 1 /\ Variant = "collect-on-visible")
  /\ oldDescriptor' = FALSE
  /\ discardedUncovered' = (newBase # 2)
  /\ UNCHANGED <<version, verifier, newBase, reopened, restoredWidth, attempted, accepted>>

Attempt ==
  /\ ~OldHistory
  /\ version = 2
  /\ ~attempted
  /\ attempted' = TRUE
  /\ accepted' = (CurrentOffer \/ Variant = "trust-retired-key" \/ (RivalOffer /\ Variant = "trust-fields-outside-signature"))
  /\ UNCHANGED <<version, verifier, newBase, reopened, restoredWidth, oldDescriptor, discardedUncovered>>

Next == Rotate \/ Publish \/ Persist \/ Restore \/ Collect \/ Attempt

Spec == Init /\ [][Next]_vars
Fair ==
  /\ Spec
  /\ WF_vars(Rotate) /\ WF_vars(Publish) /\ WF_vars(Persist) /\ WF_vars(Restore) /\ WF_vars(Collect) /\ WF_vars(Attempt)

NoNewFromRetired == Scenario = "late-old" => ~accepted
ExactSignedPolicy == RivalOffer => ~accepted
HeldAcrossSelectors == ~discardedUncovered
ReplayExact == reopened => restoredWidth = 2
Progress ==
  <>(IF OldHistory THEN reopened /\ (Selector = "old" \/ ~oldDescriptor)
     ELSE attempted /\ (accepted = CurrentOffer))

=============================================================================
