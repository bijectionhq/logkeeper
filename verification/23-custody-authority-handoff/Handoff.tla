------------------------------- MODULE Handoff ------------------------------
EXTENDS Naturals
CONSTANTS OldCount, Variant, Observe
VARIABLE state

Old == 1..OldCount
Fresh == OldCount + 1
Keys == 1..Fresh
Blank == [issued |-> {}, plans |-> {}, terminal |-> {}]

Init ==
    state = [owner |-> "source", source |-> Blank, target |-> Blank,
        image |-> Blank, precopied |-> FALSE, staged |-> FALSE, source_link |-> TRUE, old_link |-> TRUE,
        acquisitions |-> {}, sent_by_source |-> {}, closures |-> {}, held |-> {}, fenced |-> {},
        known_terminal |-> {}, published |-> {}, stale_decision |-> FALSE,
        misrouted |-> FALSE, arrived_after_seal |-> {}, recovered_late |-> FALSE,
        installed_offline |-> FALSE, installed_over_old_pin |-> FALSE, fresh_while_old_pending |-> FALSE]

Book == IF state.owner = "target" THEN state.target ELSE state.source
Deciding == state.owner # "sealed"
Reachable(key) == key = Fresh \/ state.old_link

SetBook(book) ==
    IF state.owner = "target" THEN [state EXCEPT !.target = book]
    ELSE [state EXCEPT !.source = book]

Prepare(key) ==
    /\ (state.owner = "source" /\ state.source_link /\ key \in Old) \/
       (state.owner = "target" /\ key = Fresh)
    /\ key \notin Book.issued
    /\ state' = SetBook([Book EXCEPT !.issued = @ \cup {key}, !.plans = @ \cup {key}])

QueueAcquire(key) ==
    /\ Deciding
    /\ key \in Book.plans \ Book.terminal
    /\ key \notin state.acquisitions
    /\ state' = [state EXCEPT !.acquisitions = @ \cup {key},
        !.sent_by_source = IF Observe /\ state.owner = "source" THEN @ \cup {key} ELSE @]

DeliverAcquire(key) ==
    /\ key \in state.acquisitions /\ Reachable(key)
    /\ LET accepts == key \notin state.fenced
           rebound == accepts /\ key \in Old /\ state.owner = "target" /\ Variant = "rebind_old_intent"
       IN state' = [state EXCEPT !.acquisitions = @ \ {key}, !.sent_by_source = @ \ {key},
            !.held = IF rebound THEN @ \cup {Fresh} ELSE IF accepts THEN @ \cup {key} ELSE @,
            !.misrouted = @ \/ rebound,
            !.arrived_after_seal = IF Observe /\ accepts /\ state.owner # "source" /\ key \in state.sent_by_source
                                    THEN @ \cup {key} ELSE @]

Cancel(key) ==
    /\ Deciding
    /\ key \in Book.plans \ Book.terminal
    /\ LET canceled == SetBook([Book EXCEPT !.terminal = @ \cup {key}])
       IN state' = [canceled EXCEPT !.known_terminal = @ \cup {key},
             !.published = @ \ {key}]

LateSourceCancel(key) ==
    /\ Variant = "source_after_seal" /\ state.owner # "source"
    /\ key \in state.source.plans \ state.source.terminal
    /\ state' = [state EXCEPT !.source.terminal = @ \cup {key}, !.stale_decision = TRUE]

QueueRelease(key) ==
    /\ Deciding
    /\ key \in Book.terminal
    /\ key \notin (state.closures \cup state.fenced)
    /\ state' = [state EXCEPT !.closures = @ \cup {key}]

DeliverRelease(key) ==
    /\ key \in state.closures /\ Reachable(key)
    /\ state' = [state EXCEPT !.closures = @ \ {key}, !.held = @ \ {key}, !.fenced = @ \cup {key}]

Forget(key) ==
    /\ Deciding
    /\ key \in Book.terminal
    /\ key \in state.fenced \/ (Variant = "absence_is_settled" /\ Reachable(key) /\ key \notin state.held)
    /\ state' = SetBook([Book EXCEPT !.plans = @ \ {key}, !.terminal = @ \ {key}])

Publish(key) ==
    /\ Deciding
    /\ key \in Book.plans \ Book.terminal
    /\ Reachable(key) /\ key \in state.held \ state.published
    /\ state' = [state EXCEPT !.published = @ \cup {key},
        !.fresh_while_old_pending = @ \/
          (Observe /\ key = Fresh /\ ~state.source_link /\ ~state.old_link /\
           (Old \cap state.target.plans \cap state.held) # {})]

Seal ==
    /\ state.owner = "source" /\ state.source_link
    /\ state' = [state EXCEPT !.owner = "sealed",
          !.image = IF Variant = "observed_only" THEN [state.source EXCEPT !.plans = @ \cap state.held]
                   ELSE IF Variant = "stale_precopy" /\ state.precopied THEN @
                   ELSE state.source]

Precopy ==
    /\ Variant = "stale_precopy" /\ state.owner = "source" /\ state.source_link /\ ~state.precopied
    /\ state' = [state EXCEPT !.precopied = TRUE, !.image = state.source]

Stage ==
    /\ state.owner = "sealed" /\ state.source_link /\ ~state.staged
    /\ state' = [state EXCEPT !.staged = TRUE]

Install ==
    /\ state.owner = "sealed" /\ state.staged
    /\ Variant # "needs_old_issuer" \/ state.source_link
    /\ state' = [state EXCEPT !.owner = "target",
         !.target = IF Variant = "forget_terminal" THEN [state.image EXCEPT !.terminal = {}]
                    ELSE state.image,
         !.installed_offline = Observe /\ ~state.source_link,
         !.installed_over_old_pin = Observe /\ ~state.old_link /\ (state.held \cap Old) # {}]

RecoverLate(key) ==
    /\ Observe /\ state.owner = "target" /\ ~state.source_link
    /\ key \in state.arrived_after_seal \cap state.target.plans \cap state.held
    /\ key \notin state.target.terminal
    /\ state.old_link /\ ~state.recovered_late
    /\ state' = [state EXCEPT !.recovered_late = TRUE]

ToggleSource == state' = [state EXCEPT !.source_link = ~@]
ToggleOldProvider ==
    /\ state.old_link \/ Variant # "permanent_old_loss"
    /\ state' = [state EXCEPT !.old_link = ~@]

Next ==
    \/ Seal \/ Precopy \/ Stage \/ Install \/ ToggleSource \/ ToggleOldProvider
    \/ \E key \in Keys : Prepare(key) \/ QueueAcquire(key) \/ DeliverAcquire(key) \/
       Cancel(key) \/ LateSourceCancel(key) \/ QueueRelease(key) \/ DeliverRelease(key) \/
       Forget(key) \/ Publish(key) \/ RecoverLate(key)

Spec == Init /\ [][Next]_state
FairSpec ==
    /\ Spec
    /\ WF_state(Install)
    /\ \A key \in Keys : WF_state(QueueRelease(key)) /\ WF_state(DeliverRelease(key))

EveryPossibleGrantRemainsKnown ==
    (state.held \cup (state.acquisitions \ state.fenced)) \subseteq Book.plans
PublishedIsLive == state.published \subseteq state.held \ Book.terminal
TerminalDecisionsSurvive ==
    state.known_terminal \subseteq (Book.terminal \cup state.fenced)
RecordedPlansSurvive == state.source.plans \subseteq (Book.plans \cup state.fenced)
NoLateSourceDecision == ~state.stale_decision
NoPhysicalRetargeting == ~state.misrouted

StagedEventuallyInstalls == (state.staged) ~> (state.owner = "target")
OldCancellationSettles ==
    (<>[](state.owner = "target" /\ state.old_link)) =>
      (\A key \in Old : (key \in state.target.terminal) ~> (key \in state.fenced))
OldCancellationSettlesWithoutAccess ==
    (<>[](state.owner = "target")) =>
      (\A key \in Old : (key \in state.target.terminal) ~> (key \in state.fenced))

NeverRecoversLateAndSettles ==
    ~(state.installed_offline /\ state.recovered_late /\ (state.arrived_after_seal \cap state.fenced) # {})
NeverContinuesWithOldUnavailable ==
    ~(state.installed_offline /\ state.installed_over_old_pin /\ state.fresh_while_old_pending)
NeverCarriesCancellationAndSettlesOffline ==
    ~(state.installed_offline /\ (state.image.terminal \cap state.fenced) # {})
=============================================================================
