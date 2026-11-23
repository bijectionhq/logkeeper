---------------------------- MODULE FiniteInventory ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Budget, MaxSerial, MaxEpoch, Scenario, Variant

Scopes == 1..MaxSerial
Initial == [issued |-> 0, rows |-> {}, epoch |-> [scope \in Scopes |-> 0],
            mode |-> [scope \in Scopes |-> "absent"]]

VARIABLES state, chosen, stable, visible, ever, reused, cached, fresh, admittedStale, recoveredOlder
vars == <<state, chosen, stable, visible, ever, reused, cached, fresh, admittedStale, recoveredOlder>>
NoProof == <<0, 0>>

Init ==
    /\ state = Initial /\ chosen = Initial /\ stable = Initial /\ visible = Initial
    /\ ever = {} /\ reused = FALSE /\ cached = NoProof /\ fresh = FALSE /\ admittedStale = FALSE
    /\ recoveredOlder = FALSE

Choose(next) == /\ state' = next /\ chosen' = next

Issue ==
    /\ state.issued < MaxSerial \/ Variant = "wrap_issuer"
    /\ Cardinality(state.rows) < Budget
    /\ LET next == IF state.issued = MaxSerial THEN 1 ELSE state.issued + 1
       IN /\ next \notin state.rows
          /\ Choose([state EXCEPT !.issued = next, !.rows = @ \cup {next},
                                  !.epoch[next] = 0, !.mode[next] = "quarantine"])
          /\ ever' = ever \cup {next}
          /\ reused' = (reused \/ next \in ever)
    /\ UNCHANGED <<stable, visible, cached, fresh, admittedStale, recoveredOlder>>

Fault(scope) ==
    /\ scope \in state.rows /\ state.mode[scope] \in {"serving", "quarantine"}
    /\ LET maximum == state.epoch[scope] = MaxEpoch
       IN Choose([state EXCEPT !.epoch[scope] = IF maximum THEN @ ELSE @ + 1,
                              !.mode[scope] = IF maximum /\ Variant # "reuse_epoch"
                                             THEN "sealed" ELSE "offline"])
    /\ fresh' = (fresh /\ cached[1] # scope)
    /\ UNCHANGED <<stable, visible, ever, reused, cached, admittedStale, recoveredOlder>>

Reconnect(scope) ==
    /\ scope \in state.rows /\ state.mode[scope] = "offline"
    /\ Choose([state EXCEPT !.mode[scope] = "quarantine"])
    /\ UNCHANGED <<stable, visible, ever, reused, cached, fresh, admittedStale, recoveredOlder>>

Probe(scope) ==
    /\ scope \in state.rows /\ state.mode[scope] = "quarantine"
    /\ cached' = <<scope, state.epoch[scope]>>
    /\ fresh' = TRUE
    /\ UNCHANGED <<state, chosen, stable, visible, ever, reused, admittedStale, recoveredOlder>>

Validate(scope) ==
    /\ scope \in state.rows /\ state.mode[scope] = "quarantine"
    /\ cached = <<scope, state.epoch[scope]>>
    /\ Choose([state EXCEPT !.mode[scope] = "serving"])
    /\ admittedStale' = (admittedStale \/ ~fresh)
    /\ UNCHANGED <<stable, visible, ever, reused, cached, fresh, recoveredOlder>>

Settle(scope) ==
    /\ scope \in state.rows /\ state.mode[scope] \in {"offline", "sealed"}
    /\ Choose([state EXCEPT !.rows = @ \ {scope}])
    /\ UNCHANGED <<stable, visible, ever, reused, cached, fresh, admittedStale, recoveredOlder>>

Publish ==
    /\ Scenario = "checkpoint" /\ visible = stable /\ state # visible
    /\ visible' = state
    /\ UNCHANGED <<state, chosen, stable, ever, reused, cached, fresh, admittedStale, recoveredOlder>>

Sync ==
    /\ Scenario = "checkpoint" /\ stable # visible
    /\ stable' = visible
    /\ UNCHANGED <<state, chosen, visible, ever, reused, cached, fresh, admittedStale, recoveredOlder>>

Recover(image) ==
    /\ Scenario = "checkpoint" /\ image \in {stable, visible}
    /\ state' = IF Variant = "skip_tail" THEN image ELSE chosen
    /\ recoveredOlder' = (recoveredOlder \/
        (image = stable /\ stable # visible /\ image # chosen))
    /\ UNCHANGED <<chosen, stable, visible, ever, reused, cached, fresh, admittedStale>>

Next ==
    \/ Issue \/ Publish \/ Sync \/ \E image \in {stable, visible} : Recover(image)
    \/ \E scope \in Scopes :
        Fault(scope) \/ Reconnect(scope) \/ Probe(scope) \/ Validate(scope) \/ Settle(scope)

Spec == Init /\ [][Next]_vars

NoNameReuse == ~reused
NoStaleAccess == ~admittedStale
RecoveredExact == state = chosen
Bounded ==
    /\ Cardinality(state.rows) <= Budget /\ state.issued <= MaxSerial
    /\ \A scope \in state.rows : scope <= state.issued /\ state.epoch[scope] <= MaxEpoch
NeverSettlesAtMax ==
    ~(state.issued = MaxSerial /\ state.rows = {1} /\ state.mode[1] = "serving")
NeverSettlesSealed ==
    ~(1 \in ever /\ 1 \notin state.rows /\ state.mode[1] = "sealed")
NeverRecoversOlderAtMax ==
    ~(recoveredOlder /\ state.issued = MaxSerial /\ state = chosen)
=============================================================================
