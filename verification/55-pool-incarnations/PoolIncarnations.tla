---------------------------- MODULE PoolIncarnations --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Budget, MaxScope, MaxEpoch, Variant, Scenario

Scopes == 1..MaxScope
None == <<0, 0, 0>>

VARIABLES issued, registry, mode, epoch, book, cached, opened, charged, disposed
vars == <<issued, registry, mode, epoch, book, cached, opened, charged, disposed>>

Stamp(scope) == <<scope, epoch[scope], book[scope]>>
Ready == {scope \in registry : mode[scope] = "ready"}
Online == {scope \in registry : mode[scope] \in {"ready", "quarantine"}}
StartsOffline == Scenario = "stable_settlement"

Init ==
    /\ issued = 1 /\ registry = {1}
    /\ mode = [scope \in Scopes |->
        IF scope = 1 THEN (IF StartsOffline THEN "unavailable" ELSE "ready") ELSE "unused"]
    /\ epoch = [scope \in Scopes |-> IF scope = 1 /\ StartsOffline THEN 1 ELSE 0]
    /\ book = [scope \in Scopes |-> 0]
    /\ cached = None
    /\ opened = [scope \in Scopes |-> IF scope = 1 /\ ~StartsOffline THEN Stamp(1) ELSE None]
    /\ charged = {1} /\ disposed = {}

Register ==
    /\ issued < MaxScope
    /\ Cardinality(IF Variant = "count_online" THEN Online ELSE registry) < Budget
    /\ issued' = issued + 1
    /\ registry' = registry \cup {issued'}
    /\ mode' = [mode EXCEPT ![issued'] = "quarantine"]
    /\ UNCHANGED <<epoch, book, cached, opened, charged, disposed>>

Fail(scope) ==
    /\ scope \in registry /\ mode[scope] \in {"ready", "quarantine"} /\ epoch[scope] < MaxEpoch
    /\ mode' = [mode EXCEPT ![scope] = "unavailable"]
    /\ epoch' = [epoch EXCEPT ![scope] = @ + 1]
    /\ registry' = IF Variant = "refund_on_fault" THEN registry \ {scope} ELSE registry
    /\ opened' = [opened EXCEPT ![scope] = None]
    /\ UNCHANGED <<issued, book, cached, charged, disposed>>

Reconnect(scope) ==
    /\ scope \in registry /\ mode[scope] = "unavailable"
    /\ Scenario # "stable_settlement" \/ scope # 1
    /\ mode' = [mode EXCEPT ![scope] = "quarantine"]
    /\ UNCHANGED <<issued, registry, epoch, book, cached, opened, charged, disposed>>

Probe(scope) ==
    /\ scope \in registry /\ mode[scope] = "quarantine"
    /\ cached' = Stamp(scope)
    /\ UNCHANGED <<issued, registry, mode, epoch, book, opened, charged, disposed>>

AdvanceBook(scope) ==
    /\ scope \in registry /\ mode[scope] = "quarantine" /\ book[scope] = 0
    /\ book' = [book EXCEPT ![scope] = 1]
    /\ UNCHANGED <<issued, registry, mode, epoch, cached, opened, charged, disposed>>

Validate(scope) ==
    /\ scope \in registry /\ mode[scope] = "quarantine"
    /\ cached # None
    /\ cached[1] = scope \/ Variant = "foreign_scope"
    /\ cached[2] = epoch[scope] \/ Variant = "old_probe"
    /\ cached[3] = book[scope] \/ Variant = "old_book"
    /\ mode' = [mode EXCEPT ![scope] = "ready"]
    /\ opened' = [opened EXCEPT ![scope] = cached]
    /\ UNCHANGED <<issued, registry, epoch, book, cached, charged, disposed>>

Charge(scope) ==
    /\ scope \in Ready /\ scope \notin charged
    /\ charged' = charged \cup {scope}
    /\ UNCHANGED <<issued, registry, mode, epoch, book, cached, opened, disposed>>

RecordDisposition(scope) ==
    /\ scope \in registry /\ mode[scope] = "unavailable"
    /\ mode' = [mode EXCEPT ![scope] = "closed"]
    /\ disposed' = disposed \cup {scope}
    /\ charged' = charged \ {scope}
    /\ UNCHANGED <<issued, registry, epoch, book, cached, opened>>

Forget(scope) ==
    /\ scope \in registry
    /\ mode[scope] = "closed" \/ (Variant = "timeout_forgets" /\ mode[scope] = "unavailable")
    /\ Variant # "settlement_needs_room" \/ Cardinality(registry) < Budget
    /\ registry' = registry \ {scope}
    /\ mode' = [mode EXCEPT ![scope] = "retired"]
    /\ UNCHANGED <<issued, epoch, book, cached, opened, charged, disposed>>

Next ==
    \/ Register
    \/ \E scope \in Scopes :
        Fail(scope) \/ Reconnect(scope) \/ Probe(scope) \/ AdvanceBook(scope) \/ Validate(scope)
        \/ Charge(scope) \/ RecordDisposition(scope) \/ Forget(scope)

Spec == Init /\ [][Next]_vars
FairSettlement ==
    Spec /\ WF_vars(RecordDisposition(1)) /\ WF_vars(Forget(1)) /\ WF_vars(Register)
SlotReplenished == <> (issued = 2 /\ 1 \notin registry)

BoundedBook == Cardinality(registry) <= Budget
AllDebtsRecorded == charged \subseteq registry
FreshValidation == \A scope \in Ready : opened[scope] = Stamp(scope)
TerminalClosure == \A scope \in disposed : scope \notin Ready \cup charged
NoForgottenIssuedScope ==
    \A scope \in 1..issued : scope \notin registry => scope \in disposed
NeverFillWithUnsettledPools ==
    ~(registry = {1, 2} /\ charged = registry /\ Ready = {} /\ issued = 2)
NeverReopenAtFull ==
    ~(registry = {1} /\ epoch[1] = 1 /\ 1 \in Ready)
NeverReuseSettledSlot ==
    ~(1 \in disposed /\ 1 \notin registry /\ charged = {2, 3} /\ 3 \in Ready)
NoThirdScopeBeforeDisposition == issued >= 3 => disposed # {}
=============================================================================
