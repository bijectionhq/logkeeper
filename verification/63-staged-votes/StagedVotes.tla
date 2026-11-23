----------------------------- MODULE StagedVotes -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Capacity, Limit, Variant, Scenario
Slots == 1..Capacity
Attempts == 1..Limit
None == <<0, 0>>
Frame(attempt) == <<attempt, IF attempt % 2 = 0 THEN 2 ELSE 1>>

VARIABLES issued, scope, created, durable, named, charged, accepted, pin, rotated, replaced
vars == <<issued, scope, created, durable, named, charged, accepted, pin, rotated, replaced>>

Init ==
    /\ issued = 0 /\ scope = [slot \in Slots |-> 0]
    /\ created = [id \in Attempts |-> 0]
    /\ durable = [slot \in Slots |-> None] /\ named = {}
    /\ charged = {} /\ accepted = None /\ pin = None /\ rotated = FALSE /\ replaced = FALSE

Grant(slot) ==
    /\ issued < Limit /\ scope[slot] = 0
    /\ issued' = issued + 1
    /\ scope' = [scope EXCEPT ![slot] = issued']
    /\ created' = [created EXCEPT ![issued'] = slot]
    /\ charged' = charged \cup {slot}
    /\ UNCHANGED <<durable, named, accepted, pin, rotated, replaced>>

SyncBytes(id) ==
    LET slot == created[id] IN
    /\ slot \in Slots /\ slot \in charged
    /\ scope[slot] = id \/ Variant = "late_effect"
    /\ durable[slot] = None \/ Variant = "late_effect"
    /\ durable' =
        IF Variant = "logical_offset" /\ accepted # None /\ slot # accepted[1]
        THEN [durable EXCEPT ![slot] = Frame(id), ![accepted[1]] = Frame(id)]
        ELSE [durable EXCEPT ![slot] = Frame(id)]
    /\ UNCHANGED <<issued, scope, created, named, charged, accepted, pin, rotated, replaced>>

SyncPath(slot) ==
    /\ scope[slot] # 0
    /\ named' = named \cup {slot}
    /\ UNCHANGED <<issued, scope, created, durable, charged, accepted, pin, rotated, replaced>>

Vote(slot) ==
    /\ scope[slot] > accepted[2]
    /\ durable[slot] = Frame(scope[slot]) \/ Variant = "skip_bytes"
    /\ slot \in named \/ Variant = "skip_path"
    /\ accepted' = <<slot, scope[slot]>>
    /\ replaced' = (replaced \/ accepted # None)
    /\ rotated' = (rotated \/ (pin[2] = 1 /\ accepted[2] = 2 /\ scope[slot] = 3))
    /\ UNCHANGED <<issued, scope, created, durable, named, charged, pin>>

Pin ==
    /\ Scenario = "older_pin" /\ pin = None /\ accepted # None
    /\ pin' = accepted
    /\ UNCHANGED <<issued, scope, created, durable, named, charged, accepted, rotated, replaced>>

Reclaim(slot) ==
    /\ slot \in charged /\ slot # accepted[1]
    /\ slot # pin[1] \/ Variant = "drop_pin"
    /\ scope' = [scope EXCEPT ![slot] = 0]
    /\ durable' = [durable EXCEPT ![slot] = None]
    /\ named' = named \ {slot} /\ charged' = charged \ {slot}
    /\ UNCHANGED <<issued, created, accepted, pin, rotated, replaced>>

ForgetDebit(slot) ==
    /\ Variant = "unpaid_stage" /\ slot \in charged
    /\ charged' = charged \ {slot}
    /\ UNCHANGED <<issued, scope, created, durable, named, accepted, pin, rotated, replaced>>

Next ==
    \/ Pin
    \/ \E slot \in Slots : Grant(slot) \/ SyncPath(slot) \/ Vote(slot) \/ Reclaim(slot) \/ ForgetDebit(slot)
    \/ \E id \in Attempts : SyncBytes(id)
Spec == Init /\ [][Next]_vars

Exact(ref) ==
    ref = None \/ (ref[1] \in Slots /\ ref[1] \in charged /\ ref[1] \in named /\
      scope[ref[1]] = ref[2] /\ durable[ref[1]] = Frame(ref[2]))
HasExactReport == Exact(accepted)
HasExactPin == Exact(pin)
HasPaidWork == \A slot \in Slots :
    (scope[slot] # 0 \/ durable[slot] # None \/ slot \in named) => slot \in charged
EveryVersionScoped == \A slot \in Slots : durable[slot] # None => durable[slot] = Frame(scope[slot])
OldWriteExcluded == \A id \in Attempts :
    created[id] \in Slots =>
      (scope[created[id]] # id => ~ENABLED SyncBytes(id))
NeverReplace == ~replaced
NeverReplaceWhilePinHeld == ~rotated
NeverAcceptAtReusedAddress == ~(accepted[2] = 2 /\ accepted[1] = created[1])
=============================================================================
