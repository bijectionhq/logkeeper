-------------------------- MODULE LocalIssuance ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant

Pools == {1, 2}
Plans == {1, 2, 3}
Pool(plan) == IF plan = 2 THEN 2 ELSE 1
Bytes(plan) == IF plan = 3 THEN 2 ELSE 1

VARIABLES arrived, issued, grants, charges, fences, applied, owner, mintedUnder
vars == <<arrived, issued, grants, charges, fences, applied, owner, mintedUnder>>

Init ==
    /\ arrived = {2, 3}
    /\ issued = [pool \in Pools |-> 0]
    /\ grants = [plan \in Plans |-> 0]
    /\ charges = {} /\ fences = {} /\ applied = [plan \in Plans |-> 0]
    /\ owner = [pool \in Pools |-> 0]
    /\ mintedUnder = [plan \in Plans |-> 0]

Used(pool) ==
    Cardinality({plan \in charges : Pool(plan) = pool}) +
    Cardinality({plan \in charges : Pool(plan) = pool /\ Bytes(plan) = 2})

Prepared(plan) == applied[plan] # 0
Identity(plan) ==
    IF Variant = "bare_serial" THEN <<0, applied[plan]>> ELSE <<Pool(plan), applied[plan]>>

Preset(plan) == IF plan = 3 THEN 2 ELSE 1
CanAccept(plan) ==
    Variant # "preset_version" \/ Preset(plan) = issued[Pool(plan)] + 1

Prepare(plan) ==
    /\ plan \in arrived \ fences /\ grants[plan] = 0
    /\ ~Prepared(plan) \/ Variant = "stale_fence"
    /\ CanAccept(plan) /\ Used(Pool(plan)) + Bytes(plan) <= 3
    /\ issued' = [issued EXCEPT ![Pool(plan)] = @ + 1]
    /\ grants' = [grants EXCEPT ![plan] = issued'[Pool(plan)]]
    /\ applied' = [applied EXCEPT ![plan] = grants'[plan]]
    /\ charges' = charges \cup {plan}
    /\ mintedUnder' = [mintedUnder EXCEPT ![plan] = owner[Pool(plan)]]
    /\ UNCHANGED <<arrived, fences, owner>>

DeliverDelayed ==
    /\ 1 \notin arrived /\ Prepared(2) /\ Prepared(3)
    /\ arrived' = arrived \cup {1}
    /\ UNCHANGED <<issued, grants, charges, fences, applied, owner, mintedUnder>>

Fence(plan) ==
    /\ grants[plan] # 0
    /\ fences' = fences \cup {plan}
    /\ grants' = [grants EXCEPT ![plan] = 0]
    /\ UNCHANGED <<arrived, issued, charges, applied, owner, mintedUnder>>

Takeover(pool) ==
    /\ owner[pool] = 0 /\ (\E plan \in charges \cap fences : Pool(plan) = pool)
    /\ owner' = [owner EXCEPT ![pool] = 1]
    /\ issued' = IF Variant = "stale_issued" THEN [issued EXCEPT ![pool] = 0] ELSE issued
    /\ charges' = IF Variant = "stale_debits" THEN {plan \in charges : Pool(plan) # pool} ELSE charges
    /\ fences' = IF Variant = "stale_fence" THEN {plan \in fences : Pool(plan) # pool} ELSE fences
    /\ UNCHANGED <<arrived, grants, applied, mintedUnder>>

Next == DeliverDelayed \/ (\E plan \in Plans : Prepare(plan) \/ Fence(plan))
    \/ (\E pool \in Pools : Takeover(pool))
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(DeliverDelayed) /\ (\A plan \in Plans : WF_vars(Prepare(plan)))

Capacity == \A pool \in Pools : Used(pool) <= 3
AllDecisionsKeepDebits == \A plan \in Plans : Prepared(plan) => plan \in charges
AllDecisionsKeepIdentities ==
    /\ \A plan \in Plans : applied[plan] <= issued[Pool(plan)]
    /\ \A left, right \in Plans : Prepared(left) /\ Prepared(right) /\ left # right =>
        Identity(left) # Identity(right)
EmptyIssuedPlanStaysFenced ==
    \A plan \in Plans : Prepared(plan) /\ grants[plan] = 0 => plan \in fences
ContinuesAfterReorderedDelivery == <> (\A plan \in Plans : Prepared(plan))
NeverPrepareOutOfOrderAfterTakeover ==
    ~(applied[3] = 1 /\ applied[2] = 1 /\ applied[1] = 2 /\ mintedUnder[1] = 1 /\ 3 \in fences)
=============================================================================
