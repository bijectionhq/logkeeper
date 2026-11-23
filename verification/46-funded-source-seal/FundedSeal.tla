------------------------------ MODULE FundedSeal ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Attempts, Variant, Moving
VARIABLE s

Keys == 1..Attempts
Pools == 1..2
Budget == 2
Occupied(pool) == s.ordinary[pool] + Cardinality({key \in Keys : pool \in s.held[key]})
Full(key) == s.receipts[key] = Pools
Freezes(key) ==
    s.decision[key] = "bound" \/ s.sealed = key

Init ==
    s = [source |-> "active", issued |-> 0, sealed |-> 0,
         decision |-> [key \in Keys |-> "unused"],
         held |-> [key \in Keys |-> {}], receipts |-> [key \in Keys |-> {}],
         fenced |-> [key \in Keys |-> {}], owner |-> [pool \in Pools |-> 1],
         ordinary |-> [pool \in Pools |-> 0], installed |-> FALSE, lostSource |-> FALSE,
         retireRequested |-> FALSE, refused |-> FALSE, retirementWhileMoving |-> FALSE,
         installedFull |-> FALSE]

Plan ==
    /\ s.source = "active" /\ s.issued < Attempts
    /\ \A prior \in 1..s.issued : s.decision[prior] = "abort"
    /\ s' = [s EXCEPT !.issued = @ + 1, !.decision[s.issued + 1] = "planned"]

Prepare(key, pool) ==
    /\ key <= s.issued /\ s.owner[pool] # 0
    /\ pool \notin s.held[key]
    /\ pool \notin s.fenced[key] \/ Variant = "reopen_canceled_key"
    /\ Occupied(pool) < Budget
    /\ \A earlier \in Pools : earlier < pool => earlier \in s.held[key]
    /\ s' = [s EXCEPT !.held[key] = @ \cup {pool}]

ReceiveReceipt(key, pool) ==
    /\ pool \in s.held[key] /\ pool \notin s.receipts[key]
    /\ s' = [s EXCEPT !.receipts[key] = @ \cup {pool}]

Fill(pool) ==
    /\ s.owner[pool] # 0 /\ Occupied(pool) < Budget
    /\ s' = [s EXCEPT !.ordinary[pool] = @ + 1]

MovePool(pool) ==
    /\ Moving /\ s.owner[pool] = 1
    /\ s' = [s EXCEPT !.owner[pool] = 0]

InstallPool(pool) ==
    /\ s.owner[pool] = 0
    /\ s' = [s EXCEPT !.owner[pool] = 2]

SeparateBind(key) ==
    /\ Variant = "split" /\ s.decision[key] = "planned" /\ Full(key)
    /\ s' = [s EXCEPT !.decision[key] = "bound"]

CanSeal(key) ==
    CASE Variant = "split" -> s.decision[key] = "bound"
      [] Variant = "seal_partial" -> s.decision[key] = "planned" /\ s.receipts[key] # {}
      [] Variant = "borrow_old_receipts" ->
             s.decision[key] = "planned" /\ \E earlier \in Keys : Full(earlier)
      [] OTHER -> s.decision[key] = "planned" /\ Full(key)

Seal(key) ==
    /\ s.source = "active" /\ s.sealed = 0 /\ CanSeal(key)
    /\ s' = [s EXCEPT !.source = "sealed", !.sealed = key, !.decision[key] = "bound"]

Abort(key) ==
    /\ s.source = "active" /\ s.decision[key] = "planned"
    /\ s' = [s EXCEPT !.decision[key] = "abort"]

RequestRetirement ==
    /\ ~s.retireRequested
    /\ s' = [s EXCEPT !.retireRequested = TRUE]

RetireSource ==
    /\ s.source = "active" /\ s.retireRequested
    /\ s' = [s EXCEPT !.source = "retired",
         !.decision = IF Variant = "forgotten_plan" THEN @ ELSE
             [key \in Keys |-> IF @[key] = "planned" THEN "abort" ELSE @[key]],
         !.retirementWhileMoving = (\E pool \in Pools : s.owner[pool] = 0) /\
             (\E key \in Keys : s.decision[key] = "planned" /\ Cardinality(s.held[key]) = 1)]

Release(key, pool) ==
    /\ s.owner[pool] # 0 /\ pool \notin s.fenced[key]
    /\ s.decision[key] = "abort" \/
         (Variant = "reclaim_on_retirement" /\ s.retireRequested /\ Freezes(key))
    /\ s' = [s EXCEPT !.held[key] = @ \ {pool}, !.fenced[key] = @ \cup {pool}]

DeliverFenced(key, pool) ==
    /\ s.source = "retired" /\ s.owner[pool] = 2 /\ pool \in s.fenced[key]
    /\ ~s.refused
    /\ s' = [s EXCEPT !.refused = TRUE]

LoseSource ==
    /\ s.source = "sealed" /\ ~s.lostSource
    /\ s' = [s EXCEPT !.lostSource = TRUE]

Install ==
    /\ s.source = "sealed" /\ s.sealed # 0 /\ s.held[s.sealed] = Pools
    /\ Variant # "requires_source_for_install" \/ ~s.lostSource
    /\ s' = [s EXCEPT !.source = "target", !.installed = TRUE,
         !.installedFull = s.lostSource /\ (\A pool \in Pools : Occupied(pool) = Budget)]

RetireTarget ==
    /\ s.source = "target" /\ s.retireRequested
    /\ s' = [s EXCEPT !.source = "retired"]

Next ==
    \/ Plan \/ RequestRetirement \/ RetireSource \/ LoseSource \/ Install \/ RetireTarget
    \/ \E pool \in Pools : Fill(pool) \/ MovePool(pool) \/ InstallPool(pool)
    \/ \E key \in Keys :
        SeparateBind(key) \/ Seal(key) \/ Abort(key) \/
        \E pool \in Pools :
          Prepare(key, pool) \/ ReceiveReceipt(key, pool) \/ Release(key, pool) \/ DeliverFenced(key, pool)

Spec == Init /\ [][Next]_s
Fair ==
    /\ Spec /\ WF_s(Install) /\ WF_s(RetireSource) /\ WF_s(RetireTarget)
    /\ \A pool \in Pools : WF_s(InstallPool(pool)) /\ \A key \in Keys : WF_s(Release(key, pool))

Pointwise == \A pool \in Pools : Occupied(pool) <= Budget
ExactVector == s.sealed = 0 \/ (Full(s.sealed) /\ s.held[s.sealed] = Pools)
FencesHold == \A key \in Keys : s.held[key] \cap s.fenced[key] = {}
NoStrandedCommitment ==
    s.source = "retired" => \A key \in Keys : s.decision[key] = "bound" => s.installed /\ s.sealed = key
RetirementResolvesPlans == s.source = "retired" => \A key \in Keys : s.decision[key] # "planned"
RetirementFinishes == s.retireRequested ~> (s.source = "retired")
AbortsSettle == \A key \in Keys : (s.decision[key] = "abort") ~>
    (s.fenced[key] = Pools /\ s.held[key] = {})
SealedInstalls == (s.source = "sealed") ~> s.installed

NeverRetiresWhilePoolMovesAndCloses ==
    ~(s.retirementWhileMoving /\ s.fenced[1] = Pools /\ s.refused)
NeverInstallsThenRetiresAtCapacity ==
    ~(s.installedFull /\ s.source = "retired" /\ s.sealed # 0)
NeverCancelsThenSealsSecond ==
    ~(s.issued > 1 /\ s.decision[1] = "abort" /\ s.fenced[1] = Pools /\ s.sealed = 2)
=============================================================================
