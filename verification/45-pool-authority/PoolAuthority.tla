------------------------------ MODULE PoolAuthority ------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS Tickets, Width, Variant
VARIABLE s

Serials == 1..Tickets
Weight(k) == IF k % 2 = 0 THEN 2 ELSE 1
Live(k) == s.rows[k] # "empty"

RECURSIVE SumLive(_)
SumLive(ks) ==
    IF ks = {} THEN 0 ELSE LET k == CHOOSE k \in ks : TRUE IN
        (IF Live(k) THEN Weight(k) ELSE 0) + SumLive(ks \ {k})

Used == s.ordinary + SumLive(Serials)
Closed(k) == ~Live(k) /\ (k <= s.floor \/ k \in s.spent)

Init ==
    s = [issued |-> 0, offered |-> 0, installed |-> 0, floor |-> 0,
         rows |-> [k \in Serials |-> "empty"], spent |-> {},
         decision |-> [k \in Serials |-> "open"], seen |-> {},
         ordinary |-> 0, limit |-> 3, owner |-> 1, staged |-> FALSE,
         oldOnline |-> TRUE, delayedRefused |-> FALSE, staleEffect |-> FALSE, stagedRows |-> <<>>,
         released |-> {}, everBound |-> {}, stagedWithHold |-> FALSE,
         hadAdvancedFloor |-> FALSE, activatedAtNew |-> {},
         sealedWithPendingBind |-> {}, shrankWithLive |-> FALSE, limitAtSeal |-> 0]

PoolOpen(owner) ==
    (s.owner = owner /\ owner # 0) \/
    (Variant = "old_owner_can_act" /\ owner = 1 /\ s.owner = 2)

Plan ==
    /\ s.issued < Tickets
    /\ s.issued - (IF Variant = "credit_from_offer" THEN s.offered ELSE s.installed) < Width
    /\ s' = [s EXCEPT !.issued = @ + 1]

Prepare(k, owner) ==
    /\ PoolOpen(owner) /\ k <= s.issued /\ ~Live(k)
    /\ k > s.floor /\ k \notin s.spent
    /\ Used + Weight(k) <= s.limit
    /\ s' = [s EXCEPT !.rows[k] = "prepared", !.staleEffect = @ \/ owner # s.owner]

ObserveHold(k) ==
    /\ s.rows[k] = "prepared" /\ k \notin s.seen
    /\ s' = [s EXCEPT !.seen = @ \cup {k}]

Decide(k, outcome) ==
    /\ k <= s.issued /\ s.decision[k] = "open"
    /\ outcome = "abort" \/ k \in s.seen
    /\ s' = [s EXCEPT !.decision[k] = outcome]

ApplyBind(k) ==
    /\ s.owner # 0 /\ s.decision[k] = "bind" /\ s.rows[k] = "prepared"
    /\ s' = [s EXCEPT !.rows[k] = "committed", !.everBound = @ \cup {k},
         !.activatedAtNew = IF s.owner = 2 /\ ~s.oldOnline THEN @ \cup {k} ELSE @]

ApplyCancel(k) ==
    /\ s.owner # 0 /\ s.decision[k] = "abort" /\ ~Closed(k)
    /\ s' = [s EXCEPT !.rows[k] = "empty", !.released = @ \cup {k},
                      !.spent = IF k > s.floor THEN @ \cup {k} ELSE @]

Offer(through) ==
    /\ s.offered < through /\ through <= s.issued
    /\ \A k \in 1..through : k \in s.seen \/ s.decision[k] = "abort"
    /\ s' = [s EXCEPT !.offered = through]

InstallFloor ==
    /\ s.owner # 0 /\ s.floor < s.offered
    /\ s' = [s EXCEPT !.floor = s.offered,
              !.spent = IF Variant = "retain_markers" THEN @ ELSE @ \ (1..s.offered)]

ObserveFloor ==
    /\ s.installed < s.floor
    /\ s' = [s EXCEPT !.installed = s.floor]

Ordinary(change) ==
    /\ s.owner # 0 /\ s.ordinary + change >= 0
    /\ (IF Variant = "ignore_prepared" THEN s.ordinary ELSE Used) + change <= s.limit
    /\ s' = [s EXCEPT !.ordinary = @ + change]

Shrink ==
    /\ s.owner # 0 /\ s.limit = 3
    /\ Used <= 2 \/ Variant = "shrink_under_load"
    /\ s' = [s EXCEPT !.limit = 2, !.shrankWithLive = (s.owner = 1 /\ \E k \in Serials : Live(k))]

Stage ==
    /\ s.owner = 1 /\ ~s.staged
    /\ s' = [s EXCEPT !.staged = TRUE, !.stagedWithHold = (\E k \in Serials : Live(k)),
                     !.stagedRows = IF Variant = "stale_precopy" THEN s.rows ELSE @]

Seal ==
    /\ s.owner = 1 /\ s.staged
    /\ s' = [s EXCEPT !.owner = 0, !.limitAtSeal = s.limit,
        !.sealedWithPendingBind = {k \in Serials : s.decision[k] = "bind" /\ s.rows[k] = "prepared"}]

Disconnect ==
    /\ s.owner # 1 /\ s.oldOnline
    /\ s' = [s EXCEPT !.oldOnline = FALSE]

Install ==
    /\ s.owner = 0
    /\ Variant # "needs_old_owner" \/ s.oldOnline
    /\ s' = [s EXCEPT !.owner = 2, !.hadAdvancedFloor = s.floor > 0,
         !.limit = IF Variant = "forget_limit" THEN 3 ELSE @,
         !.floor = IF Variant = "lose_floor" THEN 0 ELSE @,
         !.spent = IF Variant = "lose_spent" THEN {} ELSE @,
         !.rows = CASE Variant = "lose_live" -> [k \in Serials |-> "empty"]
                    [] Variant = "stale_precopy" -> s.stagedRows
                    [] OTHER -> @]

DeliverClosed(k) ==
    /\ s.owner = 2 /\ k \in s.released /\ k <= s.floor /\ Closed(k)
    /\ ~s.delayedRefused
    /\ s' = [s EXCEPT !.delayedRefused = TRUE]

Next ==
    \/ Plan \/ InstallFloor \/ ObserveFloor \/ Shrink \/ Stage \/ Seal \/ Disconnect \/ Install
    \/ \E change \in {-1, 1} : Ordinary(change)
    \/ \E k \in Serials : Prepare(k, 1) \/ Prepare(k, 2) \/ ObserveHold(k) \/
         Decide(k, "abort") \/ Decide(k, "bind") \/ ApplyBind(k) \/ ApplyCancel(k) \/ Offer(k) \/ DeliverClosed(k)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Install) /\ \A k \in Serials : WF_s(ApplyBind(k)) /\ WF_s(ApplyCancel(k))

Bounds == Used <= s.limit
LimitDoesNotRegress == s.owner = 2 => s.limit <= s.limitAtSeal
ClosedRemainsClosed == \A k \in s.released : Closed(k)
ObservedHoldPreserved == \A k \in s.seen : s.decision[k] # "abort" => Live(k)
CommittedPreserved == \A k \in s.everBound : s.rows[k] = "committed"
OldCannotMutate == ~s.staleEffect
InstalledCreditMatches == s.installed <= s.floor /\ s.floor <= s.offered /\ s.issued - s.floor <= Width
CancellationBound ==
    Cardinality(s.spent) <= Width /\ s.spent \subseteq (s.floor + 1)..s.issued
MarkerCountBound == Cardinality(s.spent) <= Width
SealedOwnerInstalls == (s.owner = 0) ~> (s.owner = 2)
DecisionsReachRows ==
    \A k \in Serials : ((s.decision[k] = "bind") ~> (s.rows[k] = "committed"))
                      /\ ((s.decision[k] = "abort") ~> (Closed(k)))

NeverRecoversLiveAndRefusesClosed ==
    ~(s.delayedRefused /\ ~s.oldOnline /\ s.hadAdvancedFloor /\ s.stagedWithHold /\
      s.activatedAtNew \cap s.sealedWithPendingBind # {})
NeverShrinksWithLiveHold ==
    ~(s.limit = 2 /\ s.owner = 2 /\ s.shrankWithLive)
=============================================================================
