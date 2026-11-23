----------------------------- MODULE SharedExtents -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS ExtentCount, Limit, Policy, Variant, Scenario
VARIABLE s

Uses == 1..2
Pools == 1..2
Extents == 1..ExtentCount
Pool(extent) == IF extent = 3 THEN 2 ELSE 1
Residents == {extent \in Extents : s.media[extent] \in {"pending", "present"}}
LiveReferences(extent) == {use \in Uses : s.binding[use] = extent}
LiveBorrows(extent) == {use \in Uses : s.borrow[use] = extent}

PhysicalUse(pool) == s.ordinary[pool] + Cardinality({extent \in s.charged : Pool(extent) = pool})
Surcharge(pool) ==
    IF Policy = "per_reference" THEN
      Cardinality({extent \in Extents : Pool(extent) = pool /\ Cardinality(LiveReferences(extent)) > 1})
    ELSE 0
Used(pool) == PhysicalUse(pool) + Surcharge(pool)
ControlReachable(extent) == Scenario # "old_unreachable" \/ extent # 1

Init ==
    s = [media |-> [extent \in Extents |-> IF extent = 1 THEN "present" ELSE "unused"],
         charged |-> {1}, closed |-> {}, absence |-> {}, refunded |-> {},
         binding |-> [use \in Uses |-> 0], borrow |-> [use \in Uses |-> 0], finished |-> {},
         ordinary |-> [pool \in Pools |-> 0], recovered |-> {},
         sharedWhileFull |-> FALSE, firstClosedWithBorrow |-> FALSE,
         issuedAcrossPools |-> FALSE, restartWithCharge |-> FALSE,
         recoveredWithBoth |-> {}, originalUseClosed |-> FALSE]

Fill(pool) ==
    /\ Used(pool) < Limit
    /\ s' = [s EXCEPT !.ordinary[pool] = @ + 1]

Reserve(extent) ==
    /\ s.media[extent] = "unused"
    /\ Used(Pool(extent)) < Limit
    /\ s' = [s EXCEPT !.media[extent] = "pending",
         !.charged = IF Variant = "digest_dedup" /\ @ # {} THEN @ ELSE @ \cup {extent},
         !.issuedAcrossPools = @ \/ (Pool(extent) = 2 /\ 1 \in s.charged)]

Land(extent) ==
    /\ s.media[extent] = "pending"
    /\ s' = [s EXCEPT !.media[extent] = "present"]

Attach(use, extent) ==
    /\ s.binding[use] = 0 /\ use \notin s.finished
    /\ s.media[extent] = "present" /\ extent \notin s.closed /\ extent \in s.charged
    /\ Policy # "per_reference" \/ LiveReferences(extent) = {} \/ Used(Pool(extent)) < Limit
    /\ s' = [s EXCEPT !.binding[use] = extent,
         !.sharedWhileFull = @ \/ (extent = 1 /\ LiveReferences(extent) # {} /\
             s.ordinary[1] > 0 /\ PhysicalUse(1) = Limit)]

Borrow(use) ==
    /\ s.binding[use] # 0 /\ s.borrow[use] = 0
    /\ s' = [s EXCEPT !.borrow[use] = s.binding[use]]

CloseUse(use) ==
    /\ s.binding[use] # 0
    /\ LET extent == s.binding[use] IN
       s' = [s EXCEPT !.binding[use] = 0, !.finished = @ \cup {use},
         !.firstClosedWithBorrow = @ \/ (use = 1 /\ s.borrow[use] = 1 /\ s.sharedWhileFull),
         !.originalUseClosed = @ \/ (Scenario = "old_unreachable" /\ use = 1 /\ extent = 1),
         !.charged = IF Variant = "refund_on_reference_release" THEN @ \ {extent} ELSE @]

ReturnBorrow(use) ==
    /\ s.borrow[use] # 0
    /\ s' = [s EXCEPT !.borrow[use] = 0]

CloseExtent(extent) ==
    /\ extent \in Residents /\ extent \notin s.closed /\ LiveReferences(extent) = {}
    /\ s' = [s EXCEPT !.closed = @ \cup {extent}]

Dispose(extent) ==
    /\ extent \in s.closed /\ extent \notin s.absence /\ ControlReachable(extent)
    /\ LiveBorrows(extent) = {} \/ Variant = "ignore_borrow"
    /\ s' = [s EXCEPT !.media[extent] = "absent", !.absence = @ \cup {extent}]

ReturnDebit(extent, proof) ==
    /\ extent \in s.closed /\ extent \in s.charged /\ proof \in s.absence
    /\ proof = extent \/ Variant = "same_digest_receipt"
    /\ s' = [s EXCEPT !.charged = @ \ {extent}, !.refunded = @ \cup {extent}]

Recover(pool) ==
    /\ pool \notin s.recovered
    /\ s' = [s EXCEPT !.recovered = @ \cup {pool},
         !.restartWithCharge = @ \/ (pool = 1 /\ s.firstClosedWithBorrow /\ 1 \in s.charged),
         !.recoveredWithBoth = IF ExtentCount = 3 /\ {1, 3} \subseteq s.charged
           THEN (IF s.media[1] = "present" /\ s.media[3] = "present" THEN @ \cup {pool} ELSE @) ELSE @,
         !.charged = IF Variant = "lose_debits" THEN {extent \in @ : Pool(extent) # pool} ELSE @]

Next ==
    \/ \E pool \in Pools : Fill(pool) \/ Recover(pool)
    \/ \E use \in Uses : Borrow(use) \/ CloseUse(use) \/ ReturnBorrow(use) \/
         \E extent \in Extents : Attach(use, extent)
    \/ \E extent \in Extents :
         Reserve(extent) \/ Land(extent) \/ CloseExtent(extent) \/ Dispose(extent) \/
         \E proof \in Extents : ReturnDebit(extent, proof)

Spec == Init /\ [][Next]_s

PoolBounds == \A pool \in Pools : Used(pool) <= Limit
ExactAllocationsCharged == Residents \subseteq s.charged
OldBorrowsCovered == \A use \in Uses :
    s.borrow[use] # 0 => s.media[s.borrow[use]] = "present" /\ s.borrow[use] \in s.charged
LiveReferencesCovered == \A use \in Uses :
    s.binding[use] # 0 => s.media[s.binding[use]] = "present" /\ s.binding[use] \in s.charged
RefundHasExactAbsence == s.refunded \subseteq s.absence

NeverSharesAtFullAndRecovers ==
    ~(s.sharedWhileFull /\ s.firstClosedWithBorrow /\ s.restartWithCharge /\
      s.binding[2] = 1 /\ s.borrow[1] = 1 /\ LiveReferences(1) = {2} /\ 1 \in s.charged)
NeverChargesSameContentInSeparatePools ==
    ~(s.issuedAcrossPools /\ 1 \in s.charged /\ 3 \in s.charged /\ s.media[3] = "present" /\
      s.media[1] = "present" /\ s.recoveredWithBoth = Pools)
NeverChargesARepackAlongsideItsOldBorrow ==
    ~({1, 2} \subseteq s.charged /\ s.borrow[1] = 1 /\ s.binding[2] = 2 /\ PhysicalUse(1) = Limit)
NeverRetainsDebitDuringOutage ==
    ~(Scenario = "old_unreachable" /\ ExtentCount = 3 /\ s.originalUseClosed /\ 1 \in s.closed /\
      1 \in s.charged /\ 3 \in s.charged /\ s.media[1] = "present" /\ s.binding[2] = 3)
=============================================================================
