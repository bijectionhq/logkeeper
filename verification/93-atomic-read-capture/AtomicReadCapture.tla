--------------------------- MODULE AtomicReadCapture -------------------------
EXTENDS Naturals

CONSTANT Path, Scenario, Variant

VARIABLES phase, current, prepared, matches, credit, readBasis, deliveryBasis, borrowedBasis,
          admitted, completed, route, decisions, refused, charged

vars == <<phase, current, prepared, matches, credit, readBasis, deliveryBasis, borrowedBasis,
          admitted, completed, route, decisions, refused, charged>>

Other(view) == 1 - view
NoBasis == 2
Available == credit = "available"
Covered(view) == Scenario # "uncovered" \/ view = 0
Room == Scenario # "full"
AdvancesFirst == Scenario \in {"churn", "uncovered"}

Init ==
  /\ phase = "prepare"
  /\ current = 0
  /\ prepared = NoBasis
  /\ matches = FALSE
  /\ credit = "available"
  /\ readBasis = NoBasis
  /\ deliveryBasis = NoBasis
  /\ borrowedBasis = NoBasis
  /\ admitted = 0
  /\ completed = FALSE
  /\ route = TRUE
  /\ decisions = 0
  /\ refused = FALSE
  /\ charged = TRUE

Prepare ==
  /\ phase = "prepare"
  /\ prepared' = current
  /\ matches' = TRUE
  /\ phase' = IF AdvancesFirst THEN "advance" ELSE IF Scenario = "fenced" THEN "fence"
               ELSE IF Scenario = "replacement" THEN "replace" ELSE "attempt"
  /\ UNCHANGED <<current, credit, readBasis, deliveryBasis, borrowedBasis, admitted, completed, route, decisions, refused, charged>>

Advance ==
  /\ phase \in {"advance", "advance-after-capture"}
  /\ current' = Other(current)
  /\ matches' = FALSE
  /\ phase' = IF phase = "advance" THEN "attempt" ELSE "grant"
  /\ UNCHANGED <<prepared, credit, readBasis, deliveryBasis, borrowedBasis, admitted, completed, route, decisions, refused, charged>>

ReplaceWriter ==
  /\ phase = "replace"
  /\ phase' = "fence"
  /\ UNCHANGED <<current, prepared, matches, credit, readBasis, deliveryBasis, borrowedBasis,
                 admitted, completed, route, decisions, refused, charged>>

Fence ==
  /\ phase = "fence"
  /\ Available
  /\ (Scenario # "replacement" \/ Variant # "old-writer-only")
  /\ credit' = "fenced"
  /\ phase' = "return"
  /\ UNCHANGED <<current, prepared, matches, readBasis, deliveryBasis, borrowedBasis, admitted, completed, route, decisions, refused, charged>>

Return ==
  /\ phase = "return"
  /\ credit = "fenced"
  /\ credit' = "returned"
  /\ charged' = FALSE
  /\ phase' = "attempt"
  /\ UNCHANGED <<current, prepared, matches, readBasis, deliveryBasis, borrowedBasis, admitted, completed, route, decisions, refused>>

UnilateralReturn ==
  /\ Variant = "provider-withdraws"
  /\ phase = "attempt"
  /\ Available
  /\ charged
  /\ charged' = FALSE
  /\ UNCHANGED <<phase, current, prepared, matches, credit, readBasis, deliveryBasis, borrowedBasis,
                 admitted, completed, route, decisions, refused>>

SplitCapture ==
  /\ Path = "split"
  /\ phase = "attempt"
  /\ readBasis' = current
  /\ decisions' = decisions + 1
  /\ phase' = "prepare-held"
  /\ UNCHANGED <<current, prepared, matches, credit, deliveryBasis, borrowedBasis,
                 admitted, completed, route, refused, charged>>

SplitPrepareHeld ==
  /\ Path = "split"
  /\ phase = "prepare-held"
  /\ prepared' = readBasis
  /\ phase' = IF Scenario = "churn" THEN "advance-after-capture" ELSE "grant"
  /\ UNCHANGED <<current, matches, credit, readBasis, deliveryBasis, borrowedBasis,
                 admitted, completed, route, decisions, refused, charged>>

MayCapture ==
  /\ (Available \/ Variant = "cached-credit")
  /\ Room
  /\ IF Path = "fixed" THEN matches \/ Variant = "trust-overtaken"
      ELSE Covered(current) \/ Variant = "uncovered-credit"

AfterGrant ==
  CASE Scenario = "loss" -> "lose-route"
    [] Scenario = "duplicate" -> "repeat"
    [] OTHER -> "finish"

AtomicCapture ==
  /\ Path # "split"
  /\ phase = "attempt"
  /\ MayCapture
  /\ readBasis' = current
  /\ deliveryBasis' = current
  /\ borrowedBasis' = IF Path = "fixed" THEN prepared ELSE current
  /\ credit' = IF Available THEN "assigned" ELSE credit
  /\ admitted' = admitted + 1
  /\ decisions' = decisions + 1
  /\ phase' = AfterGrant
  /\ UNCHANGED <<current, prepared, matches, completed, route, refused, charged>>

SplitGrant ==
  /\ Path = "split"
  /\ phase = "grant"
  /\ Available /\ Room
  /\ deliveryBasis' = readBasis
  /\ borrowedBasis' = prepared
  /\ credit' = "assigned"
  /\ admitted' = admitted + 1
  /\ decisions' = decisions + 1
  /\ phase' = AfterGrant
  /\ UNCHANGED <<current, prepared, matches, readBasis, completed, route, refused, charged>>

RefuseAtomic ==
  /\ Path # "split"
  /\ phase = "attempt"
  /\ ~MayCapture
  /\ phase' = IF Path = "fixed" /\ Scenario = "churn" THEN "prepare" ELSE "done"
  /\ readBasis' = IF Variant = "keep-partial-capture" THEN current ELSE readBasis
  /\ refused' = TRUE
  /\ UNCHANGED <<current, prepared, matches, credit, deliveryBasis, borrowedBasis,
                 admitted, completed, route, decisions, charged>>

LoseRoute ==
  /\ phase = "lose-route"
  /\ route
  /\ route' = FALSE
  /\ phase' = "finish"
  /\ UNCHANGED <<current, prepared, matches, credit, readBasis, deliveryBasis, borrowedBasis,
                 admitted, completed, decisions, refused, charged>>

Repeat ==
  /\ phase = "repeat"
  /\ phase' = "finish"
  /\ admitted' = IF Variant = "reuse-credit" THEN admitted + 1 ELSE admitted
  /\ credit' = IF Variant = "abandon-assigned" THEN "fenced" ELSE credit
  /\ UNCHANGED <<current, prepared, matches, readBasis, deliveryBasis, borrowedBasis,
                 completed, route, decisions, refused, charged>>

Finish ==
  /\ phase = "finish"
  /\ credit = "assigned"
  /\ (Variant # "recontact" \/ route)
  /\ completed' = TRUE
  /\ phase' = "done"
  /\ UNCHANGED <<current, prepared, matches, credit, readBasis, deliveryBasis, borrowedBasis,
                 admitted, route, decisions, refused, charged>>

Exact == deliveryBasis # NoBasis => deliveryBasis = readBasis /\ borrowedBasis = readBasis
Funded == deliveryBasis # NoBasis => credit = "assigned" /\ charged /\ Covered(borrowedBasis)
Atomic == Path # "split" => (readBasis = NoBasis) = (deliveryBasis = NoBasis)
NoReuse == admitted <= 1
FewerDecisions == Path = "delegated" => decisions <= 1
Finishes == <> completed
Refuses == <> (phase = "done" /\ refused)
ReturnsAfterReplacement == <> (phase = "done" /\ refused /\ credit = "returned" /\ ~charged)

Next == Prepare \/ Advance \/ ReplaceWriter \/ Fence \/ Return \/ UnilateralReturn \/ SplitCapture \/ SplitPrepareHeld \/
        AtomicCapture \/ SplitGrant \/ RefuseAtomic \/ LoseRoute \/ Repeat \/ Finish
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
