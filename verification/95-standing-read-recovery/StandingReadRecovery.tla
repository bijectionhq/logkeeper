--------------------------- MODULE StandingReadRecovery ------------------------
EXTENDS Naturals

CONSTANT Scenario, Variant

VARIABLES phase, placement, watermark, generation, cursor, recorded, oldRef, spent,
          live, wrote, opened, duplicate, rejected

vars == <<phase, placement, watermark, generation, cursor, recorded, oldRef, spent,
          live, wrote, opened, duplicate, rejected>>
Transfer == Scenario = "sealed"
PastCheckpoint == Scenario = "older-base"
CursorLimit == IF Scenario = "cursor-limit" THEN 2 ELSE 4
MissingLive == Scenario = "missing-live"
WrongPlacement == Scenario = "foreign-proof"

Init ==
  /\ phase = "chosen"
  /\ placement = 1
  /\ watermark = 1
  /\ generation = 1
  /\ cursor = 1
  /\ recorded = IF PastCheckpoint THEN 0 ELSE 1
  /\ oldRef = TRUE
  /\ spent = {<<1, 0>>}
  /\ live = ~MissingLive
  /\ wrote = FALSE
  /\ opened = FALSE
  /\ duplicate = FALSE
  /\ rejected = FALSE

CrashOrSeal ==
  /\ phase = "chosen"
  /\ phase' = "reopen"
  /\ placement' = IF Transfer THEN 2 ELSE placement
  /\ UNCHANGED <<watermark, generation, cursor, recorded, oldRef, spent, live,
                 wrote, opened, duplicate, rejected>>

Recover ==
  /\ phase = "reopen"
  /\ Variant # "live-required-for-replay" \/ live
  /\ IF WrongPlacement /\ Variant # "ignore-proof-placement"
        THEN (phase' = "done" /\ rejected' = TRUE)
        ELSE (phase' = (IF Transfer THEN "install" ELSE "ordinary") /\ rejected' = FALSE)
  /\ watermark' = IF Variant = "drop-watermark" THEN 0 ELSE watermark
  /\ generation' = IF Transfer /\ Variant # "carry-old-current" THEN 0 ELSE generation
  /\ cursor' = IF Variant = "reset-empty-book" THEN 0 ELSE
                IF PastCheckpoint /\ Variant # "ignore-chosen-suffix" THEN recorded + 1 ELSE recorded
  /\ UNCHANGED <<placement, recorded, oldRef, spent, live, wrote, opened, duplicate>>

Install ==
  /\ phase = "install"
  /\ \E candidate \in 1..2 :
        /\ candidate > watermark
        /\ generation' = candidate
        /\ watermark' = candidate
        /\ cursor' = 0
  /\ phase' = "ordinary"
  /\ UNCHANGED <<placement, recorded, oldRef, spent, live, wrote, opened, duplicate, rejected>>

Ordinary ==
  /\ phase = "ordinary"
  /\ phase' = "open"
  /\ wrote' = TRUE
  /\ UNCHANGED <<placement, watermark, generation, cursor, recorded, oldRef, spent, live,
                 opened, duplicate, rejected>>

Open ==
  /\ phase = "open"
  /\ phase' = "done"
  /\ IF (live \/ Variant = "historical-proof-authorizes-use") /\
        (cursor + 1 < CursorLimit \/ Variant = "check-issued-id-only")
      THEN /\ opened' = TRUE
           /\ spent' = spent \cup {<<generation, cursor>>}
           /\ duplicate' = (<<generation, cursor>> \in spent)
           /\ cursor' = cursor + 1
           /\ rejected' = FALSE
      ELSE /\ rejected' = TRUE
           /\ UNCHANGED <<opened, spent, duplicate, cursor>>
  /\ UNCHANGED <<placement, watermark, generation, recorded, oldRef, live, wrote>>

RefundOld ==
  /\ Variant = "retire-on-install"
  /\ Transfer
  /\ phase = "ordinary"
  /\ oldRef
  /\ oldRef' = FALSE
  /\ UNCHANGED <<phase, placement, watermark, generation, cursor, recorded, spent, live,
                 wrote, opened, duplicate, rejected>>

CursorFits == cursor < CursorLimit
NoDuplicate == ~duplicate
SealedHasNoCurrent == (phase = "install" /\ Transfer) => generation = 0
NewerAfterTransfer == (Transfer /\ wrote) => generation = 2
KeepsOriginalFunding == oldRef
EligibleScope == (WrongPlacement \/ ~live) => ~opened
Completes == <> (wrote /\ opened)
WritesWithoutOptional == <> (wrote /\ rejected)
RejectsForeign == <> rejected

Next == CrashOrSeal \/ Recover \/ Install \/ Ordinary \/ Open \/ RefundOld
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
