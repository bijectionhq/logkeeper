---------------------------- MODULE StandingReadCredit -------------------------
EXTENDS Naturals

CONSTANT Policy, Scenario, Variant

VARIABLES phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow,
          oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough

vars == <<phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow,
          oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>
HasPrior == Scenario \in {"hidden", "full"}
PipeCapacity == IF Scenario = "full" THEN 1 ELSE 2

Init ==
  /\ phase = "prepare"
  /\ active = "original"
  /\ oldCharge = 1
  /\ newCharge = 0
  /\ prior = 0
  /\ next = 0
  /\ issued = 0
  /\ nextBorrow = "none"
  /\ oldLearned = FALSE
  /\ oldOnline = TRUE
  /\ fence = FALSE
  /\ done = FALSE
  /\ settled = FALSE
  /\ wrote = FALSE
  /\ split = FALSE
  /\ sealedPrior = 0
  /\ installedThrough = 1

Prepare ==
  /\ phase = "prepare"
  /\ phase' = "decide-original"
  /\ newCharge' = IF Scenario \in {"full", "uncovered"} THEN 0 ELSE 1
  /\ UNCHANGED <<active, oldCharge, prior, next, issued, nextBorrow,
                 oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>

OriginalChoice ==
  /\ phase = "decide-original"
  /\ phase' = "seal"
  /\ prior' = IF HasPrior THEN 1 ELSE 0
  /\ issued' = prior'
  /\ UNCHANGED <<active, oldCharge, newCharge, next, nextBorrow, oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>

Seal ==
  /\ phase = "seal"
  /\ phase' = "move"
  /\ fence' = TRUE
  /\ sealedPrior' = IF Variant = "omit-hidden-assignment" THEN 0 ELSE prior
  /\ oldOnline' = (Scenario # "orphan")
  /\ UNCHANGED <<active, oldCharge, newCharge, prior, next, issued, nextBorrow, oldLearned, done, settled, wrote, split, installedThrough>>

Activate ==
  /\ phase = "move"
  /\ fence
  /\ newCharge = 1 \/ Scenario \in {"full", "uncovered"}
  /\ phase' = "serving"
  /\ active' = "successor"
  /\ installedThrough' = 2
  /\ UNCHANGED <<oldCharge, newCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior>>

ReofferOriginal ==
  /\ phase = "serving"
  /\ Scenario = "reoffer"
  /\ active = "successor"
  /\ oldCharge = 1
  /\ (1 > installedThrough \/ Variant = "forget-window-watermark")
  /\ active' = "original"
  /\ installedThrough' = 1
  /\ UNCHANGED <<phase, oldCharge, newCharge, prior, next, issued, nextBorrow,
                 oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior>>

LearnOld ==
  /\ phase = "serving"
  /\ prior # 0
  /\ ~oldLearned
  /\ oldOnline
  /\ oldLearned' = TRUE
  /\ UNCHANGED <<phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>

SettleOld ==
  /\ phase = "serving"
  /\ oldLearned
  /\ ~settled
  /\ oldOnline
  /\ settled' = TRUE
  /\ UNCHANGED <<phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, done, wrote, split, sealedPrior, installedThrough>>

RefundOld ==
  /\ phase = "serving"
  /\ oldOnline
  /\ oldCharge = 1
  /\ fence
  /\ IF Variant = "refund-from-silence" THEN ~oldLearned ELSE sealedPrior = 0 \/ settled
  /\ oldCharge' = 0
  /\ UNCHANGED <<phase, active, newCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>

StageCreditLater ==
  /\ phase = "serving"
  /\ Scenario = "full"
  /\ newCharge = 0
  /\ IF Variant = "ignore-overlap" THEN TRUE ELSE oldCharge + 1 <= PipeCapacity
  /\ newCharge' = 1
  /\ UNCHANGED <<phase, active, oldCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>

Open ==
  /\ phase = "serving"
  /\ active = "successor"
  /\ newCharge = 1
  /\ next = 0
  /\ Policy # "advance-issued-first" \/ Scenario # "orphan" \/ oldOnline
  /\ next' = issued + 1
  /\ issued' = next'
  /\ nextBorrow' = IF Variant = "rebind-old-physical-credit" THEN "original" ELSE active
  /\ UNCHANGED <<phase, active, oldCharge, newCharge, prior, oldLearned, oldOnline, fence, done, settled, wrote, split, sealedPrior, installedThrough>>

Complete ==
  /\ phase = "serving"
  /\ next # 0
  /\ ~done
  /\ done' = TRUE
  /\ UNCHANGED <<phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, settled, wrote, split, sealedPrior, installedThrough>>

OrdinaryWrite ==
  /\ phase = "serving"
  /\ Scenario = "uncovered"
  /\ ~wrote
  /\ Variant # "require-fusion-for-publication" \/ newCharge = 1
  /\ wrote' = TRUE
  /\ UNCHANGED <<phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, done, settled, split, sealedPrior, installedThrough>>

SplitRead ==
  /\ phase = "serving"
  /\ Scenario = "uncovered"
  /\ wrote
  /\ ~split
  /\ split' = TRUE
  /\ UNCHANGED <<phase, active, oldCharge, newCharge, prior, next, issued, nextBorrow, oldLearned, oldOnline, fence, done, settled, wrote, sealedPrior, installedThrough>>

Conserves == oldCharge + newCharge <= PipeCapacity
OriginalStillPaid == (prior # 0 /\ ~settled) => oldCharge = 1
ExactNewOwner == next # 0 => nextBorrow = "successor" /\ newCharge = 1
NoReinstall == phase = "serving" => active = "successor" /\ installedThrough = 2
KeepsOrder == next # 0 => next > prior /\ issued = next
Finishes == <> done
WritesAndFallsBack == <> (wrote /\ split)

Next == Prepare \/ OriginalChoice \/ Seal \/ Activate \/ ReofferOriginal \/ LearnOld \/ SettleOld \/ RefundOld \/
        StageCreditLater \/ Open \/ Complete \/ OrdinaryWrite \/ SplitRead
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
