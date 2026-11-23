--------------------------- MODULE SettlementRedo ---------------------------
EXTENDS Naturals

CONSTANTS Rounds, Workspace, Candidate, Variant, SyncAvailable

RefundBytes == 1
ImageBytes == 2
Redo == Candidate = "redo"

VARIABLES allocation, absent, reported, stable, visible, alternate, frame, bytes, named, crashes
vars == <<allocation, absent, reported, stable, visible, alternate, frame, bytes, named, crashes>>

Usage == (IF frame = 0 THEN 0 ELSE RefundBytes) + (IF alternate = 0 THEN 0 ELSE ImageBytes)

Init ==
  /\ allocation = 1
  /\ absent = 0
  /\ reported = 0
  /\ stable = 0
  /\ visible = 0
  /\ alternate = 0
  /\ frame = 0
  /\ bytes = FALSE
  /\ named = FALSE
  /\ crashes = [count |-> 0, unnamed |-> FALSE, predecessor |-> FALSE]

ObserveAbsence ==
  /\ absent < allocation
  /\ absent' = allocation
  /\ UNCHANGED <<allocation, reported, stable, visible, alternate, frame, bytes, named, crashes>>

StageFrame ==
  /\ Redo
  /\ frame = 0
  /\ reported < allocation
  /\ absent = allocation
  /\ Usage + RefundBytes <= Workspace
  /\ frame' = allocation
  /\ bytes' = FALSE
  /\ named' = FALSE
  /\ UNCHANGED <<allocation, absent, reported, stable, visible, alternate, crashes>>

SyncBytes ==
  /\ frame # 0
  /\ ~bytes
  /\ bytes' = TRUE
  /\ UNCHANGED <<allocation, absent, reported, stable, visible, alternate, frame, named, crashes>>

SyncName ==
  /\ bytes
  /\ ~named
  /\ named' = TRUE
  /\ UNCHANGED <<allocation, absent, reported, stable, visible, alternate, frame, bytes, crashes>>

Recover(cut) == IF bytes /\ named /\ frame = cut + 1 THEN frame ELSE cut

CanReport ==
  CASE Variant = "visible-is-durable" -> visible >= allocation
    [] Variant = "bytes-without-name" -> frame = allocation /\ bytes
    [] OTHER -> Recover(stable) >= allocation /\ Recover(visible) >= allocation

Report ==
  /\ reported < allocation
  /\ CanReport
  /\ reported' = allocation
  /\ UNCHANGED <<allocation, absent, stable, visible, alternate, frame, bytes, named, crashes>>

Spend ==
  /\ reported = allocation
  /\ allocation < Rounds
  /\ allocation' = allocation + 1
  /\ UNCHANGED <<absent, reported, stable, visible, alternate, frame, bytes, named, crashes>>

StageBase ==
  /\ alternate = 0
  /\ stable = visible
  /\ Usage + ImageBytes <= Workspace
  /\ (IF Redo THEN reported ELSE absent) > stable
  /\ alternate' = IF Redo THEN reported ELSE absent
  /\ UNCHANGED <<allocation, absent, reported, stable, visible, frame, bytes, named, crashes>>

Publish ==
  /\ stable = visible
  /\ alternate > visible
  /\ visible' = alternate
  /\ UNCHANGED <<allocation, absent, reported, stable, alternate, frame, bytes, named, crashes>>

SyncSelector ==
  /\ SyncAvailable
  /\ stable < visible
  /\ stable' = visible
  /\ UNCHANGED <<allocation, absent, reported, visible, alternate, frame, bytes, named, crashes>>

RetireAlternate ==
  /\ alternate # 0
  /\ stable >= alternate
  /\ alternate' = 0
  /\ UNCHANGED <<allocation, absent, reported, stable, visible, frame, bytes, named, crashes>>

ReclaimFrame ==
  /\ frame # 0
  /\ IF Variant = "reclaim-by-visible" THEN visible >= frame
     ELSE stable >= frame /\ visible >= frame
  /\ frame' = 0
  /\ bytes' = FALSE
  /\ named' = FALSE
  /\ UNCHANGED <<allocation, absent, reported, stable, visible, alternate, crashes>>

Crash(cut) ==
  /\ cut \in {stable, visible}
  /\ crashes.count < 2
  /\ crashes' = [count |-> crashes.count + 1,
                 unnamed |-> crashes.unnamed \/ (bytes /\ ~named),
                 predecessor |-> crashes.predecessor \/
                   (stable < visible /\ cut = stable /\ frame = reported /\ bytes /\ named /\
                    allocation = reported + 1)]
  /\ stable' = cut
  /\ visible' = cut
  /\ bytes' = (bytes /\ named)
  /\ UNCHANGED <<allocation, absent, reported, alternate, frame, named>>

Next ==
  \/ ObserveAbsence \/ StageFrame \/ SyncBytes \/ SyncName \/ Report \/ Spend
  \/ StageBase \/ Publish \/ SyncSelector \/ RetireAlternate \/ ReclaimFrame
  \/ \E cut \in {stable, visible} : Crash(cut)

Spec == Init /\ [][Next]_vars

Fair ==
  /\ Spec
  /\ WF_vars(ObserveAbsence) /\ WF_vars(StageFrame) /\ WF_vars(SyncBytes) /\ WF_vars(SyncName)
  /\ WF_vars(Report) /\ WF_vars(Spend)
  /\ WF_vars(StageBase) /\ WF_vars(Publish) /\ WF_vars(SyncSelector)
  /\ WF_vars(RetireAlternate) /\ WF_vars(ReclaimFrame)

Fits == Usage <= Workspace
VerifiedAbsence == reported <= absent
RecoveredRefunds == \A cut \in {stable, visible} : reported <= Recover(cut)
RecoveredCapacity == \A cut \in {stable, visible} : allocation <= Recover(cut) + 1

FirstRefund == <>(reported >= 1)
EventuallyCycles == <>(reported = Rounds /\ frame = 0 /\ alternate = 0)
NoEarlySpendWithPredecessor ==
  ~(allocation = 2 /\ stable = 0 /\ visible = 1 /\ frame = 1 /\ bytes /\ named)
NoTwoCrashRepeatedReuse ==
  ~(crashes.count = 2 /\ crashes.unnamed /\ crashes.predecessor /\
    allocation = 3 /\ reported = 3 /\ stable = 3 /\ frame = 0 /\ alternate = 0)

=============================================================================
