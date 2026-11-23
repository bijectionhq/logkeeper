------------------------------ MODULE CrashMedia ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS MaxRecords, Variant
VARIABLE s

Init ==
    s = [history |-> <<>>, synced |-> 0, named |-> FALSE,
         ack |-> 0, committed |-> 0,
         cut |-> 0, image |-> <<>>, baseSynced |-> FALSE,
         renamed |-> FALSE, selectorSynced |-> FALSE, oldRemoved |-> FALSE,
         newOnly |-> {}, ackAtPublish |-> 0,
         crashed |-> FALSE, usedNew |-> FALSE, readable |-> FALSE,
         frames |-> {}, recovered |-> <<>>, visible |-> 0]

Write(value) ==
    /\ Len(s.history) < MaxRecords
    /\ s' = [s EXCEPT !.history = Append(@, value),
          !.newOnly = IF Variant = "redirect_before_selector"
                          /\ s.renamed /\ ~s.selectorSynced
                      THEN @ \cup {Len(s.history) + 1} ELSE @]

SyncBytes ==
    /\ s.synced < Len(s.history)
    /\ s' = [s EXCEPT !.synced = Len(s.history)]

SyncName ==
    /\ ~s.named
    /\ s' = [s EXCEPT !.named = TRUE]

Acknowledge ==
    /\ s.ack < Len(s.history)
    /\ s.synced = Len(s.history) \/ Variant = "ack_before_bytes"
    /\ s.named \/ Variant = "ack_before_name"
    /\ s' = [s EXCEPT !.ack = Len(s.history)]

CertifyCommit ==
    /\ s.committed < s.ack
    /\ s' = [s EXCEPT !.committed = s.ack]

Capture ==
    /\ s.cut = 0 /\ s.ack > 0
    /\ s' = [s EXCEPT !.cut = s.ack]

WriteBase ==
    /\ s.cut > 0 /\ s.image = <<>>
    /\ s' = [s EXCEPT !.image = SubSeq(s.history, 1, s.cut)]

SyncBase ==
    /\ Len(s.image) = s.cut /\ s.cut > 0 /\ ~s.baseSynced
    /\ s' = [s EXCEPT !.baseSynced = TRUE]

Publish ==
    /\ s.cut > 0 /\ ~s.renamed
    /\ s.baseSynced \/ Variant = "publish_incomplete_base"
    /\ Variant # "head_match" \/ s.ack = s.cut
    /\ s' = [s EXCEPT !.renamed = TRUE, !.ackAtPublish = s.ack]

SyncSelector ==
    /\ s.renamed /\ ~s.selectorSynced
    /\ s' = [s EXCEPT !.selectorSynced = TRUE]

ReclaimOld ==
    /\ s.renamed /\ ~s.oldRemoved
    /\ s.selectorSynced \/ Variant = "unlink_before_selector_sync"
    /\ s' = [s EXCEPT !.oldRemoved = TRUE]

LastDecodable(start, frames) ==
    LET candidates == { last \in start..Len(s.history) :
        IF Variant = "skip_gap"
        THEN last = start \/ last \in frames
        ELSE (start + 1)..last \subseteq frames }
    IN CHOOSE last \in candidates : \A other \in candidates : other <= last

Crash(kept, nameSurvives, useNew, imageSurvives) ==
    LET start == IF useNew THEN s.cut ELSE 0
        frames == IF ~nameSurvives \/ (useNew /\ Variant = "omit_intervening_tail")
                  THEN {}
                  ELSE IF useNew THEN kept ELSE kept \ s.newOnly
        canRead == IF useNew
                   THEN imageSurvives /\ s.image = SubSeq(s.history, 1, start)
                   ELSE ~s.oldRemoved
        last == IF canRead THEN LastDecodable(start, frames) ELSE 0
        positions == SelectSeq([i \in 1..(last - start) |-> start + i],
                               LAMBDA i : i \in frames)
        decoded == IF ~canRead THEN <<>>
                   ELSE (IF useNew THEN s.image ELSE <<>>)
                        \o [i \in 1..Len(positions) |-> s.history[positions[i]]]
    IN /\ 1..s.synced \subseteq kept
       /\ s.named => nameSurvives
       /\ useNew => s.renamed
       /\ s.selectorSynced => useNew
       /\ s.baseSynced => imageSurvives
       /\ s' = [s EXCEPT !.crashed = TRUE, !.usedNew = useNew,
                !.readable = canRead, !.frames = frames, !.recovered = decoded,
                !.visible = IF Variant = "intact_means_committed" \/ last <= s.committed
                            THEN last ELSE s.committed]

Next ==
    /\ ~s.crashed
    /\ \/ \E value \in {1, 2} : Write(value)
       \/ SyncBytes \/ SyncName \/ Acknowledge \/ CertifyCommit
       \/ Capture \/ WriteBase \/ SyncBase \/ Publish \/ SyncSelector \/ ReclaimOld
       \/ \E kept \in SUBSET (1..Len(s.history)), nameSurvives \in BOOLEAN,
             useNew \in BOOLEAN, imageSurvives \in BOOLEAN :
             Crash(kept, nameSurvives, useNew, imageSurvives)

Spec == Init /\ [][Next]_s

AcknowledgedPrefixSurvives ==
    s.crashed /\ s.ack > 0 =>
        /\ s.readable
        /\ s.ack <= Len(s.recovered)
        /\ SubSeq(s.recovered, 1, s.ack) = SubSeq(s.history, 1, s.ack)

RecoveryNeverSkipsMissingFrame ==
    s.crashed /\ s.readable =>
        /\ SubSeq(s.history, 1, Len(s.recovered)) = s.recovered
        /\ ((IF s.usedNew THEN s.cut ELSE 0) + 1)..Len(s.recovered)
             \subseteq s.frames

VisibilityRequiresCommitEvidence ==
    s.crashed => s.visible = s.committed

NeverPublishesAfterAdvance == s.ackAtPublish <= s.cut

NeverRecoversVolatilePublishOnOld ==
    ~(s.crashed /\ s.renamed /\ ~s.selectorSynced /\ ~s.usedNew /\
        s.cut < s.ackAtPublish /\ s.ackAtPublish < s.ack /\ Len(s.recovered) >= s.ack)

NeverReclaimsAndRecoversExactSuffix ==
    ~(s.crashed /\ s.usedNew /\ s.oldRemoved /\
        s.cut < s.ackAtPublish /\ s.ackAtPublish < s.ack /\ Len(s.recovered) >= s.ack)

NeverKeepsUncertifiedBytes ==
    ~(s.crashed /\ s.ack = 0 /\ Len(s.recovered) > 0 /\ s.visible = 0)
=============================================================================
