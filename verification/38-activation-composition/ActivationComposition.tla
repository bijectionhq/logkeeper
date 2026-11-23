--------------------------- MODULE ActivationComposition ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Owners, Variant
VARIABLE s

Revisions == 1..Owners
Result == 11
CopyKey == 21

Init ==
    s = [owner |-> 1, locator |-> 1, cached |-> 1, stopped |-> {}, phase |-> "open",
         target |-> [issued |-> 1, live |-> 0, outcome |-> Result, job |-> CopyKey],
         stage |-> [issued |-> 0, live |-> 0, outcome |-> 0, job |-> 0],
         source |-> 0, provider |-> 0, reply |-> 0, hadResult |-> FALSE, hadFence |-> FALSE,
         oldSource |-> 0, oldProvider |-> 0, acked |-> FALSE, settled |-> FALSE,
         recordedStaged |-> FALSE, fencedStaged |-> FALSE, staleRetried |-> FALSE, duplicate |-> FALSE,
         wrongAuthority |-> FALSE]

Send ==
    /\ s.target.outcome # 0 /\ s.reply = 0
    /\ s' = [s EXCEPT !.reply = s.target.outcome,
                     !.target.outcome = IF Variant = "send_discharges" THEN 0 ELSE @]

Record ==
    /\ s.reply # 0 /\ s.source = 0
    /\ s' = [s EXCEPT !.source = s.reply, !.hadResult = TRUE,
                     !.recordedStaged = s.phase = "staged"]

DuplicateRecord ==
    /\ s.reply # 0 /\ s.source = s.reply /\ s.acked /\ ~s.duplicate
    /\ s' = [s EXCEPT !.duplicate = TRUE,
                     !.target.outcome = IF Variant = "duplicate_reopens" THEN s.reply ELSE @]

Fence ==
    /\ s.target.job # 0 /\ s.provider = 0
    /\ s' = [s EXCEPT !.provider = s.target.job, !.hadFence = TRUE,
                     !.fencedStaged = s.phase = "staged"]

Seal ==
    /\ s.phase = "open" /\ s.owner < Owners /\ s.locator = s.owner
    /\ s' = [s EXCEPT !.phase = "sealed"]

Stage ==
    /\ s.phase = "sealed"
    /\ s' = [s EXCEPT !.phase = "staged", !.stage = s.target,
                     !.oldSource = s.source, !.oldProvider = s.provider]

Install ==
    /\ s.phase = "staged"
    /\ s' = [s EXCEPT !.phase = "open", !.owner = @ + 1,
         !.target = IF Variant = "reset_issuance" THEN [s.stage EXCEPT !.issued = 0] ELSE s.stage,
         !.source = IF Variant = "restore_source" THEN s.oldSource ELSE @,
         !.provider = IF Variant = "restore_provider" THEN s.oldProvider ELSE @]

Publish ==
    /\ s.locator < s.owner
    /\ s' = [s EXCEPT !.locator = s.owner]

Stop(revision) ==
    /\ revision < s.locator /\ revision \notin s.stopped
    /\ s' = [s EXCEPT !.stopped = @ \cup {revision}]

Refresh ==
    /\ s.cached < s.locator
    /\ Variant # "suppress_refresh_after_stale" \/ ~s.staleRetried
    /\ s' = [s EXCEPT !.cached = s.locator]

RetryStale ==
    /\ s.source # 0 /\ s.cached \in s.stopped /\ ~s.staleRetried
    /\ s' = [s EXCEPT !.staleRetried = TRUE]

Ack ==
    /\ s.phase = "open" \/ Variant = "ack_while_sealed"
    /\ s.cached = s.owner \/ Variant = "apply_at_stale_revision"
    /\ s.source = s.target.outcome /\ s.target.outcome # 0
    /\ s' = [s EXCEPT !.target.outcome = 0, !.acked = TRUE,
                     !.wrongAuthority = @ \/ s.cached # s.owner]

Settle ==
    /\ s.phase = "open" \/ Variant = "settle_while_sealed"
    /\ s.cached = s.owner
    /\ s.provider = s.target.job /\ s.target.job # 0
    /\ s' = [s EXCEPT !.target.job = 0, !.settled = TRUE]

Mint ==
    /\ s.phase = "open" /\ s.target.live = 0 /\ s.target.issued < 2
    /\ s' = [s EXCEPT !.target.issued = @ + 1, !.target.live = s.target.issued + 1]

StopSome == \E revision \in Revisions : Stop(revision)
Next ==
    \/ Send \/ Record \/ DuplicateRecord \/ Fence \/ Seal \/ Stage \/ Install \/ Publish \/ StopSome
    \/ Refresh \/ RetryStale \/ Ack \/ Settle \/ Mint

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(Stage) /\ WF_s(Install) /\ WF_s(Publish) /\ WF_s(StopSome)
             /\ WF_s(Refresh) /\ WF_s(Ack) /\ WF_s(Settle)

ResultProtected == s.source = Result \/ s.target.outcome = Result
SourceRecordIsDurable == s.hadResult => s.source = Result
ProviderFenceIsDurable == s.hadFence => s.provider = CopyKey
CompletedTargetWritesSurvive == (s.acked => s.target.outcome = 0) /\ (s.settled => s.target.job = 0)
UnsettledCopyKeepsOriginalKey == ~s.settled => s.target.job = CopyKey
RetiredAdmissionStaysClosed == s.target.live # 1
IssuedFenceSurvives == s.target.issued >= 1
OnlyCurrentRevisionWrites == ~s.wrongAuthority
SafeDiscovery == s.locator <= s.owner /\ \A revision \in s.stopped : revision < s.locator

StagedCutInstalls ==
    \A revision \in Revisions : (s.owner = revision /\ s.phase = "staged") ~> (s.owner > revision)
ExternalFactsAreApplied ==
    (s.source = Result /\ s.provider = CopyKey) ~> (s.acked /\ s.settled)

NeverReconcilesStagedExternalFacts ==
    ~(s.acked /\ s.settled /\ s.recordedStaged /\ s.fencedStaged /\ s.staleRetried /\ s.duplicate /\
      s.stopped = 1..(Owners - 1))
=============================================================================
