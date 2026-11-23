-------------------------- MODULE IntentRetirement --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Intents, CopyLimit, ReceiptLimit, Policy, Variant, Scenario
VARIABLE s

Handles == 1..Intents
SealValue(id) == 2 + (id % 2)
Installed(id) == s.chosen[id] # 0
Aborted(id) == s.source[id] = 1
Sealed(id) == s.source[id] > 1
SourceCanReply == Scenario # "result_link_down"
ProviderReachable == Scenario # "provider_disconnected"

Init ==
    s = [issued |-> 0, active |-> 0, family |-> 1, retired |-> {},
         source |-> [id \in Handles |-> 0], chosen |-> [id \in Handles |-> 0],
         receipt |-> [id \in Handles |-> 0], seen |-> [id \in Handles |-> 0],
         sent |-> {}, serving |-> {}, credits |-> {}, lostReplies |-> {},
         movedBeforeReplace |-> {}, recoveredAfterMove |-> {},
         plans |-> {}, queued |-> {}, medium |-> [id \in Handles |-> "empty"], lateRefused |-> {}]

Mint ==
    /\ s.active = 0 /\ s.issued < Intents
    /\ Variant = "late_credit" \/ Cardinality(s.credits) < ReceiptLimit
    /\ s' = [s EXCEPT !.issued = @ + 1, !.active = s.issued + 1,
                       !.credits = IF Variant = "late_credit" THEN @ ELSE @ \cup {s.issued + 1}]

Seal(id) ==
    /\ s.active = id /\ s.source[id] = 0
    /\ s' = [s EXCEPT !.source[id] = SealValue(id)]

Abort(id) ==
    /\ s.active = id /\ s.source[id] = 0
    /\ s' = [s EXCEPT !.source[id] = 1]

Plan(id) ==
    /\ s.active = id /\ id \notin s.plans /\ ~Aborted(id) /\ ~Installed(id)
    /\ s.medium[id] = "empty" /\ Cardinality(s.plans) < CopyLimit
    /\ s' = [s EXCEPT !.plans = @ \cup {id}, !.queued = @ \cup {id}]

Deliver(id) ==
    /\ id \in s.queued /\ ProviderReachable
    /\ s' = [s EXCEPT !.queued = @ \ {id},
                      !.lateRefused = IF s.medium[id] = "fenced" /\ s.active > id THEN @ \cup {id} ELSE @,
                      !.medium[id] = IF @ = "fenced" THEN @ ELSE "held"]

Install(id) ==
    /\ s.active # 0 /\ (s.active = id \/ Variant = "install_by_route")
    /\ Sealed(id) /\ ~Installed(s.active) /\ s.medium[id] = "held"
    /\ s.active \in s.credits \/ (Variant = "late_credit" /\ Cardinality(s.credits) < ReceiptLimit)
    /\ s' = [s EXCEPT !.chosen[s.active] = s.source[id], !.receipt[s.active] = s.source[id],
                       !.credits = @ \cup {s.active}, !.serving = @ \cup {s.active}]

MoveOn(id) ==
    /\ id \in s.serving
    /\ s' = [s EXCEPT !.serving = @ \ {id},
                      !.receipt[id] = IF Variant = "drop_on_move" THEN 0 ELSE @]

Retire(id) ==
    /\ s.active = id \/ (Variant = "retire_by_route" /\ id \in s.retired /\ s.active # 0)
    /\ Aborted(id) \/ Installed(id) \/ Variant = "guess_terminal"
    /\ Policy # "drain_first" \/ ((id \notin s.plans \/ id \in s.serving) /\ s.receipt[id] = 0)
    /\ s' = [s EXCEPT !.active = 0, !.retired = @ \cup {s.active},
           !.credits = IF Aborted(id) THEN @ \ {id} ELSE @,
           !.receipt[id] = IF Variant = "drop_on_retire" THEN 0 ELSE @,
           !.plans = IF Variant = "forget_cleanup" THEN @ \ {id} ELSE @]

Clean(id) ==
    /\ id \in s.plans /\ ProviderReachable
    /\ Aborted(id) \/ (Installed(id) /\ id \notin s.serving)
    /\ Variant # "needs_gate" \/ s.active = id
    /\ s' = [s EXCEPT !.plans = @ \ {id},
           !.medium[id] = IF Variant = "no_missing_fence" /\ @ = "empty" THEN @ ELSE "fenced"]

Send(id) ==
    /\ s.receipt[id] # 0 /\ id \notin s.sent
    /\ s' = [s EXCEPT !.sent = @ \cup {id}]

DropReply(id) ==
    /\ id \in s.sent /\ s.seen[id] = 0
    /\ s' = [s EXCEPT !.sent = @ \ {id}, !.lostReplies = @ \cup {id}]

RecordAtSource(id) ==
    /\ SourceCanReply /\ id \in s.sent /\ s.receipt[id] # 0 /\ s.seen[id] = 0
    /\ s' = [s EXCEPT !.seen[id] = s.receipt[id],
                       !.recoveredAfterMove =
                         IF id \in s.retired /\ id \in s.movedBeforeReplace /\ id \in s.lostReplies
                         THEN @ \cup {id} ELSE @]

Ack(id) ==
    /\ s.receipt[id] # 0
    /\ s.seen[id] = s.receipt[id] \/ (Variant = "send_is_ack" /\ id \in s.sent)
    /\ s' = [s EXCEPT !.credits = @ \ {id}, !.receipt[id] = 0]

Replace ==
    /\ s.family = 1
    /\ s' = [s EXCEPT !.family = 2, !.issued = IF Variant = "forget_issued" THEN 0 ELSE @,
         !.movedBeforeReplace = {id \in Handles : Installed(id) /\ id \notin s.serving},
         !.receipt = IF Variant = "forget_receipts" THEN [id \in Handles |-> 0] ELSE @]

RetireSome == \E id \in Handles : Retire(id)
CleanSome == \E id \in Handles : Clean(id)
InstallSome == \E id \in Handles : Install(id)
Next ==
    \/ Mint \/ Replace \/ RetireSome \/ CleanSome \/ InstallSome
    \/ \E id \in Handles : Seal(id) \/ Abort(id) \/ Plan(id) \/ Deliver(id) \/ MoveOn(id) \/
         Send(id) \/ DropReply(id) \/ RecordAtSource(id) \/ Ack(id)

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(RetireSome) /\ WF_s(CleanSome) /\ WF_s(InstallSome)

OldHandleStaysClosed == s.active \notin s.retired
RetirementHasExactDisposition == \A id \in s.retired : Aborted(id) \/ Installed(id)
ExactInstall == \A id \in Handles : Installed(id) => s.chosen[id] = s.source[id] /\ Sealed(id)
KeepsUnrecordedOutcome ==
    \A id \in Handles : Installed(id) /\ s.seen[id] # s.chosen[id] => s.receipt[id] = s.chosen[id]
TracksPossiblePhysicalCopies ==
    \A id \in Handles :
       (s.medium[id] = "held" \/ (id \in s.queued /\ s.medium[id] # "fenced")) => id \in s.plans
HeldCopyIsTracked == \A id \in Handles : s.medium[id] = "held" => id \in s.plans
ServingKeepsCopy == \A id \in s.serving : s.medium[id] = "held"
BoundedDebt == Cardinality(s.plans) <= CopyLimit /\ Cardinality(s.credits) <= ReceiptLimit
CreditPrecedesSeal ==
    \A id \in Handles : s.active = id /\ Sealed(id) /\ ~Installed(id) => id \in s.credits

RetiresWithEvidence ==
    \A id \in Handles : (s.active = id /\ (Aborted(id) \/ Installed(id))) ~> (id \in s.retired)
SettlesRetiredAbortedCopy ==
    \A id \in Handles : (id \in s.retired /\ Aborted(id) /\ id \in s.plans) ~> (id \notin s.plans)
ReadyInstalls ==
    \A id \in Handles : (s.active = id /\ Sealed(id) /\ s.medium[id] = "held") ~> Installed(id)

NeverReusesGateWithOldCleanup ==
    ~(s.active = 2 /\ 1 \in s.retired /\ 1 \in s.plans)
NeverReconcilesAfterMovingAndReplacing ==
    ~(s.active = 2 /\ 1 \in s.recoveredAfterMove /\ s.receipt[1] = 0)
NeverFencesBeforeDelayedCopy ==
    ~(1 \in s.lateRefused /\ 1 \in s.retired /\ Aborted(1))

=============================================================================
