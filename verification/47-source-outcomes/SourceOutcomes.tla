------------------------------ MODULE SourceOutcomes ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Attempts, Width, Policy, Variant, Scenario
VARIABLE s

Keys == 1..Attempts
Participants == 1..3
LiveRows == {key \in Keys : s.rows[key] # "empty"}
Owes(key) == s.applied[key] # Participants
CanReach(key, who) == Scenario # "old_offline" \/ key # 1 \/ who # 1

Init ==
    s = [issued |-> 0, rows |-> [key \in Keys |-> "empty"],
         terminal |-> [key \in Keys |-> "open"],
         applied |-> [key \in Keys |-> {}], acked |-> [key \in Keys |-> {}],
         learner |-> [key \in Keys |-> "empty"], learnedIssued |-> 0,
         phase |-> "open", retired |-> FALSE, sourceDown |-> FALSE,
         queriedClosed |-> {}, compacted |-> {}, inventedResult |-> FALSE,
         cutHiddenAbort |-> FALSE, recoveredOffline |-> FALSE]

Plan ==
    /\ s.phase # "sealed" /\ ~s.retired /\ s.issued < Attempts
    /\ Cardinality(LiveRows) < Width
    /\ \A key \in LiveRows : s.rows[key] # "planned"
    /\ \A key \in LiveRows : s.rows[key] = "seal" => 3 \in s.applied[key]
    /\ s' = [s EXCEPT !.issued = @ + 1, !.rows[s.issued + 1] = "planned"]

Choose(key, result) ==
    /\ s.phase # "sealed" /\ s.rows[key] = "planned"
    /\ result # "seal" \/ Scenario = "general"
    /\ s' = [s EXCEPT !.rows[key] = result, !.terminal[key] = result]

Learn ==
    /\ s.phase = "open" /\ (s.learner # s.rows \/ s.learnedIssued # s.issued)
    /\ s' = [s EXCEPT !.learner = s.rows, !.learnedIssued = s.issued]

SealSourceBook ==
    /\ s.phase = "open"
    /\ s' = [s EXCEPT !.phase = "sealed",
         !.cutHiddenAbort = Scenario = "old_offline" /\ s.learner[1] = "planned" /\ s.rows[1] = "abort"]

LosePredecessor ==
    /\ s.phase # "open" /\ ~s.sourceDown
    /\ s' = [s EXCEPT !.sourceDown = TRUE]

InstallSourceBook ==
    /\ s.phase = "sealed"
    /\ Variant # "lookup_required" \/ \A key \in LiveRows, who \in Participants : CanReach(key, who)
    /\ s' = [s EXCEPT !.phase = "recovered",
         !.recoveredOffline = s.cutHiddenAbort /\ s.sourceDown,
         !.rows = IF Variant = "learned_only" THEN s.learner ELSE @,
         !.issued = IF Variant = "lose_issuance" THEN s.learnedIssued ELSE @]

Apply(key, who) ==
    /\ s.phase # "sealed" /\ CanReach(key, who)
    /\ s.rows[key] \in {"abort", "seal"}
    /\ who \notin s.applied[key]
    /\ s' = [s EXCEPT !.applied[key] = @ \cup {who}]

Acknowledge(key, who, receiptKey) ==
    /\ s.phase # "sealed" /\ s.rows[key] \in {"abort", "seal"}
    /\ who \notin s.acked[key] /\ who \in s.applied[receiptKey]
    /\ key = receiptKey \/ Variant = "foreign_ack"
    /\ s' = [s EXCEPT !.acked[key] = @ \cup {who}]

Compact(key) ==
    /\ s.phase # "sealed" /\ s.rows[key] \in {"abort", "seal"}
    /\ s.acked[key] = Participants \/ Variant = "early_compact"
    /\ Policy # "prefix" \/ \A older \in 1..(key - 1) : s.rows[older] = "empty"
    /\ s' = [s EXCEPT !.rows[key] = "empty", !.acked[key] = {}, !.compacted = @ \cup {key}]

Query(key) ==
    /\ s.phase = "recovered" /\ s.sourceDown
    /\ key <= s.issued /\ s.rows[key] = "empty" /\ key \notin s.queriedClosed
    /\ s' = [s EXCEPT !.queriedClosed = @ \cup {key},
         !.inventedResult = @ \/ (Variant = "absence_is_abort" /\ s.terminal[key] = "seal")]

Retire ==
    /\ s.phase # "sealed" /\ ~s.retired
    /\ \A key \in LiveRows : s.rows[key] # "planned"
    /\ s' = [s EXCEPT !.retired = TRUE]

Next ==
    \/ Plan \/ Learn \/ SealSourceBook \/ InstallSourceBook \/ LosePredecessor \/ Retire
    \/ \E key \in Keys :
        (Choose(key, "abort") \/ Choose(key, "seal") \/ Compact(key) \/ Query(key) \/
         \E who \in Participants :
            Apply(key, who) \/ \E receiptKey \in Keys : Acknowledge(key, who, receiptKey))

Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(InstallSourceBook) /\ \A key \in Keys : WF_s(Compact(key))

PreservesUnsettled == \A key \in Keys :
    s.terminal[key] # "open" /\ Owes(key) => s.rows[key] = s.terminal[key]
IssuedMonotone == \A key \in Keys :
    s.terminal[key] # "open" \/ s.rows[key] # "empty" => key <= s.issued
ExactAck == \A key \in Keys : s.acked[key] \subseteq s.applied[key]
BoundedRows == Cardinality(LiveRows) <= Width
ClosedHasNoDebt == \A key \in 1..s.issued : s.rows[key] = "empty" => ~Owes(key)
NoInventedResult == ~s.inventedResult
CompactedStaysMissing == \A key \in s.compacted : s.rows[key] = "empty"
Installs == (s.phase = "sealed") ~> (s.phase = "recovered")
SettledCreditReturns == \A key \in Keys : (s.acked[key] = Participants) ~> (s.rows[key] = "empty")
NeverCompactsPastAStuckResult ==
    ~(s.issued = Attempts /\ Owes(1) /\ s.rows[1] = "abort" /\ 2 \in s.queriedClosed)
NeverRecoversHiddenResult ==
    ~(s.phase = "recovered" /\ s.recoveredOffline /\ s.retired /\ s.rows[1] = "abort" /\ Owes(1))
=============================================================================
