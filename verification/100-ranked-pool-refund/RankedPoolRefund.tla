--------------------------- MODULE RankedPoolRefund ------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Scenario, Failed, Variant

Voters == 1..3
Available == Voters \ {Failed}
Majority(voters) == Cardinality(voters) >= 2
NoCut == 5

OldChoice ==
  CASE Scenario = "spent" -> 2
    [] Scenario = "refund" -> 1
    [] OTHER -> 0

Accepted(v) ==
  CASE Scenario = "spent" -> IF v = 3 THEN 1 ELSE 2
    [] Scenario = "refund" -> IF v = 3 THEN 0 ELSE 1
    [] Scenario = "minority" -> IF v = 1 THEN 1 ELSE 0
    [] OTHER -> 0

RawStaged == IF Scenario = "staged" THEN 1 ELSE 0

VARIABLES reports, captured, stable, visible, votes, active, replied, debit, effected
vars == <<reports, captured, stable, visible, votes, active, replied, debit, effected>>

Init ==
  /\ reports = {}
  /\ captured = NoCut
  /\ stable = [v \in Voters |-> NoCut]
  /\ visible = [v \in Voters |-> NoCut]
  /\ votes = {}
  /\ active = FALSE
  /\ replied = FALSE
  /\ debit = "pending"
  /\ effected = FALSE

Ranked ==
  IF 2 \in {Accepted(v) : v \in reports} THEN 2
  ELSE IF 1 \in {Accepted(v) : v \in reports} THEN 1 ELSE 0

Report(v) ==
  /\ v \in Available \ reports
  /\ reports' = reports \cup {v}
  /\ UNCHANGED <<captured, stable, visible, votes, active, replied, debit, effected>>

FreezeCut ==
  /\ captured = NoCut
  /\ Majority(reports)
  /\ captured' = IF Variant = "learned-only" THEN 0
                  ELSE IF Variant = "adopt-staging" THEN RawStaged
                  ELSE IF Variant = "refund-only" /\ Ranked = 2 THEN 1 ELSE Ranked
  /\ UNCHANGED <<reports, stable, visible, votes, active, replied, debit, effected>>

Rival == captured + 6
Size(body) == IF body >= 6 THEN body - 6 ELSE body
Exact(v) == stable[v] = captured /\ visible[v] = captured

Stage(v, first, second) ==
  /\ captured # NoCut
  /\ v \in Available \ votes
  /\ ~Exact(v)
  /\ stable' = [stable EXCEPT ![v] = first]
  /\ visible' = [visible EXCEPT ![v] = second]
  /\ UNCHANGED <<reports, captured, votes, active, replied, debit, effected>>

CanVote(v) ==
  CASE Variant = "count-visible-only" -> visible[v] = captured
    [] Variant = "compare-length-only" -> Size(stable[v]) = captured /\ Size(visible[v]) = captured
    [] OTHER -> Exact(v)

Vote(v) ==
  /\ v \in Available \ votes
  /\ captured # NoCut
  /\ CanVote(v)
  /\ votes' = votes \cup {v}
  /\ UNCHANGED <<reports, captured, stable, visible, active, replied, debit, effected>>

Install ==
  /\ ~active
  /\ Majority(votes)
  /\ active' = TRUE
  /\ UNCHANGED <<reports, captured, stable, visible, votes, replied, debit, effected>>

RefundReply ==
  /\ active
  /\ captured >= 1
  /\ ~replied
  /\ replied' = TRUE
  /\ UNCHANGED <<reports, captured, stable, visible, votes, active, debit, effected>>

DecideDebit ==
  /\ active
  /\ debit = "pending"
  /\ debit' = IF captured = 1 \/ (Variant = "receipt-is-credit" /\ replied)
              THEN "granted" ELSE "refused"
  /\ UNCHANGED <<reports, captured, stable, visible, votes, active, replied, effected>>

Materialize ==
  /\ ~effected
  /\ (debit = "granted" \/ (Variant = "stage-is-credit" /\ captured = 1 /\
      \E v \in Available : visible[v] = captured))
  /\ effected' = TRUE
  /\ UNCHANGED <<reports, captured, stable, visible, votes, active, replied, debit>>

Next ==
  \/ \E v \in Available : Report(v) \/ Vote(v) \/
       (\E first, second \in {captured, Rival, NoCut} : Stage(v, first, second))
  \/ FreezeCut \/ Install \/ RefundReply \/ DecideDebit \/ Materialize

Spec == Init /\ [][Next]_vars
Fair ==
  /\ Spec
  /\ \A v \in Available : WF_vars(Report(v)) /\ WF_vars(Vote(v)) /\ WF_vars(Stage(v, captured, captured))
  /\ WF_vars(FreezeCut) /\ WF_vars(Install) /\ WF_vars(RefundReply) /\ WF_vars(DecideDebit) /\ WF_vars(Materialize)

ExactVotes == \A v \in votes : Exact(v)
Inherited == active => OldChoice <= captured
NoDoubleSpend == ~(OldChoice = 2 /\ effected)
EffectUsesChosenDebit == effected => debit = "granted"
StagingIsNotAChoice == Scenario = "staged" => ~replied
Outcome ==
  <>IF Scenario = "spent" THEN active /\ replied /\ debit = "refused"
    ELSE IF Scenario = "staged" THEN active /\ debit = "refused" /\ ~replied
    ELSE active /\ replied /\ debit = "granted" /\ effected

=============================================================================
