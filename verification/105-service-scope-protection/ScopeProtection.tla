------------------------- MODULE ScopeProtection -------------------------
EXTENDS FiniteSets

CONSTANTS World, Policy, CanReplicate, InjectLoss, ExactInputs, CanRequalify
VARIABLES copies, owed, physicalLoss, opened, renewed

vars == <<copies, owed, physicalLoss, opened, renewed>>
AZs == {"A", "B", "C"}
Inputs == {"old", "new"}

Init ==
  /\ copies = [input \in Inputs |-> IF input = "old" THEN {"A", "B"} ELSE {"B"}]
  /\ owed = {"old"}
  /\ physicalLoss = IF World = "slow" THEN {} ELSE {"A"}
  /\ opened = FALSE
  /\ renewed = FALSE

(* B and C are the known responding current voters and A is excluded from this service cut. *)
ServingQuorum == ~("B" \in physicalLoss \/ "C" \in physicalLoss)

(* Controlled counterfactual: both worlds expose the same responding quorum and inputs. *)
CredibleLosses == IF World = "diagnosed" /\ ~renewed THEN {"A"} ELSE AZs
DecisionLosses == IF Policy = "timeout-is-failure" THEN {"A"} ELSE CredibleLosses

Residual(placement, input, loss) == placement[input] \ loss
Covers(placement, debt, losses) ==
  \A lost \in losses : \A input \in debt : Residual(placement, input, {lost}) # {}

Open ==
  /\ ~opened
  /\ ServingQuorum
  /\ ExactInputs \/ Policy = "skip-inputs"
  /\ opened' = TRUE
  /\ UNCHANGED <<copies, owed, physicalLoss, renewed>>

Replicate ==
  /\ CanReplicate
  /\ opened
  /\ ServingQuorum
  /\ "C" \notin copies["new"]
  /\ copies' = [copies EXCEPT !["new"] = @ \cup {"C"}]
  /\ UNCHANGED <<owed, physicalLoss, opened, renewed>>

Ack ==
  /\ opened
  /\ ServingQuorum
  /\ "new" \notin owed
  /\ Covers(copies, {"new"}, DecisionLosses) \/ Policy = "skip-ack-coverage"
  /\ owed' = owed \cup {"new"}
  /\ UNCHANGED <<copies, physicalLoss, opened, renewed>>

WithdrawA ==
  LET post == [copies EXCEPT !["old"] = @ \ {"A"}]
  IN /\ opened
     /\ "A" \in copies["old"]
     /\ Covers(post, owed, DecisionLosses) \/ Policy = "withdraw-on-scope"
     /\ copies' = post
     /\ UNCHANGED <<owed, physicalLoss, opened, renewed>>

CopyOldToC ==
  /\ opened
  /\ ServingQuorum
  /\ "C" \notin copies["old"]
  /\ copies' = [copies EXCEPT !["old"] = @ \cup {"C"}]
  /\ UNCHANGED <<owed, physicalLoss, opened, renewed>>

LoseOne ==
  /\ InjectLoss
  /\ opened
  /\ physicalLoss = {}
  /\ \E lost \in AZs : physicalLoss' = {lost}
  /\ UNCHANGED <<copies, owed, opened, renewed>>

(* The renewal case supplies a verified new voter family and keeps no copy from the lost AZ. *)
Renew ==
  LET post == [input \in Inputs |-> Residual(copies, input, physicalLoss)]
  IN /\ CanRequalify
     /\ opened
     /\ ~renewed
     /\ physicalLoss = {"A"}
     /\ Covers(post, owed, AZs) \/ Policy = "renew-on-heartbeats"
     /\ copies' = post
     /\ renewed' = TRUE
     /\ physicalLoss' = {}
     /\ UNCHANGED <<owed, opened>>

Next == Open \/ Replicate \/ Ack \/ WithdrawA \/ CopyOldToC \/ LoseOne \/ Renew
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Open) /\ WF_vars(Replicate) /\ WF_vars(Ack)
OpenedWithExactInputs == opened => ExactInputs
PromisesIntact == Covers(copies, owed, CredibleLosses)
SurvivesActualLoss == \A input \in owed : Residual(copies, input, physicalLoss) # {}
RenewalHasFullCoverage == renewed => Covers(copies, owed, AZs)
EventuallyOpen == <>opened
EventuallyAck == <>("new" \in owed)
NeverAcksWithIndependentCopy == ~("new" \in owed /\ "C" \in copies["new"])
PriorCopyNeverReplacedBeforeLoss ==
  ~(copies["old"] = {"B", "C"} /\ physicalLoss = {"B"})
NeverLoseAgainAfterQualifiedRenewal ==
  ~(renewed /\ physicalLoss = {"B"} /\ "new" \in owed)
=============================================================================
