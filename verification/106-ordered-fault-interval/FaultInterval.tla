------------------------------- MODULE FaultInterval -------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Scenario, Policy
VARIABLES journal, stable, visible, local, running, crashed, voters, custody, cert, usedCert

vars == <<journal, stable, visible, local, running, crashed, voters, custody, cert, usedCert>>
At(prefix, event) == {p \in 1..prefix : journal[p] = event}
Has(event) == At(Len(journal), event) # {}
StartAt(prefix) == IF At(prefix, "renew") = {} THEN 0 ELSE CHOOSE p \in At(prefix, "renew") : TRUE
IntervalAt(prefix) ==
  [start |-> StartAt(prefix),
   loss |-> \E p \in At(prefix, "confirm-A") : p > StartAt(prefix)]
Current == IntervalAt(Len(journal))
Basis == <<Len(journal), voters, custody, Current.start>>
FullData == ~Has("B-only-ack") \/ Has("repair")
FromRenewal == Scenario \in {"recover-renewal", "late-confirmation"}

Init ==
  /\ journal = IF FromRenewal THEN <<"confirm-A", "renew">> ELSE <<"confirm-A">>
  /\ stable = IF Scenario \in {"recover-confirmation", "recover-renewal", "new-majority"}
                 THEN Len(journal) - 1 ELSE Len(journal)
  /\ visible = Len(journal)
  /\ local = Current
  /\ running = TRUE
  /\ crashed = FALSE
  /\ voters = 1
  /\ custody = 1
  /\ cert = <<>>
  /\ usedCert = <<>>

Crash ==
  /\ Scenario \in {"recover-confirmation", "recover-renewal", "new-majority"}
  /\ running
  /\ ~crashed
  /\ \E root \in {stable, visible} : /\ stable' = root
                                      /\ visible' = root
  /\ running' = FALSE
  /\ crashed' = TRUE
  /\ UNCHANGED <<journal, local, voters, custody, cert, usedCert>>

Open ==
  /\ ~running
  /\ Policy # "requires-live-detector"
  /\ local' = IF Policy = "checkpoint-only" THEN IntervalAt(visible) ELSE Current
  /\ running' = TRUE
  /\ UNCHANGED <<journal, stable, visible, crashed, voters, custody, cert, usedCert>>

ReplaceVoters ==
  /\ Scenario \in {"new-majority", "renewal-race"}
  /\ running
  /\ voters = 1
  /\ voters' = 2
  /\ local' = IF Policy = "reset-on-voters" THEN [local EXCEPT !.loss = FALSE] ELSE local
  /\ UNCHANGED <<journal, stable, visible, running, crashed, custody, cert, usedCert>>

ChangeCustody ==
  /\ Scenario = "renewal-race"
  /\ running
  /\ custody = 1
  /\ custody' = 2
  /\ UNCHANGED <<journal, stable, visible, local, running, crashed, voters, cert, usedCert>>

DeliverLateConfirmation ==
  /\ Scenario = "late-confirmation"
  /\ running
  /\ ~local.loss
  /\ Current.start = 0 \/ Policy = "ignore-interval"
  /\ journal' = Append(journal, "confirm-A")
  /\ local' = [local EXCEPT !.loss = TRUE]
  /\ UNCHANGED <<stable, visible, running, crashed, voters, custody, cert, usedCert>>

AckOnB ==
  /\ running
  /\ local.loss
  /\ CASE Scenario = "new-majority" -> crashed /\ voters = 2
       [] Scenario \in {"recover-confirmation", "recover-renewal"} -> crashed
       [] OTHER -> TRUE
  /\ ~Has("B-only-ack")
  /\ journal' = Append(journal, "B-only-ack")
  /\ UNCHANGED <<stable, visible, local, running, crashed, voters, custody, cert, usedCert>>

Repair ==
  /\ Scenario = "renewal-race"
  /\ running
  /\ ~FullData
  /\ journal' = Append(journal, "repair")
  /\ UNCHANGED <<stable, visible, local, running, crashed, voters, custody, cert, usedCert>>

Certify ==
  /\ Scenario = "renewal-race"
  /\ running
  /\ local.loss
  /\ FullData
  /\ cert # Basis
  /\ cert' = Basis
  /\ UNCHANGED <<journal, stable, visible, local, running, crashed, voters, custody, usedCert>>

MatchesCert ==
  /\ Len(cert) = 4
  /\ cert[1] = Basis[1] \/ Policy = "ignore-frontier"
  /\ cert[2] = Basis[2] \/ Policy = "ignore-voters"
  /\ cert[3] = Basis[3] \/ Policy = "ignore-custody"
  /\ cert[4] = Basis[4]

Renew ==
  /\ running
  /\ local.loss
  /\ Current.start = 0
  /\ MatchesCert
  /\ usedCert' = <<cert, Basis, FullData>>
  /\ journal' = Append(journal, "renew")
  /\ local' = [start |-> Len(journal) + 1, loss |-> FALSE]
  /\ UNCHANGED <<stable, visible, running, crashed, voters, custody, cert>>

Next == Crash \/ Open \/ ReplaceVoters \/ ChangeCustody \/ DeliverLateConfirmation \/ AckOnB \/ Repair \/ Certify \/ Renew
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Crash) /\ WF_vars(Open) /\ WF_vars(ReplaceVoters) /\ WF_vars(AckOnB)

ExactServing == running => local = Current
AcknowledgedInOriginalLoss == \A p \in At(Len(journal), "B-only-ack") :
  IntervalAt(p - 1) = [start |-> 0, loss |-> TRUE]
ExactRenewal == Len(usedCert) = 0 \/ (usedCert[1] = usedCert[2] /\ usedCert[3])
EventuallyAck == <>Has("B-only-ack")
NeverRenewAfterRepair == ~(Has("repair") /\ Current.start > 0)
===================================================================================
