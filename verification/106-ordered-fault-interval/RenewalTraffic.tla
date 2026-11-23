------------------------------- MODULE RenewalTraffic -------------------------------
CONSTANTS Policy, AddUncovered
VARIABLES certified, uncovered, renewed, background

vars == <<certified, uncovered, renewed, background>>
Init == /\ certified = FALSE
        /\ uncovered = FALSE
        /\ renewed = FALSE
        /\ background = FALSE

Certify ==
  /\ ~renewed
  /\ ~uncovered
  /\ ~certified
  /\ certified' = TRUE
  /\ UNCHANGED <<uncovered, renewed, background>>

CoveredCommit ==
  /\ ~(Policy = "reserve-ready-turn" /\ certified /\ ~renewed)
  /\ certified' = IF Policy = "exact-frontier" THEN FALSE ELSE certified
  /\ background' = ~background
  /\ UNCHANGED <<uncovered, renewed>>

UncoveredCommit ==
  /\ AddUncovered
  /\ ~renewed
  /\ ~uncovered
  /\ ~(Policy = "reserve-ready-turn" /\ certified)
  /\ uncovered' = TRUE
  /\ certified' = IF Policy = "carry-everything" THEN certified ELSE FALSE
  /\ UNCHANGED <<renewed, background>>

Renew ==
  /\ ~renewed
  /\ certified
  /\ renewed' = TRUE
  /\ UNCHANGED <<certified, uncovered, background>>

Next == Certify \/ CoveredCommit \/ UncoveredCommit \/ Renew
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Certify) /\ WF_vars(CoveredCommit) /\ WF_vars(Renew)
RenewalIsCovered == renewed => ~uncovered
EventuallyRenews == <>renewed
=====================================================================================
