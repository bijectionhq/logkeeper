------------------------- MODULE ReadIdentityChoices --------------------------
EXTENDS Naturals

CONSTANT Width, Mode, Scenario

VARIABLES floor, sparse, admitted, abandoned, live, earlyArrived, restarted, doubleAdmission

vars == <<floor, sparse, admitted, abandoned, live, earlyArrived, restarted, doubleAdmission>>
Nonces == 1..3
Spent == (1..floor) \cup sparse
Consumed == admitted \cup abandoned

Init ==
  /\ floor = 0
  /\ sparse = {}
  /\ admitted = {}
  /\ abandoned = {}
  /\ live = {}
  /\ earlyArrived = FALSE
  /\ restarted = FALSE
  /\ doubleAdmission = FALSE

Compact(consumed) ==
  CHOOSE through \in 0..3 :
    /\ (1..through) \subseteq consumed
    /\ (through = 3 \/ through + 1 \notin consumed)

Save(nonce) ==
  LET now == Spent \cup {nonce}
      high == IF Mode = "maximum" THEN nonce ELSE Compact(now)
  IN /\ floor' = high
     /\ sparse' = now \ (1..high)

Eligible(nonce) == nonce \notin Spent /\ nonce <= floor + Width

Arrived(nonce) ==
  CASE nonce = 1 -> earlyArrived
    [] nonce = 2 -> TRUE
    [] OTHER -> Scenario = "window-edge"

Admit(nonce) ==
  /\ Arrived(nonce)
  /\ Eligible(nonce)
  /\ Save(nonce)
  /\ admitted' = admitted \cup {nonce}
  /\ live' = live \cup {nonce}
  /\ doubleAdmission' = (doubleAdmission \/ nonce \in admitted)
  /\ UNCHANGED <<abandoned, earlyArrived, restarted>>

ArriveEarly ==
  /\ Scenario = "delayed"
  /\ ~earlyArrived
  /\ earlyArrived' = TRUE
  /\ UNCHANGED <<floor, sparse, admitted, abandoned, live, restarted, doubleAdmission>>

AbandonEarly ==
  /\ Scenario = "abandon"
  /\ Eligible(1)
  /\ Save(1)
  /\ abandoned' = abandoned \cup {1}
  /\ UNCHANGED <<admitted, live, earlyArrived, restarted, doubleAdmission>>

Close(nonce) ==
  /\ nonce \in live
  /\ live' = live \ {nonce}
  /\ UNCHANGED <<floor, sparse, admitted, abandoned, earlyArrived, restarted, doubleAdmission>>

Restart ==
  /\ ~restarted
  /\ admitted # {}
  /\ restarted' = TRUE
  /\ sparse' = IF Mode = "lose-sparse" THEN {} ELSE sparse
  /\ UNCHANGED <<floor, admitted, abandoned, live, earlyArrived, doubleAdmission>>

ExactConsumption == Spent = Consumed
FitsWindow == sparse \subseteq ((floor + 1)..(floor + Width))
NoRepeat == ~doubleAdmission
RefusesBeyondGap == Scenario = "window-edge" => 3 \notin admitted
LaterCompletes == <> (2 \in admitted)
BothComplete == <> ({1, 2} \subseteq admitted)
AbandonThenProceed == <> (1 \in abandoned /\ 2 \in admitted)

Next == (\E nonce \in Nonces : Admit(nonce) \/ Close(nonce)) \/ ArriveEarly \/ AbandonEarly \/ Restart
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Next)

=============================================================================
