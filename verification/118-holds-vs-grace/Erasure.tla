------------------------------ MODULE Erasure -------------------------------
EXTENDS Integers
CONSTANTS Fault, E, Deadline, Arm, Horizon
VARIABLES t, s
vars == <<t, s>>
Sample == -E .. E

\* One old dependent view, one detached open, one unresolved key-copy request,
\* two crash-selectable slots, one old/new generation. Ciphertext is retained.
Init ==
  /\ t = 0
  /\ s = [slots |-> 0, committed |-> FALSE, stampError |-> 0,
           oldKey |-> TRUE, oldHold |-> TRUE, ciphertext |-> TRUE,
           job |-> "pending", openedAt |-> -1, oldAppend |-> FALSE,
           copy |-> "queued", escaped |-> FALSE, recovered |-> FALSE]

StageSlot ==
  /\ ~s.committed /\ s.slots < 2
  /\ s' = [s EXCEPT !.slots = @ + 1]
  /\ UNCHANGED t

Commit ==
  /\ ~s.committed
  /\ s.slots = 2 \/ (Fault = "old-selector" /\ s.slots = 1)
  /\ \E err \in Sample :
       s' = [s EXCEPT !.committed = TRUE, !.stampError = err,
          !.oldKey = Fault # "early-revoke",
          !.oldHold = Fault # "drop-hold",
          !.copy = IF Fault = "escape-copy" THEN @ ELSE "fenced"]
  /\ UNCHANGED t

DelayedAppend ==
  /\ s.committed /\ Fault = "old-append" /\ ~s.oldAppend
  /\ s' = [s EXCEPT !.oldAppend = TRUE]
  /\ UNCHANGED t

CompleteCopy ==
  /\ s.committed /\ s.copy = "queued"
  /\ s' = [s EXCEPT !.copy = "finished", !.escaped = TRUE]
  /\ UNCHANGED t

Tick ==
  /\ s.committed /\ t < Horizon
  /\ t' = t + 1
  /\ \E err \in Sample :
       s' = [s EXCEPT !.oldKey = @ /\
                   (Fault = "grace-only" \/ t' + err < s.stampError + Arm)]

CompleteOpen ==
  /\ s.committed /\ s.job = "pending"
  /\ s' = [s EXCEPT !.openedAt = t,
            !.job = IF s.oldKey \/ Fault = "admit-only" THEN "plain" ELSE "erased"]
  /\ UNCHANGED t

Recover ==
  /\ s.committed /\ ~s.recovered /\ s.slots = 2 /\ ~s.oldAppend
  /\ t >= Deadline
  /\ s' = [s EXCEPT !.recovered = TRUE]
  /\ UNCHANGED t

Next == StageSlot \/ Commit \/ DelayedAppend \/ CompleteCopy \/ Tick \/ CompleteOpen \/ Recover
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(StageSlot) /\ WF_vars(Commit) /\ WF_vars(Tick)
             /\ WF_vars(CompleteOpen) /\ WF_vars(Recover)

CleanRecovery == s.committed => s.slots = 2 /\ ~s.oldAppend
DeadlineUnreadable == (s.committed /\ t >= Deadline) => ~s.oldKey /\ ~s.escaped
NoLatePlaintext == s.job = "plain" => s.openedAt < Deadline
NoEarlyEraseAtCommit == (s.committed /\ t = 0) => s.oldKey
FullViewWindow == (s.committed /\ t < Deadline) => s.oldKey
GuaranteedWindow == (s.committed /\ t < Arm - 2 * E) => s.oldKey
HoldSurvives == s.oldHold /\ s.ciphertext
KeyDomainClosed == s.committed => ~s.escaped
EventuallyRecovers == <>s.recovered

SawRevocationAndRecovery == ~(s.recovered /\ ~s.oldKey /\ s.oldHold /\ s.ciphertext
                               /\ s.job = "erased")
SawPredeadlineRead == ~(s.job = "plain" /\ s.openedAt < Deadline /\ s.committed)
=============================================================================
