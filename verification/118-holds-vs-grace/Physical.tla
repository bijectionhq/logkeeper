------------------------------ MODULE Physical ------------------------------
EXTENDS Integers

CONSTANTS Mode, Scenario, Fault, G, D, Bounded, E, Horizon, LeaseEnd
VARIABLES t, s
vars == <<t, s>>

\* Version 1 belongs to the retiring allocation. Version 2 is either a
\* replacement owned by a successor or a late conditional create.
RootKinds == {"fork", "selector", "preparation", "suffix"}
Exact == Mode = "A"
Pins == Mode \in {"A", "pin"}
Sample == -E .. E
ReadPending == s.borrow \in {"running", "detached"}
OldRoot == s.phase = "open" \/ s.ref
Drain == ~ReadPending
OldAbsent == 1 \notin s.versions
AfterDelete == s.phase \in {"deleted", "settled"}

Init ==
  /\ t = 0
  /\ s = [phase |-> "open", ref |-> Scenario \in RootKinds,
           admittedLateRef |-> FALSE, version2Root |-> FALSE,
           versions |-> {1}, hidden |-> FALSE, write |-> "idle",
           borrow |-> "idle", detached |-> FALSE, issued |-> 0,
           crashed |-> FALSE, disposed |-> FALSE, versionRead |-> "none",
           retired |-> 0, stampError |-> 0]

QueueWrite ==
  /\ Scenario = "write" /\ s.phase = "open" /\ s.write = "idle" /\ t = 0
  /\ s' = [s EXCEPT !.write = "queued"]
  /\ UNCHANGED t

StartBorrow ==
  /\ Scenario \in {"borrow", "worker"} /\ s.phase = "open"
  /\ s.borrow = "idle" /\ t = 0
  /\ s' = [s EXCEPT !.borrow = "running", !.issued = t]
  /\ UNCHANGED t

StartLeasedBorrow ==
  /\ Scenario = "worker-race" /\ s.phase # "open" /\ s.borrow = "idle"
  /\ \E err \in Sample : t + err < LeaseEnd
  /\ s' = [s EXCEPT !.borrow = "running", !.issued = t]
  /\ UNCHANGED t

Detach ==
  /\ s.borrow = "running"
  /\ s' = [s EXCEPT !.borrow = "detached", !.detached = TRUE]
  /\ UNCHANGED t

Crash ==
  /\ Scenario = "worker" /\ s.detached /\ ~s.crashed
  /\ s' = [s EXCEPT !.crashed = TRUE]
  /\ UNCHANGED t

Retire ==
  /\ s.phase = "open"
  /\ IF Scenario = "write" THEN s.write = "queued" ELSE TRUE
  /\ IF Scenario \in {"borrow", "worker"} THEN s.detached ELSE TRUE
  /\ IF Scenario = "worker" THEN s.crashed ELSE TRUE
  /\ \E err \in Sample :
       s' = [s EXCEPT !.phase = "retired", !.retired = t, !.stampError = err]
  /\ UNCHANGED t

ReleaseRoot ==
  /\ s.phase = "retired" /\ s.ref
  /\ \E err \in Sample :
       s' = [s EXCEPT !.ref = FALSE, !.retired = t, !.stampError = err]
  /\ UNCHANGED t

Register ==
  /\ Scenario = "register" /\ ~s.admittedLateRef /\ ~OldAbsent
  /\ s.phase = "retired" \/ (Fault = "stale-mark" /\ s.phase = "withdrawing")
  /\ s' = [s EXCEPT !.ref = TRUE, !.admittedLateRef = TRUE]
  /\ UNCHANGED t

InstallReplacement ==
  /\ Scenario = "replace" /\ ~s.version2Root /\ ~AfterDelete
  /\ s' = [s EXCEPT !.versions = @ \cup {2}, !.version2Root = TRUE]
  /\ UNCHANGED t

VersionRead ==
  /\ Scenario = "replace" /\ s.version2Root /\ s.versionRead = "none"
  /\ ~OldAbsent /\ s.phase = "open"
  /\ s' = [s EXCEPT !.versionRead = CASE Fault = "trust-latest" -> "wrong"
                                     [] Fault = "hash-only" -> "refused"
                                     [] OTHER -> "exact"]
  /\ UNCHANGED t

Dispose ==
  /\ Scenario \in {"worker", "worker-race"} /\ Exact /\ ~s.disposed
  /\ s.crashed \/ Scenario = "worker-race"
  /\ s.phase = "retired" /\ Fault # "no-dispose"
  /\ t >= (IF Fault = "early-dispose" THEN LeaseEnd ELSE LeaseEnd + E)
  /\ s' = [s EXCEPT !.disposed = TRUE]
  /\ UNCHANGED t

Withdraw ==
  /\ s.phase = "retired" /\ (~s.ref \/ Fault = "ignore-root")
  /\ IF Exact
       THEN /\ (Scenario \notin {"worker", "worker-race"} \/ s.disposed)
            /\ (Drain \/ Fault = "drop-borrow")
       ELSE /\ \E err \in Sample : t + err >= s.retired + s.stampError + G
            /\ (~Pins \/ Drain)
  /\ s' = [s EXCEPT !.phase = "withdrawing",
                    !.write = IF Exact /\ Fault # "no-fence" /\ @ = "queued"
                              THEN "stopped" ELSE @]
  /\ UNCHANGED t

CompleteWrite ==
  /\ s.phase # "open" /\ s.write = "queued"
  /\ ~Bounded \/ t <= D
  /\ s' = [s EXCEPT !.write = "finished",
                    !.versions = IF @ = {} THEN {2} ELSE @]
  /\ UNCHANGED t

FinishBorrow ==
  /\ s.phase # "open" /\ ReadPending
  /\ ~Bounded \/ t - s.issued <= D
  /\ s' = [s EXCEPT !.borrow = "finished"]
  /\ UNCHANGED t

Delete ==
  /\ s.phase = "withdrawing"
  /\ s' = [s EXCEPT !.phase = "deleted",
                    !.hidden = Fault = "marker",
                    !.versions = CASE Fault = "marker" -> @
                                   [] Fault = "delete-latest" /\ 2 \in @ -> @ \ {2}
                                   [] OTHER -> @ \ {1}]
  /\ UNCHANGED t

Settle ==
  /\ s.phase = "deleted"
  /\ OldAbsent \/ (Fault = "marker" /\ s.hidden)
  /\ IF Exact THEN Drain /\ s.write # "queued" ELSE TRUE
  /\ s' = [s EXCEPT !.phase = "settled"]
  /\ UNCHANGED t

Tick ==
  /\ s.phase # "open" /\ t < Horizon
  /\ IF ~Bounded THEN TRUE
       ELSE /\ (s.write # "queued" \/ t < D)
            /\ (~ReadPending \/ t - s.issued < D)
  /\ t' = t + 1
  /\ UNCHANGED s

Next ==
  QueueWrite \/ StartBorrow \/ StartLeasedBorrow \/ Detach \/ Crash \/ Retire \/ ReleaseRoot
  \/ Register \/ InstallReplacement \/ VersionRead \/ Dispose \/ Withdraw \/ CompleteWrite
  \/ FinishBorrow \/ Delete \/ Settle \/ Tick
Spec == Init /\ [][Next]_vars

LiveRootsBacked == (OldRoot => ~OldAbsent) /\ (s.version2Root => 2 \in s.versions)
BorrowBacked == ReadPending => ~OldAbsent
StableAbsence == (AfterDelete /\ Scenario = "write") => s.versions = {}
NoWrongVersion == s.versionRead # "wrong"
ExactSettlement == s.phase = "settled" => OldAbsent /\ Drain /\ s.write # "queued"
DisposalAfterAdmission ==
  s.disposed => \A err \in Sample : t + err >= LeaseEnd

\* Witness predicates are intentionally false on a successful target trace.
SawWriteClosure == ~(s.phase = "settled" /\ s.write # "idle")
SawDetachedDrain == ~(s.phase = "settled" /\ s.detached /\ s.borrow = "finished")
SawWorkerReclaimed == ~(s.phase = "settled" /\ s.crashed /\ (Exact => s.disposed))
SawLeasedBorrow == ~(s.phase = "settled" /\ s.issued >= LeaseEnd /\ s.borrow = "finished")
SawReplacementSurvive == ~(s.phase = "settled" /\ s.versionRead = "exact" /\ s.versions = {2})
SawVerifiedRefusal == ~(s.versionRead = "refused" /\ s.versions = {1, 2})
SawRootRelease == ~(s.phase = "settled" /\ OldAbsent)
SawRegistrationWin == ~(s.admittedLateRef /\ OldRoot /\ ~OldAbsent)

WorkerFair == Spec /\ WF_vars(StartBorrow) /\ WF_vars(Detach) /\ WF_vars(Crash)
                   /\ WF_vars(Retire) /\ WF_vars(FinishBorrow) /\ WF_vars(Tick)
                   /\ WF_vars(Dispose) /\ WF_vars(Withdraw) /\ WF_vars(Delete)
                   /\ WF_vars(Settle)
WorkerReclaimed == <>(s.phase = "settled")
=============================================================================
