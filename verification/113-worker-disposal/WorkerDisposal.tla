------------------------------ MODULE WorkerDisposal ------------------------------
\* Disposal of a withdrawn worker's holds against its still-running readers.
\* "operator-evidence": dispose on an operator report, which may be wrong.
\* "lease-timed": the worker serves only within a journal-issued lease; dispose after it lapses.
\* "never": keep the holds until an explicit disposal that never arrives.
\* "unchecked-clock": like lease-timed, but the worker's clock may run slow without bound.
\* "async-fence": the worker stops serving through a separate fence action, not at each read.
EXTENDS Naturals
CONSTANTS Policy, Lease, Drift, MaxTime

VARIABLES now, withdrawnAt, workerAlive, serving, disposed, readerBroken, trimmed, workerClock

vars == <<now, withdrawnAt, workerAlive, serving, disposed, readerBroken, trimmed, workerClock>>

Init ==
  /\ now = 0
  /\ workerClock = 0
  /\ withdrawnAt = MaxTime + 1
  /\ workerAlive = TRUE
  /\ serving = TRUE
  /\ disposed = FALSE
  /\ readerBroken = FALSE
  /\ trimmed = FALSE

Withdrawn == withdrawnAt <= MaxTime
MaxSkew == IF Policy = "unchecked-clock" THEN MaxTime ELSE Drift

\* Real time advances; the worker's clock lags by at most the drift bound.
Tick ==
  /\ now < MaxTime
  /\ now' = now + 1
  /\ workerClock' \in {c \in workerClock..(now + 1) : (now + 1) - c <= MaxSkew}
  /\ UNCHANGED <<withdrawnAt, workerAlive, serving, disposed, readerBroken, trimmed>>

\* The administrator withdraws the worker, for example after a partition.
Withdraw ==
  /\ ~Withdrawn
  \* Leave the bounded horizon room for the lease and drift to elapse.
  /\ now + Lease + Drift <= MaxTime
  /\ withdrawnAt' = now
  /\ UNCHANGED <<now, workerAlive, serving, disposed, readerBroken, trimmed, workerClock>>

\* The worker may also really stop.
Stop ==
  /\ workerAlive
  /\ workerAlive' = FALSE
  /\ serving' = FALSE
  /\ UNCHANGED <<now, withdrawnAt, disposed, readerBroken, trimmed, workerClock>>

\* A partitioned worker stops serving once its own clock says the lease lapsed.
SelfFence ==
  /\ serving
  /\ Policy \in {"lease-timed", "unchecked-clock", "async-fence"}
  /\ Withdrawn
  /\ workerClock >= withdrawnAt + Lease
  /\ serving' = FALSE
  /\ UNCHANGED <<now, withdrawnAt, workerAlive, disposed, readerBroken, trimmed, workerClock>>

CanDispose ==
  CASE Policy = "operator-evidence" -> Withdrawn
    [] Policy = "never" -> FALSE
    [] OTHER -> Withdrawn /\ now >= withdrawnAt + Lease + Drift

Dispose ==
  /\ ~disposed
  /\ CanDispose
  /\ disposed' = TRUE
  /\ UNCHANGED <<now, withdrawnAt, workerAlive, serving, readerBroken, trimmed, workerClock>>

\* After disposal the custodian can retire the old checkpoint and trim.
Trim ==
  /\ disposed
  /\ ~trimmed
  /\ trimmed' = TRUE
  /\ UNCHANGED <<now, withdrawnAt, workerAlive, serving, disposed, readerBroken, workerClock>>

\* The last renewal before withdrawal grants a lease ending by withdrawnAt + Lease.
LeaseValid == ~Withdrawn \/ workerClock < withdrawnAt + Lease

\* A reader on a still-serving worker reads the old checkpoint.
Read ==
  /\ serving
  /\ Policy \in {"lease-timed", "unchecked-clock"} => LeaseValid
  /\ readerBroken' = (readerBroken \/ trimmed)
  /\ UNCHANGED <<now, withdrawnAt, workerAlive, serving, disposed, trimmed, workerClock>>

Next == Tick \/ Withdraw \/ Stop \/ SelfFence \/ Dispose \/ Trim \/ Read
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Tick) /\ WF_vars(Withdraw) /\ WF_vars(SelfFence) /\ WF_vars(Dispose) /\ WF_vars(Trim)

ReadersKeepTheirBytes == ~readerBroken
EventuallyTrims == Withdrawn ~> trimmed
TrimWitness == ~trimmed
=====================================================================================
