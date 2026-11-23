-------------------------- MODULE DistributedPrepare -------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant
Pools == {1, 2}

VARIABLES phase, held, receipts, closed, everClosed, ordinary, down, crashed, late
vars == <<phase, held, receipts, closed, everClosed, ordinary, down, crashed, late>>

Init ==
    /\ phase = "initial" /\ held = {} /\ receipts = {}
    /\ closed = {} /\ everClosed = {}
    /\ ordinary = [pool \in Pools |-> 0]
    /\ down = FALSE /\ crashed = FALSE /\ late = FALSE

Used(pool) == ordinary[pool] + (IF pool = 1 THEN 1 ELSE 0) + (IF pool \in held THEN 1 ELSE 0)

Plan ==
    /\ phase = "initial" /\ ~down
    /\ phase' = "pending"
    /\ UNCHANGED <<held, receipts, closed, everClosed, ordinary, down, crashed, late>>

Prepare(pool) ==
    /\ phase \in {"pending", "aborted"} /\ pool \notin closed \cup held
    /\ Used(pool) < 2
    /\ held' = held \cup {pool} /\ receipts' = receipts \cup {pool}
    /\ late' = (late \/ phase = "aborted")
    /\ UNCHANGED <<phase, closed, everClosed, ordinary, down, crashed>>

Seal ==
    /\ phase = "pending" /\ ~down
    /\ receipts = Pools \/ (Variant = "partial_seal" /\ receipts # {})
    /\ phase' = "sealed"
    /\ UNCHANGED <<held, receipts, closed, everClosed, ordinary, down, crashed, late>>

Abort ==
    /\ phase = "pending" /\ ~down
    /\ phase' = "aborted"
    /\ UNCHANGED <<held, receipts, closed, everClosed, ordinary, down, crashed, late>>

Install ==
    /\ phase = "sealed" /\ ~down
    /\ phase' = "installed"
    /\ UNCHANGED <<held, receipts, closed, everClosed, ordinary, down, crashed, late>>

Fence(pool) ==
    /\ phase = "aborted" /\ pool \notin closed
    /\ closed' = closed \cup {pool} /\ everClosed' = everClosed \cup {pool}
    /\ UNCHANGED <<phase, held, receipts, ordinary, down, crashed, late>>

Return(pool) ==
    /\ pool \in held
    /\ pool \in closed \/ Variant = "expire_hold"
    /\ held' = held \ {pool}
    /\ UNCHANGED <<phase, receipts, closed, everClosed, ordinary, down, crashed, late>>

DisruptPool(pool) ==
    /\ Variant \in {"forget_hold", "forget_fence"}
    /\ held' = IF Variant = "forget_hold" THEN held \ {pool} ELSE held
    /\ closed' = IF Variant = "forget_fence" THEN closed \ {pool} ELSE closed
    /\ UNCHANGED <<phase, receipts, everClosed, ordinary, down, crashed, late>>

AdmitOrdinary(pool) ==
    /\ Used(pool) < 2 /\ ordinary[pool] < 1
    /\ ordinary' = [ordinary EXCEPT ![pool] = @ + 1]
    /\ UNCHANGED <<phase, held, receipts, closed, everClosed, down, crashed, late>>

CrashCoordinator ==
    /\ phase = "pending" /\ held # {} /\ held # Pools /\ ~crashed
    /\ down' = TRUE /\ crashed' = TRUE
    /\ UNCHANGED <<phase, held, receipts, closed, everClosed, ordinary, late>>

RecoverCoordinator ==
    /\ down
    /\ down' = FALSE
    /\ UNCHANGED <<phase, held, receipts, closed, everClosed, ordinary, crashed, late>>

Next ==
    \/ Plan \/ Seal \/ Abort \/ Install \/ CrashCoordinator \/ RecoverCoordinator
    \/ \E pool \in Pools : Prepare(pool) \/ Fence(pool) \/ Return(pool) \/ DisruptPool(pool) \/ AdmitOrdinary(pool)
Spec == Init /\ [][Next]_vars

Fair == Spec /\ WF_vars(RecoverCoordinator) /\ WF_vars(Seal \/ Abort)
             /\ WF_vars(Install)
             /\ \A pool \in Pools : WF_vars(Fence(pool)) /\ WF_vars(Return(pool))
FairWithoutCoordinatorRecovery ==
    Spec /\ WF_vars(Seal \/ Abort) /\ WF_vars(Install)
         /\ \A pool \in Pools : WF_vars(Fence(pool)) /\ WF_vars(Return(pool))

Decides == (phase = "pending") ~> (phase \in {"aborted", "sealed", "installed"})
Installs == (phase = "sealed") ~> (phase = "installed")
SettlesAbort == (phase = "aborted") ~> (closed = Pools /\ held = {})

Fits == \A pool \in Pools : Used(pool) <= 2
LiveReceiptsAreBacked == phase # "aborted" => receipts \subseteq held
FullCommittedVector == phase \in {"sealed", "installed"} => held = Pools
ClosedScopesStayClosed == everClosed \subseteq closed
NeverResumeAfterCoordinatorLoss == ~(crashed /\ phase = "installed")
NeverClearDelayedPrepareAfterAbort ==
    ~(phase = "aborted" /\ late /\ receipts = Pools /\ closed = Pools /\ held = {})
=============================================================================
