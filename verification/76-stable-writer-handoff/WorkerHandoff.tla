-------------------------- MODULE WorkerHandoff ------------------------------
EXTENDS Naturals

CONSTANT Variant, DirectoryUp, OldWorkerUp, AllocatorUp, Eligible
VARIABLES holder, head, cut, applied, served, staleCommit, reused
vars == <<holder, head, cut, applied, served, staleCommit, reused>>

Init ==
    /\ holder = "old" /\ head = 1 /\ cut = 0 /\ applied = 0
    /\ served = FALSE /\ staleCommit = FALSE /\ reused = FALSE

Choose ==
    /\ holder = "old"
    /\ Eligible \/ Variant = "skip_nomination"
    /\ IF Variant = "directory" THEN DirectoryUp ELSE TRUE
    /\ IF Variant = "recipient_needs_release" THEN OldWorkerUp ELSE TRUE
    /\ IF Variant = "migrate" THEN AllocatorUp ELSE TRUE
    /\ holder' = "new" /\ cut' = head
    /\ reused' = (Variant # "migrate")
    /\ UNCHANGED <<head, applied, served, staleCommit>>

OldAppend ==
    /\ head < 2 /\ ~staleCommit
    /\ holder = "old" \/ Variant = "old_epoch"
    /\ head' = head + 1 /\ staleCommit' = (holder = "new")
    /\ UNCHANGED <<holder, cut, applied, served, reused>>

CatchUp ==
    /\ holder = "new" /\ applied < cut
    /\ applied' = cut
    /\ UNCHANGED <<holder, head, cut, served, staleCommit, reused>>

Serve ==
    /\ holder = "new" /\ ~served
    /\ applied = cut \/ Variant = "serve_early"
    /\ head < 3
    /\ served' = TRUE /\ head' = head + 1
    /\ UNCHANGED <<holder, cut, applied, staleCommit, reused>>

Next == Choose \/ OldAppend \/ CatchUp \/ Serve \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
Fair == Spec /\ WF_vars(Choose) /\ WF_vars(CatchUp) /\ WF_vars(Serve)

OldEpochCannotCommit == ~staleCommit
CatchUpPrecedesServing == served => applied = cut
AuthorizedHolder == holder = "new" => Eligible
Serves == <> served
NeverServeAfterLastOldCommit == ~(served /\ cut = 2 /\ head = 3 /\ reused)
=============================================================================
