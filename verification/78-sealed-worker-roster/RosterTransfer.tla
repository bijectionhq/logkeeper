------------------------------- MODULE RosterTransfer -------------------------------
EXTENDS Naturals

CONSTANT Variant
VARIABLES phase, mounted, workers, oldGrant

OlderEmpty == [issued |-> 0, candidate |-> 0]
BeforeWithdrawal == [issued |-> 1, candidate |-> 1]
SealedBook == [issued |-> 1, candidate |-> 0]
Offers == {OlderEmpty, BeforeWithdrawal, SealedBook}
NoBook == [issued |-> 0, candidate |-> 2]

Init ==
    /\ phase = "live"
    /\ mounted = NoBook
    /\ workers = BeforeWithdrawal
    /\ oldGrant = FALSE

Withdraw ==
    /\ phase = "live"
    /\ phase' = "withdrawn"
    /\ workers' = SealedBook
    /\ UNCHANGED <<mounted, oldGrant>>

Seal ==
    /\ phase = "withdrawn"
    /\ phase' = "sealed"
    /\ UNCHANGED <<mounted, workers, oldGrant>>

Mount(book) ==
    /\ phase = "sealed"
    /\ CASE Variant = "cut-only" -> TRUE
          [] Variant = "omit-watermark" -> book.candidate = SealedBook.candidate
          [] OTHER -> book = SealedBook
    /\ phase' = "mounted"
    /\ mounted' = book
    /\ UNCHANGED <<workers, oldGrant>>

Activate ==
    /\ phase = "mounted"
    /\ Variant # "need-source"
    /\ phase' = "active"
    /\ workers' = IF Variant = "use-cache" THEN BeforeWithdrawal ELSE mounted
    /\ UNCHANGED <<mounted, oldGrant>>

Enroll ==
    /\ phase = "active"
    /\ workers.candidate = 0
    /\ workers' = [issued |-> workers.issued + 1, candidate |-> workers.issued + 1]
    /\ UNCHANGED <<phase, mounted, oldGrant>>

DelayedNomination ==
    /\ phase = "active"
    /\ workers.candidate = 1
    /\ oldGrant' = TRUE
    /\ UNCHANGED <<phase, mounted, workers>>

Vars == <<phase, mounted, workers, oldGrant>>
ExactMount == Mount(SealedBook)
Next == Withdraw \/ Seal \/ (\E book \in Offers : Mount(book)) \/ Activate \/ Enroll \/
        DelayedNomination \/ UNCHANGED Vars
Spec == Init /\ [][Next]_Vars
Fair == Spec /\ WF_Vars(Withdraw) /\ WF_Vars(Seal) /\ WF_Vars(ExactMount) /\ WF_Vars(Activate)

MountedExact == phase \in {"mounted", "active"} => mounted = SealedBook
ActiveBookMatchesOrExtends == phase = "active" =>
    workers = SealedBook \/ workers = [issued |-> 2, candidate |-> 2]
NoWithdrawnGrant == ~oldGrant
InstallsOffline == <>(phase = "active")
=====================================================================================
