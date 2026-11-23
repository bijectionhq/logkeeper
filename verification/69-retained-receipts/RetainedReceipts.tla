--------------------------- MODULE RetainedReceipts --------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant

Exact == <<7, 1, 0, 42>>
DifferentBytes == <<7, 1, 0, 43>>
DifferentGrant == <<7, 2, 0, 42>>
DifferentLineage == <<8, 1, 0, 42>>
Queries == {Exact, DifferentBytes, DifferentGrant, DifferentLineage}

VARIABLES end, phase, retained, physical, stable, pending, book, sent, unsafe, checked
vars == <<end, phase, retained, physical, stable, pending, book, sent, unsafe, checked>>

Init ==
    /\ end = 0 /\ phase = "old" /\ retained = 0 /\ physical = FALSE
    /\ stable = 0 /\ pending = FALSE /\ book = FALSE
    /\ sent = {} /\ unsafe = FALSE /\ checked = {}

Choose ==
    /\ end = 0 /\ phase = "old"
    /\ end' = 1 /\ physical' = TRUE
    /\ UNCHANGED <<phase, retained, stable, pending, book, sent, unsafe, checked>>

Seal ==
    /\ phase = "old" /\ end = 1 /\ phase' = "sealed"
    /\ UNCHANGED <<end, retained, physical, stable, pending, book, sent, unsafe, checked>>

Activate ==
    /\ phase = "sealed" /\ phase' = "next"
    /\ UNCHANGED <<end, retained, physical, stable, pending, book, sent, unsafe, checked>>

Stage ==
    /\ end = 1 /\ stable = 0 /\ ~pending
    /\ pending' = TRUE /\ book' = (Variant # "drop_identity" /\ retained = 0)
    /\ UNCHANGED <<end, phase, retained, physical, stable, sent, unsafe, checked>>

Sync ==
    /\ pending
    /\ stable' = 1 /\ pending' = FALSE
    /\ UNCHANGED <<end, phase, retained, physical, book, sent, unsafe, checked>>

ReclaimOldFrame ==
    /\ physical /\ stable = 1
    /\ physical' = FALSE
    /\ UNCHANGED <<end, phase, retained, stable, pending, book, sent, unsafe, checked>>

Trim ==
    /\ phase = "next" /\ stable = 1 /\ retained = 0
    /\ retained' = 1
    /\ UNCHANGED <<end, phase, physical, stable, pending, book, sent, unsafe, checked>>

Selectable(cut) == cut = stable \/ (pending /\ cut = 1)
HasReceipt(cut) == IF cut = 0 THEN physical ELSE book
AcceptsKey(key) ==
    key = Exact
    \/ (Variant = "ignore_lineage" /\ key[2] = Exact[2] /\ key[3] = Exact[3] /\ key[4] = Exact[4])
    \/ (Variant = "lsn_only" /\ key[3] = Exact[3])
    \/ (Variant = "payload_only" /\ key[3] = Exact[3] /\ key[4] = Exact[4])
Reconcile(cut, key) ==
    /\ phase = "next" /\ Selectable(cut)
    /\ LET returns == HasReceipt(cut) /\ AcceptsKey(key) /\
                    (retained = 0 \/ Variant = "serve_after_trim")
       IN /\ unsafe' = (unsafe \/ (returns /\ (key # Exact \/ retained # 0)))
          /\ sent' = IF returns THEN sent \cup {key} ELSE sent
          /\ end' = IF returns /\ Variant = "append_on_reconcile" THEN end + 1 ELSE end
          /\ checked' = checked \cup {<<cut, key, returns, physical>>}
    /\ end <= 1
    /\ UNCHANGED <<phase, retained, physical, stable, pending, book>>

Next ==
    \/ Choose \/ Seal \/ Activate \/ Stage \/ Sync \/ ReclaimOldFrame \/ Trim
    \/ \E cut \in {0, 1}, key \in Queries : Reconcile(cut, key)

Spec == Init /\ [][Next]_vars
ExactReturnedReceipt == ~unsafe
RetainedCoverage == retained = 0 /\ end > 0 => \A cut \in {0, 1} : Selectable(cut) => HasReceipt(cut)
ReconcileNeverAppends == end <= 1
NeverUseBothThenArchive ==
    ~( {<<0, Exact, TRUE, TRUE>>, <<1, Exact, TRUE, TRUE>>, <<1, Exact, TRUE, FALSE>>} \subseteq checked )
=============================================================================
