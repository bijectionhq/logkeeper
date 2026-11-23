----------------------------- MODULE MoveRecovery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant

VARIABLES chosen, authority, window, staged, selected,
          charged, closed, cursor, trueCursor, observed, eligible, activeBorrow, unsafeServe
vars == <<chosen, authority, window, staged, selected,
          charged, closed, cursor, trueCursor, observed, eligible, activeBorrow, unsafeServe>>

Init ==
    /\ chosen = FALSE /\ authority = "sealed" /\ window = 1
    /\ staged = FALSE /\ selected = 0
    /\ charged = {1, 2, 3} /\ closed = FALSE
    /\ cursor = 0 /\ trueCursor = 0 /\ observed = {}
    /\ eligible = TRUE /\ activeBorrow = TRUE /\ unsafeServe = FALSE

Choose ==
    /\ ~chosen /\ charged = {1, 2, 3} /\ eligible
    /\ chosen' = TRUE
    /\ UNCHANGED <<authority, window, staged, selected, charged, closed, cursor, trueCursor,
                    observed, eligible, activeBorrow, unsafeServe>>

Apply ==
    /\ chosen /\ authority = "sealed"
    /\ authority' = "destination"
    /\ window' = IF Variant = "bare_activation" THEN window ELSE 2
    /\ UNCHANGED <<chosen, staged, selected, charged, closed, cursor, trueCursor,
                    observed, eligible, activeBorrow, unsafeServe>>

Publish ==
    /\ authority = "destination" /\ window = 2
    /\ staged' = TRUE
    /\ UNCHANGED <<chosen, authority, window, selected, charged, closed, cursor, trueCursor,
                    observed, eligible, activeBorrow, unsafeServe>>

FinishSelector ==
    /\ staged
    /\ selected' = 1 /\ staged' = FALSE
    /\ UNCHANGED <<chosen, authority, window, charged, closed, cursor, trueCursor,
                    observed, eligible, activeBorrow, unsafeServe>>

SettleWorkspace ==
    /\ authority = "destination" /\ 3 \in charged
    /\ closed' = TRUE /\ charged' = charged \ {3}
    /\ UNCHANGED <<chosen, authority, window, staged, selected, cursor, trueCursor,
                    observed, eligible, activeBorrow, unsafeServe>>

AdvanceNeighbor ==
    /\ trueCursor < 2
    /\ trueCursor' = trueCursor + 1 /\ cursor' = cursor + 1
    /\ UNCHANGED <<chosen, authority, window, staged, selected, charged, closed,
                    observed, eligible, activeBorrow, unsafeServe>>

Reopen(cut) ==
    /\ cut = selected \/ (staged /\ cut = 1)
    /\ chosen
    /\ LET accepted == ~(Variant = "requote_history" /\ cut = 0 /\ 3 \notin charged)
       IN /\ authority' = IF accepted THEN "destination" ELSE "sealed"
          /\ window' = IF accepted THEN 2 ELSE 1
          /\ observed' = observed \cup {<<cut, accepted, closed, cursor > 0>>}
    /\ charged' = IF Variant = "restore_claims" /\ cut = 0 THEN charged \cup {3} ELSE charged
    /\ cursor' = IF Variant = "replace_neighbor" /\ cut = 0 THEN 0 ELSE cursor
    /\ UNCHANGED <<chosen, staged, selected, closed, trueCursor, eligible, activeBorrow, unsafeServe>>

LoseEligibility ==
    /\ eligible
    /\ eligible' = FALSE
    /\ UNCHANGED <<chosen, authority, window, staged, selected, charged, closed, cursor,
                    trueCursor, observed, activeBorrow, unsafeServe>>

Serve ==
    /\ authority = "destination" /\ window = 2
    /\ eligible \/ Variant = "admit_from_history"
    /\ unsafeServe' = (unsafeServe \/ ~eligible)
    /\ UNCHANGED <<chosen, authority, window, staged, selected, charged, closed, cursor,
                    trueCursor, observed, eligible, activeBorrow>>

FinishOldBorrow ==
    /\ activeBorrow /\ authority = "destination"
    /\ activeBorrow' = FALSE /\ charged' = charged \ {1}
    /\ UNCHANGED <<chosen, authority, window, staged, selected, closed, cursor,
                    trueCursor, observed, eligible, unsafeServe>>

Next ==
    \/ Choose \/ Apply \/ Publish \/ FinishSelector \/ SettleWorkspace
    \/ AdvanceNeighbor \/ LoseEligibility \/ Serve \/ FinishOldBorrow
    \/ \E cut \in {0, 1} : Reopen(cut)

Spec == Init /\ [][Next]_vars

ActiveAndWindowTogether == authority = "destination" => window = 2
HistoricalActivationStable == \A result \in observed : result[2]
OriginalSettlementStaysClosed == closed => 3 \notin charged
NeighborCursorSurvives == cursor = trueCursor
ServingUsesCurrentCustody == ~unsafeServe
OldBorrowPreserved == activeBorrow => 1 \in charged
NeverBothRecoverAfterSettlement == ~(closed /\ staged /\ activeBorrow /\ cursor > 0 /\
    {<<0, TRUE, TRUE, TRUE>>, <<1, TRUE, TRUE, TRUE>>} \subseteq observed)
=============================================================================
