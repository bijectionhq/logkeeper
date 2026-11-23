------------------------ MODULE RealizedCheckpoint --------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant
Recovery == {1, 2}
Exact == <<1, 2, 3>>
Swapped == <<1, 4, 3>>
Bases == {"old", "live", "settled", "truncated", "swapped", "lost_window"}

VARIABLES stable, visible, frame, owned, absent, poolAck, installed, row, window
vars == <<stable, visible, frame, owned, absent, poolAck, installed, row, window>>

Init ==
    /\ stable = "old" /\ visible = "old" /\ frame = TRUE
    /\ owned = {} /\ absent = {} /\ poolAck = FALSE
    /\ installed = FALSE /\ row = TRUE /\ window = FALSE

Install ==
    /\ ~installed
    /\ installed' = TRUE /\ window' = TRUE
    /\ UNCHANGED <<stable, visible, frame, owned, absent, poolAck, row>>

ConfirmAbsence(scope) ==
    /\ installed /\ scope \notin owned \cup absent
    /\ absent' = absent \cup {scope}
    /\ UNCHANGED <<stable, visible, frame, owned, poolAck, installed, row, window>>

OwnCustody(scope) ==
    /\ installed /\ scope \notin owned \cup absent
    /\ owned' = owned \cup {scope}
    /\ UNCHANGED <<stable, visible, frame, absent, poolAck, installed, row, window>>

Acknowledge ==
    /\ installed /\ ~poolAck
    /\ Recovery \subseteq owned \cup absent \/ (Variant = "one_scope" /\ owned \cup absent # {})
    /\ poolAck' = TRUE
    /\ UNCHANGED <<stable, visible, frame, owned, absent, installed, row, window>>

Compact ==
    /\ row /\ installed /\ poolAck
    /\ row' = FALSE
    /\ window' = IF Variant = "drop_serving_window" THEN FALSE ELSE window
    /\ UNCHANGED <<stable, visible, frame, owned, absent, poolAck, installed>>

Capture ==
    /\ installed
    /\ LET next == IF row THEN
            IF Variant = "truncate_body" THEN "truncated"
            ELSE IF Variant = "swap_extent" THEN "swapped" ELSE "live"
          ELSE IF window THEN "settled" ELSE "lost_window"
       IN visible # next /\ visible' = next
    /\ UNCHANGED <<stable, frame, owned, absent, poolAck, installed, row, window>>

Sync ==
    /\ stable # visible
    /\ stable' = visible
    /\ UNCHANGED <<visible, frame, owned, absent, poolAck, installed, row, window>>

Selectable == {stable, visible}
Resolve(base) ==
    CASE base = "old" -> IF frame THEN Exact ELSE <<>>
      [] base = "live" -> Exact
      [] base = "swapped" -> Swapped
      [] OTHER -> <<>>
HasWindow(base) == base \in {"live", "settled"} \/ (base = "old" /\ frame)

Reclaim ==
    /\ frame /\ visible # "old"
    /\ stable # "old" \/ Variant = "visible_only"
    /\ frame' = FALSE
    /\ UNCHANGED <<stable, visible, owned, absent, poolAck, installed, row, window>>

Next ==
    Install \/ Acknowledge \/ Compact \/ Capture \/ Sync \/ Reclaim \/
    (\E scope \in Recovery : ConfirmAbsence(scope) \/ OwnCustody(scope))
Spec == Init /\ [][Next]_vars

PoolAckCoversAll == poolAck => Recovery \subseteq absent \cup owned
FrameHasNoSelectableUse == ~frame => "old" \notin Selectable
ExactOwedVector == row => \A base \in Selectable : Resolve(base) = Exact
ServingWindowKeepsItsBinding == installed => window /\ \A base \in Selectable : HasWindow(base)
NeverRecoverUnsettledWithoutFrame ==
    ~(row /\ ~poolAck /\ ~frame /\ 1 \in absent /\ 2 \notin absent \cup owned /\ stable = "live")
NeverForgetDecisionWithIndependentCustody ==
    ~(~row /\ 1 \in absent /\ 2 \in owned /\ stable = "settled" /\ ~frame)
=============================================================================
