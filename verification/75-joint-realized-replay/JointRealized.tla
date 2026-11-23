--------------------------- MODULE JointRealized -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Variant
Steps == 6
Views == 0..Steps

Origin == [plan |-> FALSE, seal |-> 0, window |-> 9, owed |-> FALSE, reply |-> 0]

Apply(state, position, receipt) ==
    CASE position = 1 -> [state EXCEPT !.plan = TRUE]
      [] position = 2 -> [state EXCEPT !.plan = FALSE, !.seal = receipt, !.owed = TRUE]
      [] position = 3 -> [state EXCEPT !.window = state.seal]
      [] position = 4 -> [state EXCEPT !.reply = 4]
      [] position = 5 -> [state EXCEPT !.owed = FALSE]
      [] position = 6 -> [state EXCEPT !.seal = 0]

RECURSIVE ChosenAt(_)
ChosenAt(position) ==
    IF position = 0 THEN Origin ELSE Apply(ChosenAt(position - 1), position, 1)

VARIABLES head, stable, visible, compactFloor, routed, rival, recovered
vars == <<head, stable, visible, compactFloor, routed, rival, recovered>>

Init ==
    /\ head = 0 /\ stable = 0 /\ visible = 0 /\ compactFloor = 0
    /\ routed = FALSE /\ rival = FALSE /\ recovered = {}

Advance ==
    /\ head < Steps
    /\ head' = head + 1 /\ recovered' = {}
    /\ UNCHANGED <<stable, visible, compactFloor, routed, rival>>

Capture ==
    /\ visible < head
    /\ visible' = head
    /\ UNCHANGED <<head, stable, compactFloor, routed, rival, recovered>>

Sync ==
    /\ stable < visible /\ stable' = visible
    /\ UNCHANGED <<head, visible, compactFloor, routed, rival, recovered>>

Reclaim ==
    /\ compactFloor < stable /\ compactFloor' = stable
    /\ UNCHANGED <<head, stable, visible, routed, rival, recovered>>

ReplaceRoute ==
    /\ head >= 2 /\ ~routed /\ routed' = TRUE
    /\ UNCHANGED <<head, stable, visible, compactFloor, rival, recovered>>

ReplacePhysical ==
    /\ head >= 2 /\ compactFloor < 2 /\ ~rival /\ rival' = TRUE
    /\ UNCHANGED <<head, stable, visible, compactFloor, routed, recovered>>

Body(cut) ==
    LET state == ChosenAt(cut) IN
      IF Variant = "drop_vector" /\ cut >= 2 THEN [state EXCEPT !.seal = 0]
      ELSE state

Physical(cut) ==
    /\ compactFloor <= cut
    /\ ~rival \/ cut >= 2 \/ Variant = "position_only"

RECURSIVE Resume(_, _, _)
Resume(state, at, end) ==
    IF at = end THEN state
    ELSE Resume(Apply(state, at + 1,
           IF (Variant = "position_only" /\ rival) \/ (Variant = "live_route" /\ routed)
           THEN 2 ELSE 1), at + 1, end)

Reopen(cut) ==
    /\ cut \in {stable, visible} /\ Physical(cut)
    /\ LET state == IF Variant = "base_only" THEN Body(cut) ELSE Resume(Body(cut), cut, head)
       IN recovered' = recovered \cup {<<cut, state>>}
    /\ UNCHANGED <<head, stable, visible, compactFloor, routed, rival>>

Next == Advance \/ Capture \/ Sync \/ Reclaim \/ ReplaceRoute \/ ReplacePhysical
    \/ (\E cut \in Views : Reopen(cut))

Spec == Init /\ [][Next]_vars

ExactRecoveredCut == \A item \in recovered : item[2] = ChosenAt(head)
NoMutableSealReplay == \A item \in recovered : item[2].seal = ChosenAt(head).seal
NeverReopenBothThroughRouteLoss ==
    ~(routed /\ head = Steps /\ \E left, right \in recovered : left[1] < right[1])
NeverReopenBothWithReclaimedPrefix ==
    ~(compactFloor >= 2 /\ head = Steps /\ \E left, right \in recovered : left[1] < right[1])
=============================================================================
