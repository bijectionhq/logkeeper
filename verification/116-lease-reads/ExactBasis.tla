------------------------------ MODULE ExactBasis ------------------------------
EXTENDS Naturals

CONSTANT Mode
VARIABLES phase, published, floor, trimmed, objects

vars == <<phase, published, floor, trimmed, objects>>
Root == 0
Suffix == 1
Cut == 2
Dependencies == {Root, Suffix}

Init ==
    /\ phase = "idle"
    /\ published = FALSE
    /\ floor = Root
    /\ trimmed = Root
    /\ objects = Dependencies

\* Cut 2 initially depends on the root at 0 and replay input at 1.
\* Publication gives future operations a new root but changes no old borrow.
Admit ==
    /\ phase = "idle" /\ ~published
    /\ phase' = "held"
    /\ UNCHANGED <<published, floor, trimmed, objects>>

Publish ==
    /\ ~published
    /\ published' = TRUE
    /\ UNCHANGED <<phase, floor, trimmed, objects>>

Report ==
    /\ published
    /\ floor' = IF phase = "held" /\ Mode = "basis" THEN Root ELSE Cut
    /\ UNCHANGED <<phase, published, trimmed, objects>>

Trim(through) ==
    /\ through \in (trimmed + 1)..floor
    /\ trimmed' = through
    /\ UNCHANGED <<phase, published, floor, objects>>

Collect(object) ==
    /\ object \in objects /\ object < trimmed
    /\ objects' = objects \ {object}
    /\ UNCHANGED <<phase, published, floor, trimmed>>

Finish ==
    /\ phase = "held"
    /\ trimmed <= Suffix /\ Dependencies \subseteq objects
    /\ phase' = "finished"
    /\ UNCHANGED <<published, floor, trimmed, objects>>

Next ==
    \/ Admit \/ Publish \/ Report \/ Finish
    \/ \E through \in 1..Cut : Trim(through)
    \/ \E object \in Dependencies : Collect(object)

Spec == Init /\ [][Next]_vars

ReplayRetained == phase = "held" => trimmed <= Suffix
ObjectsRetained == phase = "held" => Dependencies \subseteq objects
FinishAndCollectWitness == ~(phase = "finished" /\ objects = {})
=============================================================================
