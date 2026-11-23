------------------------------ MODULE ChosenReplay ---------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Variant, MaxCut

Canonical == <<11, 12, 13>>
Position(frame) == CASE frame \in {11, 41, 51} -> 1 [] frame = 12 -> 2 [] frame = 13 -> 3 [] OTHER -> 4
Frames == {11, 12, 13, 14, 41, 51}

InitialImage == <<1, 0, <<>>>>
Apply(image, frame) ==
    IF frame = 12
    THEN IF image[1] < 2 THEN <<2, 0, image[3]>> ELSE image
    ELSE
        LET window == IF frame \in {11, 41, 51} THEN 1 ELSE 2
            offset == IF frame = 14 THEN 1 ELSE 0
        IN IF image[1] = window /\ image[2] = offset THEN
            <<window, offset + 1, Append(image[3], frame)>>
        ELSE image
Decision(image, frame) ==
    IF frame = 12 THEN IF image[1] < 2 THEN <<frame, "install">> ELSE <<frame, "refuse">>
    ELSE IF Apply(image, frame) = image THEN <<frame, "refuse">> ELSE <<frame, "append">>
RECURSIVE Walk(_, _)
Walk(image, frames) ==
    IF Len(frames) = 0 THEN <<image, <<>>>>
    ELSE LET rest == Walk(Apply(image, Head(frames)), Tail(frames))
         IN <<rest[1], <<Decision(image, Head(frames))>> \o rest[2]>>
Bootstrap(cut) == Walk(InitialImage, SubSeq(Canonical, 1, cut))[1]
TailAt(cut) == SubSeq(Canonical, cut + 1, MaxCut)

VARIABLES material, selected, candidate, recovered, observed
vars == <<material, selected, candidate, recovered, observed>>

Init ==
    /\ material = {11, 12, 13} /\ selected = 0 /\ candidate = FALSE
    /\ recovered = {} /\ observed = {}

Stage(frame) ==
    /\ frame \in {14, 41, 51}
    /\ material' = material \cup {frame}
    /\ UNCHANGED <<selected, candidate, recovered, observed>>

Publish ==
    /\ MaxCut >= 2
    /\ candidate' = TRUE
    /\ UNCHANGED <<material, selected, recovered, observed>>

ResolveSelector ==
    /\ candidate
    /\ selected' = 2 /\ candidate' = FALSE
    /\ UNCHANGED <<material, recovered, observed>>

CanSelect(cut) == cut = selected \/ (candidate /\ cut = 2)
ReplayInput(cut, substitution) ==
    LET official == TailAt(cut)
        tail == IF substitution = 0 THEN official ELSE <<substitution>> \o Tail(official)
    IN IF Variant = "overrun_cut" /\ 14 \in material /\ MaxCut = 3 THEN Append(tail, 14) ELSE tail

Recover(cut, substitution) ==
    /\ CanSelect(cut)
    /\ substitution = 0 \/
        (cut = 0 /\ substitution \in material /\ Position(substitution) = 1 /\
          ((Variant = "position_only" /\ substitution = 41) \/ (Variant = "foreign_lineage" /\ substitution = 51)))
    /\ LET base == IF Variant = "latest_window" /\ candidate /\ cut = 0
                     THEN <<Bootstrap(2)[1], Bootstrap(2)[2], Bootstrap(cut)[3]>>
                     ELSE Bootstrap(cut)
           input == ReplayInput(cut, substitution)
           result == Walk(base, input)
       IN /\ \A i \in 1..Len(input) : input[i] \in material
          /\ recovered' = recovered \cup {<<cut, result>>}
          /\ observed' = observed \cup {cut}
    /\ UNCHANGED <<material, selected, candidate>>

Next ==
    \/ Publish \/ ResolveSelector
    \/ \E frame \in Frames : Stage(frame)
    \/ \E cut \in {0, 2}, substitute \in {0, 41, 51} : Recover(cut, substitute)
Spec == Init /\ [][Next]_vars
ExactRecovery == \A item \in recovered : item[2] = Walk(Bootstrap(item[1]), TailAt(item[1]))
NeverRecoverBothWithRivals == ~({0, 2} \subseteq observed /\ {14, 41, 51} \subseteq material)
=============================================================================
