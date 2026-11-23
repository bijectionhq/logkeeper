----------------------------- MODULE InstallBinding -----------------------------
EXTENDS Naturals

CONSTANT Variant
VARIABLE s

Expected == [move |-> 2, cut |-> 2, target |-> 1]
Evidence == {Expected, [move |-> 1, cut |-> 2, target |-> 1],
                       [move |-> 2, cut |-> 1, target |-> 1]}

Init == s = [received |-> {}, accepted |-> {}]

Receive(evidence) ==
    /\ evidence \notin s.received
    /\ s' = [s EXCEPT !.received = @ \cup {evidence}]

Accept(evidence) ==
    /\ evidence \in s.received /\ evidence \notin s.accepted
    /\ evidence.target = Expected.target
    /\ evidence.move = Expected.move \/ Variant = "target_only"
    /\ evidence.cut = Expected.cut \/ Variant = "move_without_cut"
    /\ s' = [s EXCEPT !.accepted = @ \cup {evidence}]

Next == \E evidence \in Evidence : Receive(evidence) \/ Accept(evidence)
Spec == Init /\ [][Next]_s
ExactInstall == s.accepted \subseteq {Expected}
=============================================================================
