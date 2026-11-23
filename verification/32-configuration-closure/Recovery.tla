----------------------------- MODULE Recovery -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Binding, PriorChoice
VARIABLE s

Zones == 1..3
Cuts == 1..2
History == <<"a", "b">>
OldCopies == IF PriorChoice = 1 THEN <<2, 1, 1>> ELSE <<2, 2, 1>>
Available == Zones \ {s.lost}

Init ==
    s = [lost |-> 0, first |-> 0, candidates |-> {}, active |-> {},
         staged |-> [cut \in Cuts |-> {}], extended |-> {}]

Lose(zone) ==
    /\ s.lost = 0
    /\ s' = [s EXCEPT !.lost = zone]

Recover(reporters, cut) ==
    /\ s.active = {} /\ cut \notin s.candidates
    /\ Binding # "first_cut" \/ s.first = 0
    /\ reporters \subseteq Available /\ Cardinality(reporters) >= 2
    /\ \E source \in reporters : OldCopies[source] = cut
    /\ \A source \in reporters : OldCopies[source] <= cut
    /\ s' = [s EXCEPT !.first = IF @ = 0 THEN cut ELSE @, !.candidates = @ \cup {cut}]

Readable(cut) ==
    (\E source \in Available : OldCopies[source] >= cut) \/ s.staged[cut] \cap Available # {}

Stage(cut, zone) ==
    /\ cut \in s.candidates
    /\ s.active = {} \/ (Binding = "multiple_seeds" /\ cut \notin s.active)
    /\ zone \in Available \ s.staged[cut] /\ Readable(cut)
    /\ s' = [s EXCEPT !.staged[cut] = @ \cup {zone}]

Install(cut) ==
    /\ cut \in s.candidates \ s.active
    /\ s.active = {} \/ Binding = "multiple_seeds"
    /\ Cardinality(s.staged[cut] \cap Available) >= 2
    /\ s' = [s EXCEPT !.active = @ \cup {cut}]

Extend(cut) ==
    /\ cut \in s.active \ s.extended
    /\ s' = [s EXCEPT !.extended = @ \cup {cut}]

RecoverSome == \E reporters \in SUBSET Zones, cut \in Cuts : Recover(reporters, cut)
StageSome == \E cut \in Cuts, zone \in Zones : Stage(cut, zone)
InstallSome == \E cut \in Cuts : Install(cut)
Next == (\E zone \in Zones : Lose(zone)) \/ RecoverSome \/ StageSome \/ InstallSome \/
    (\E cut \in Cuts : Extend(cut))
Spec == Init /\ [][Next]_s
Fair == Spec /\ WF_s(RecoverSome) /\ WF_s(StageSome) /\ WF_s(InstallSome)

PreservesPriorChoice == \A cut \in s.candidates : PriorChoice <= cut
OneSeed == Cardinality(s.active) <= 1
ActiveHasSurvivingCopy == \A cut \in s.active : s.staged[cut] \cap Available # {}
Chosen(cut) == IF cut \in s.extended THEN Append(SubSeq(History, 1, cut), "c") ELSE SubSeq(History, 1, cut)
Prefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))
SeedsAndCommandsAgree ==
    \A a, b \in s.active : Prefix(Chosen(a), Chosen(b)) \/ Prefix(Chosen(b), Chosen(a))
EventuallyInstalls == <>(s.active # {})
NeverRecoversAfterLosingLargerSpeculation ==
    ~(s.first = 2 /\ s.lost = 1 /\ ~Readable(2) /\ s.active = {1})

=============================================================================
